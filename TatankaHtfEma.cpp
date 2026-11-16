// Copyright (c) 2026 Tatanka Trading LLC.
// This Source Code Form is subject to the Mozilla Public License, v. 2.0.
// If a copy of the MPL was not distributed with this file, obtain one at https://mozilla.org/MPL/2.0/.
// Tatanka 1hr 21 EMA (HTF EMA) v1.0.1 for Sierra Chart - tatankatrading.com

#include "sierrachart.h"

SCDLLName("Tatanka HTF EMA")

// NinjaTrader's TatankaHtfEma.cs v1.0.1. NinjaTrader adds the source timeframe as a second data series and
// runs its bars and the chart's bars in time order. It stamps every bar with its close, and it runs a chart
// bar before a source bar with the same stamp. So on each chart bar:
// - Exact is the EMA through the last source bar stamped before the chart bar. It steps once per source bar,
//   at the first chart bar after that bar closes: on a 5-minute chart the 10:00-10:05 bar is the first to
//   show the hour that closed at 10:00.
// - Live is one EMA step from that EMA at the chart bar's close.
// - On the bar still forming, a source bar counts only once it has closed: a trade came at or after its close
//   (also when that trade is a forming tick, volume or range bar's last trade, its stamp so far). So Exact holds
//   still while a source bar forms, and a reload shows what the bar showed live.
// - Smooth Scaled is an EMA of the chart's closes, its length scaled by source / chart timeframe.
// - A chart bar stamped before the first source bar shows nothing. Exact and Live also wait until a source
//   bar has closed after the chart's first bar: NinjaTrader skips the source bars it runs before the chart has
//   a bar (CurrentBars[0] < 0).
// The source bars come from the chart itself where its bars make them exactly. A second or minute source: time
// bars shorter than it that divide it; on other charts (bars that don't divide it, bars as long as it or longer,
// tick, volume and range bars, daily charts) a hidden intraday chart of the same symbol at the source timeframe,
// with this chart's Session Times, time zone and Days to Load (as the Periodic Volume Profile opens its 1-minute
// chart). A day, week, month or year source: intraday bars shorter than a day and 1-day charts; on other charts
// (intraday bars of a day or longer, daily charts of several days, weekly, monthly) the daily chart that TPO
// Profile and If/Then open. As NinjaTrader loads its second series over the chart's own days, only source bars
// from this chart's first trading day on are used. A hidden chart is read only while it holds this chart's symbol
// and those settings: NinjaTrader's second series is always the chart's own instrument.
//
// Columns Sierra Chart adds with Include Columns With No Data hold no trades, and NinjaTrader has no such bars:
// they make no source bar and no EMA step, and the line holds the previous bar's value there. Sierra Chart has no
// setting for a study to read, so a column is empty when it has no volume and no trades and does not move (the
// Periodic Volume Profile's rule). On a symbol whose data has no volume (a cash index, some forex feeds) a real bar
// that does not move is skipped the same way, where NinjaTrader counts it.
//
// Second and minute source bars start at the trading day's start from the Session Times (the Evening Start Time
// with the evening session), as NinjaTrader's start at its Trading Hours session's open. So the trading day must
// start at the market's open after its daily break (17:00 Chicago for CME); otherwise 60-minute source bars sit at
// another minute of the hour, and day sources split elsewhere.
//
// Tick, volume and range bars are stamped with their last trade, which needs Sierra Chart's bar end times. A chart
// opened before the study was added may not have them: the study asks for a reload in the Message Log and until
// then takes the next bar's start, so a bar can step one bar early where a source bar closed between two bars.
//
// Deliberate differences (also in README.md):
// - The forming bar is recalculated on every trade (Sierra Chart has no Calculate setting; NinjaTrader's default
//   is On price change), and a bar that has closed is recalculated once more. So where NinjaTrader's live bar kept
//   a value its reload shows otherwise (the bar's last trade came before a source bar closed, and the next trade
//   came after the bar ended), this shows the reload's. With On bar close, NinjaTrader's closed bars match these.
// - Sources: seconds, minutes, days, weeks, months and years (NinjaTrader also offers tick, volume, range and other
//   bar types, which have no length in seconds). A Quarterly chart counts as 3 x 30 days for Smooth Scaled
//   (NinjaTrader has no quarterly bars).
// - While the hidden chart loads, Live and Exact show nothing.
// - A bar with no volume and no trades that does not move counts as an empty column (above), also on a symbol
//   whose data has no volume, where NinjaTrader counts it.
// - Smooth Scaled on a daily chart of several days, weekly or monthly (no hidden chart) takes the weekdays as the
//   trading days, so a holiday where its first source bar ends can move its first value by a bar.

namespace
{
	enum HtfUnit
	{
		UNIT_SECONDS,
		UNIT_MINUTES,
		UNIT_DAYS,
		UNIT_WEEKS,
		UNIT_MONTHS,
		UNIT_YEARS
	};

	enum HtfEmaMode
	{
		MODE_LIVE_HTF,
		MODE_EXACT_HTF,
		MODE_SMOOTH_SCALED
	};

	// Where the source bars come from.
	enum SourceKind
	{
		SRC_OWN,				// the chart's own bars, grouped
		SRC_HIDDEN_INTRADAY,	// a hidden intraday chart at the source timeframe
		SRC_HIDDEN_DAILY		// the hidden daily chart, its days grouped
	};

	const int PI_SOURCE_CHART	= 1;	// the hidden chart's number (0: none)
	const int PP_STATE			= 1;	// HtfState

	const int64_t US_PER_SECOND		= 1000000;
	const int64_t SECONDS_PER_DAY	= 86400;
	const int DAILY_DAYS_TO_LOAD	= 3000;	// what TPO Profile and If/Then ask for, so the studies share one daily chart

	const char* const LOG_PREFIX = "Tatanka HTF EMA: ";
	// TPO Profile's request, for the same cause.
	const char* const MSG_NO_END_TIMES = "Reload the chart (Chart >> Reload and Recalculate). Tick, volume and range bars need their end times.";

	bool IsIntradayUnit(int unit)
	{
		return unit == UNIT_SECONDS || unit == UNIT_MINUTES;
	}

	// NinjaTrader's GetPeriodSeconds for the source timeframe's unit.
	double UnitSeconds(int unit)
	{
		switch (unit)
		{
			case UNIT_SECONDS:	return 1.0;
			case UNIT_MINUTES:	return 60.0;
			case UNIT_DAYS:		return 86400.0;
			case UNIT_WEEKS:	return 604800.0;
			case UNIT_MONTHS:	return 2592000.0;
			case UNIT_YEARS:	return 31536000.0;
		}
		return 0.0;
	}

	// C#'s Math.Round: a tie goes to the even integer (10.5 -> 10).
	double RoundHalfEven(double x)
	{
		const double whole	= std::floor(x);
		const double part	= x - whole;
		if (part > 0.5)
			return whole + 1.0;
		if (part < 0.5)
			return whole;
		return std::fmod(whole, 2.0) == 0.0 ? whole : whole + 1.0;
	}

	// NinjaTrader's GetScaledLength: EMA length x chart bars per source bar (21 x 12 = 252 on a 5-minute chart,
	// 21 x 0.5 = 10.5 -> 10 on a 2-hour chart), the plain length when either timeframe has no length in seconds.
	int ScaledLength(int length, double htfSeconds, double chartSeconds)
	{
		if (htfSeconds <= 0 || chartSeconds <= 0)
			return (std::max)(1, length);
		const double rounded = RoundHalfEven(length * (htfSeconds / chartSeconds));
		// C#'s unchecked (int) of a value out of range is int.MinValue, so Math.Max gives 1.
		if (!(rounded < 2147483648.0))
			return 1;
		return (std::max)(1, (int)rounded);
	}

	int64_t FloorDiv(int64_t value, int64_t divisor)
	{
		const int64_t quotient = value / divisor;
		return (value % divisor != 0 && (value < 0) != (divisor < 0)) ? quotient - 1 : quotient;
	}

	int64_t Micros(const SCDateTime& t)
	{
		return t.AsMicrosecondsSinceBaseDate();
	}

	// A column Sierra Chart adds with Include Columns With No Data: no volume, no trades, and either all zero or
	// flat at the previous close (the Periodic Volume Profile's rule). NinjaTrader has no bar there. A real bar
	// with no volume that does not move (a symbol whose data has no volume) looks the same and is skipped too.
	bool IsEmptyColumn(double volume, double trades, double open, double high, double low, double close, bool hasPrevious,
		double previousClose)
	{
		if (volume != 0 || trades != 0)
			return false;
		if (open == 0 && high == 0 && low == 0 && close == 0)
			return true;
		return hasPrevious && open == previousClose && high == previousClose && low == previousClose && close == previousClose;
	}

	// ---- Bar times (the Periodic Volume Profile's rules) ----

	struct ChartSessions
	{
		int		DayStart				= 0;
		int		DayEnd					= 0;
		int		EveningStart			= 0;
		int		EveningEnd				= 0;
		bool	UseEvening				= false;
		bool	NewBarAtSessionStart	= false;
	};

	ChartSessions SessionsOf(SCStudyInterfaceRef sc)
	{
		ChartSessions s;
		s.DayStart				= sc.StartTime1;
		s.DayEnd				= sc.EndTime1;
		s.EveningStart			= sc.StartTime2;
		s.EveningEnd			= sc.EndTime2;
		s.UseEvening			= sc.UseSecondStartEndTimes != 0;
		s.NewBarAtSessionStart	= sc.NewBarAtSessionStart != 0;
		return s;
	}

	// start..end inclusive; a range may cross midnight.
	bool InClockRange(int clock, int start, int end)
	{
		return start <= end ? clock >= start && clock <= end : clock >= start || clock <= end;
	}

	// The first instant after barStart (seconds since Sierra's base date) at which a time bar ends early: each
	// session end that no session continues and, with New Bar at Session Start, the trading day's start.
	// INT64_MAX when there is none or the Session Times are unset. NinjaTrader's bars end at its session
	// boundaries too, and it stamps them there.
	int64_t SessionCutAfter(int64_t barStart, const ChartSessions& s)
	{
		if (s.DayStart == s.DayEnd)
			return INT64_MAX;
		auto trading = [&s](int clock)
		{
			clock %= (int)SECONDS_PER_DAY;
			return InClockRange(clock, s.DayStart, s.DayEnd) || (s.UseEvening && InClockRange(clock, s.EveningStart, s.EveningEnd));
		};
		int cuts[3];
		int count = 0;
		if (s.NewBarAtSessionStart)
			cuts[count++] = s.UseEvening ? s.EveningStart : s.DayStart;
		if (!trading(s.DayEnd + 1))
			cuts[count++] = s.DayEnd + 1;
		if (s.UseEvening && !trading(s.EveningEnd + 1))
			cuts[count++] = s.EveningEnd + 1;

		const int64_t date	= FloorDiv(barStart, SECONDS_PER_DAY);
		const int64_t clock	= barStart - date * SECONDS_PER_DAY;
		int64_t first = INT64_MAX;
		for (int k = 0; k < count; k++)
			first = (std::min)(first, (cuts[k] > clock ? date : date + 1) * SECONDS_PER_DAY + cuts[k]);
		return first;
	}

	// A time bar's close, NinjaTrader's stamp: its start plus its length, or earlier where the next bar starts
	// inside it or where the Session Times cut it (cutSeconds from SessionCutAfter). Microseconds.
	int64_t TimeBarEnd(int64_t startUs, int64_t lengthSeconds, bool hasNext, int64_t nextStartUs, int64_t cutSeconds)
	{
		int64_t end = startUs + lengthSeconds * US_PER_SECOND;
		if (hasNext && startUs < nextStartUs && nextStartUs < end)
			end = nextStartUs;
		if (cutSeconds != INT64_MAX && cutSeconds * US_PER_SECOND < end)
			end = cutSeconds * US_PER_SECOND;
		return end;
	}

	// The close of trading date `date`: its session's end (the end time is inclusive, so one second after it).
	// A daily bar is stamped there, and a chart bar cut by the session end closes there too.
	int64_t TradingDateClose(int date, const ChartSessions& s)
	{
		return ((int64_t)date * SECONDS_PER_DAY + s.DayEnd + 1) * US_PER_SECOND;
	}

	// ---- The chart ----

	struct ChartInfo
	{
		bool	Intraday		= false;
		bool	TimeBars		= false;	// intraday bars of a fixed time length
		int		SecondsPerBar	= 0;
		bool	Daily			= false;	// a Historical Daily chart
		bool	OneDayBars		= false;	// a Historical Daily chart of 1 day per bar
		double	PeriodSeconds	= 0;		// NinjaTrader's GetPeriodSeconds of the chart's bars (0: none)
		bool	EndTimes		= false;	// sc.BaseDataEndDateTime is filled
	};

	ChartInfo ChartInfoOf(SCStudyInterfaceRef sc)
	{
		ChartInfo c;
		n_ACSIL::s_BarPeriod barPeriod;
		sc.GetBarPeriodParameters(barPeriod);
		c.EndTimes = sc.BaseDataEndDateTime.GetArraySize() >= sc.ArraySize;
		if (barPeriod.ChartDataType == INTRADAY_DATA)
		{
			c.Intraday		= true;
			c.TimeBars		= barPeriod.IntradayChartBarPeriodType == IBPT_DAYS_MINS_SECS && sc.SecondsPerBar > 0;
			c.SecondsPerBar	= c.TimeBars ? sc.SecondsPerBar : 0;
			c.PeriodSeconds	= c.SecondsPerBar;
		}
		else if (barPeriod.ChartDataType == DAILY_DATA)
		{
			c.Daily = true;
			const int days = barPeriod.HistoricalChartDaysPerBar > 0 ? barPeriod.HistoricalChartDaysPerBar : 1;
			switch (barPeriod.HistoricalChartBarPeriodType)
			{
				case HISTORICAL_CHART_PERIOD_DAYS:
					c.OneDayBars	= days == 1;
					c.PeriodSeconds	= 86400.0 * days;
					break;
				case HISTORICAL_CHART_PERIOD_WEEKLY:	c.PeriodSeconds = 604800.0;			break;
				case HISTORICAL_CHART_PERIOD_MONTHLY:	c.PeriodSeconds = 2592000.0;		break;
				case HISTORICAL_CHART_PERIOD_QUARTERLY:	c.PeriodSeconds = 3.0 * 2592000.0;	break;
				case HISTORICAL_CHART_PERIOD_YEARLY:	c.PeriodSeconds = 31536000.0;		break;
				default:								break;
			}
		}
		return c;
	}

	// Which source bars the chart's own bars make exactly: second or minute sources on shorter time bars that
	// divide them; day, week, month and year sources on intraday bars shorter than a day (or on 1-day bars).
	int ChooseSource(int unit, int64_t sourceSeconds, const ChartInfo& c)
	{
		if (IsIntradayUnit(unit))
		{
			if (c.TimeBars && c.SecondsPerBar < sourceSeconds && sourceSeconds % c.SecondsPerBar == 0)
				return SRC_OWN;
			return SRC_HIDDEN_INTRADAY;
		}
		if ((c.Intraday && !(c.TimeBars && c.SecondsPerBar >= SECONDS_PER_DAY)) || c.OneDayBars)
			return SRC_OWN;
		return SRC_HIDDEN_DAILY;
	}

	int TradingDateOfBar(SCStudyInterfaceRef sc, const ChartInfo& c, int i)
	{
		return c.Daily ? sc.BaseDateTimeIn[i].GetDate() : sc.GetTradingDayDate(sc.BaseDateTimeIn[i]);
	}

	// A day, week, month or year source's unit of a trading date. A week is keyed by its Sunday, so the Sunday
	// evening session (Monday's trading date) is in Monday's week.
	int64_t DateUnitKey(int date, int unit)
	{
		const SCDateTime day(date, 0);
		if (unit == UNIT_DAYS)
			return date;
		if (unit == UNIT_WEEKS)
			return date - day.GetDayOfWeek();
		if (unit == UNIT_MONTHS)
			return (int64_t)day.GetYear() * 12 + day.GetMonth();
		return day.GetYear();
	}

	// ---- State ----

	// The source series as NinjaTrader's second series has it: each bar's close stamp, its last price, its
	// trading date, and NinjaTrader's EMA through it (seeded with the first bar's price).
	struct SourceBars
	{
		std::vector<int64_t>	Close;
		std::vector<double>		Price;
		std::vector<int>		Date;
		std::vector<double>		Ema;

		int Count() const { return (int)Close.size(); }

		void Resize(int n)
		{
			Close.resize((size_t)n);
			Price.resize((size_t)n);
			Date.resize((size_t)n);
			Ema.resize((size_t)n);
		}

		// Sets bar k (k <= Count()); lowers firstChanged to k and lowS to its old and new close when it changed.
		void Set(int k, int64_t close, double price, int date, int& firstChanged, int64_t& lowS)
		{
			if (k == Count())
			{
				Close.push_back(close);
				Price.push_back(price);
				Date.push_back(date);
				Ema.push_back(0.0);
			}
			else if (Close[(size_t)k] == close && Price[(size_t)k] == price && Date[(size_t)k] == date)
				return;
			else
			{
				lowS = (std::min)(lowS, Close[(size_t)k]);
				Close[(size_t)k]	= close;
				Price[(size_t)k]	= price;
				Date[(size_t)k]		= date;
			}
			if (k < firstChanged)
				firstChanged = k;
			lowS = (std::min)(lowS, close);
		}

		// Drops the bars from k on.
		void Truncate(int k, int& firstChanged, int64_t& lowS)
		{
			if (k >= Count())
				return;
			lowS = (std::min)(lowS, Close[(size_t)k]);
			firstChanged = (std::min)(firstChanged, k);
			Resize(k);
		}
	};

	// One source bar grouped from the chart's own bars.
	struct OwnGroup
	{
		int		FirstBar	= 0;
		int		LastBar		= 0;
		int64_t	FirstKey	= 0;	// a second or minute source: the bar's start (us)
		int64_t	Key			= 0;	// the unit key of its newest chart bar
		int		Units		= 0;	// unit changes since the group opened (a source of several days, weeks...)
		int		LastDate	= 0;	// the trading date of its newest chart bar
	};

	struct HtfState
	{
		// The chart's bars as last computed.
		std::vector<int64_t>	ChartClose;		// each bar's close stamp (us)
		std::vector<double>		Smooth;			// the chart-timeframe EMA
		std::vector<char>		Empty;			// an empty column (Include Columns With No Data)
		std::vector<int>		Real;			// the bars holding trades up to and including this one
		int						LastLive		= -1;	// the bar last computed as the forming one
		bool					EndTimesLogged	= false;

		// The source.
		int						Kind			= -1;
		SourceBars				Src;
		std::vector<int>		GroupOf;		// SRC_OWN: each chart bar's group (-1: none yet), and its group as of that bar
		std::vector<int64_t>	GroupKeyAt;
		std::vector<int>		GroupUnitsAt;
		std::vector<int>		GroupDateAt;
		std::vector<OwnGroup>	Groups;
		int						Chart			= 0;	// the hidden chart read last
		int						FirstDate		= 0;	// this chart's first trading date when the source was read
		std::vector<int64_t>	HiddenStart;	// SRC_HIDDEN_INTRADAY: the hidden chart's bar starts (us)
		int						HiddenFirst		= 0;	// its first bar on or after FirstDate
		std::vector<int>		Days;			// a daily chart of several days, weekly or monthly: the trading dates its
												// bars hold (ChartBarClose; SRC_HIDDEN_INTRADAY uses Src.Date)

		// The hidden chart's resolution (the Periodic Volume Profile's rules).
		bool					Resolved		= false;
		int						ResolvedKind	= -1;
		int						ResolvedSeconds	= 0;
		std::string				Requested;		// this chart's symbol then
		bool					Mismatch		= false;
		bool					Logged			= false;

		void ResetSource()
		{
			Src = SourceBars();
			GroupOf.clear();
			GroupKeyAt.clear();
			GroupUnitsAt.clear();
			GroupDateAt.clear();
			Groups.clear();
			HiddenStart.clear();
			Days.clear();
			HiddenFirst	= 0;
			Chart		= 0;
			FirstDate	= 0;
		}
	};

	HtfState& StateOf(SCStudyInterfaceRef sc)
	{
		void*& slot = sc.GetPersistentPointer(PP_STATE);
		if (slot == nullptr)
			slot = new HtfState();
		return *static_cast<HtfState*>(slot);
	}

	void DeleteState(SCStudyInterfaceRef sc)
	{
		void*& slot = sc.GetPersistentPointer(PP_STATE);
		delete static_cast<HtfState*>(slot);
		slot = nullptr;
	}

	// ---- The source from the chart's own bars ----

	// Groups the chart's bars into source bars from chart bar `from` on (resuming the group of the bar before it).
	// A second or minute source: buckets of its length from the trading day's start, so on an ETH chart 60 minutes
	// lands on the hour and 240 minutes on the session open, cut at the session end, as NinjaTrader builds them.
	// A day, week, month or year source: the bars' trading dates, so the Sunday evening session counts as Monday;
	// several units count unit changes from the chart's first bar. Empty columns are no bars (st.Empty).
	void UpdateOwnSource(SCStudyInterfaceRef sc, HtfState& st, const ChartInfo& chart, const ChartSessions& sessions, int unit,
		int period, int from, int& firstChanged, int64_t& lowS)
	{
		const int n = sc.ArraySize;
		const bool intradayUnit		= IsIntradayUnit(unit);
		const int64_t bucketUs		= (int64_t)period * (unit == UNIT_MINUTES ? 60 : 1) * US_PER_SECOND;
		const int unitsPerGroup		= intradayUnit ? 1 : period;
		const bool resume = from > 0 && from <= n && from <= (int)st.GroupOf.size() && st.GroupOf[(size_t)from - 1] >= 0;
		st.GroupOf.resize((size_t)n);
		st.GroupKeyAt.resize((size_t)n);
		st.GroupUnitsAt.resize((size_t)n);
		st.GroupDateAt.resize((size_t)n);
		int i = 0;
		if (resume)
		{
			// The group of the bar before `from`, as it stood after that bar.
			const size_t before = (size_t)from - 1;
			const int g = st.GroupOf[before];
			st.Groups.resize((size_t)g + 1);
			OwnGroup& last	= st.Groups.back();
			last.LastBar	= from - 1;
			while (st.Empty[(size_t)last.LastBar])	// its newest bar with trades
				last.LastBar--;
			last.Key		= st.GroupKeyAt[before];
			last.Units		= st.GroupUnitsAt[before];
			last.LastDate	= st.GroupDateAt[before];
			i = from;
		}
		else
			st.Groups.clear();
		const int keep = resume ? (int)st.Groups.size() - 1 : 0;
		for (; i < n; i++)
		{
			if (st.Empty[(size_t)i])
			{
				// No bar to NinjaTrader: the group stands as it was.
				const bool any = !st.Groups.empty();
				st.GroupOf[(size_t)i]		= any ? (int)st.Groups.size() - 1 : -1;
				st.GroupKeyAt[(size_t)i]	= any ? st.Groups.back().Key : 0;
				st.GroupUnitsAt[(size_t)i]	= any ? st.Groups.back().Units : 0;
				st.GroupDateAt[(size_t)i]	= any ? st.Groups.back().LastDate : 0;
				continue;
			}
			int64_t key;
			int date;
			if (intradayUnit)
			{
				const int64_t start		= Micros(sc.BaseDateTimeIn[i]);
				const int64_t dayStart	= Micros(sc.GetTradingDayStartDateTimeOfBar(sc.BaseDateTimeIn[i]));
				const int64_t elapsed	= (std::max)((int64_t)0, start - dayStart);
				key		= dayStart + elapsed / bucketUs * bucketUs;
				date	= TradingDateOfBar(sc, chart, i);
			}
			else
			{
				date	= TradingDateOfBar(sc, chart, i);
				key		= DateUnitKey(date, unit);
			}
			// A group keeps its state as of its last bar: it is resumed from there.
			bool open = st.Groups.empty();
			if (!open)
			{
				OwnGroup& g = st.Groups.back();
				if (key != g.Key)
				{
					if (g.Units + 1 >= unitsPerGroup)
						open = true;
					else
					{
						g.Units++;
						g.Key = key;
					}
				}
			}
			if (open)
			{
				OwnGroup g;
				g.FirstBar	= i;
				g.FirstKey	= key;
				g.Key		= key;
				st.Groups.push_back(g);
			}
			OwnGroup& g = st.Groups.back();
			g.LastBar	= i;
			g.LastDate	= (std::max)(g.LastDate, date);
			st.GroupOf[(size_t)i]		= (int)st.Groups.size() - 1;
			st.GroupKeyAt[(size_t)i]	= g.Key;
			st.GroupUnitsAt[(size_t)i]	= g.Units;
			st.GroupDateAt[(size_t)i]	= g.LastDate;
		}
		st.Src.Truncate((int)st.Groups.size(), firstChanged, lowS);
		for (int k = keep; k < (int)st.Groups.size(); k++)
		{
			const OwnGroup& g = st.Groups[(size_t)k];
			const int64_t close = intradayUnit
				? TimeBarEnd(g.FirstKey, bucketUs / US_PER_SECOND, false, 0, SessionCutAfter(FloorDiv(g.FirstKey, US_PER_SECOND), sessions))
				: TradingDateClose(g.LastDate, sessions);
			st.Src.Set(k, close, sc.Close[g.LastBar], g.LastDate, firstChanged, lowS);
		}
	}

	// ---- The source from a hidden chart ----

	std::string ChartSymbol(SCStudyInterfaceRef sc, int chartNumber)
	{
		const SCString symbol = sc.GetChartSymbol(chartNumber);
		return symbol.GetChars();
	}

	// Equal Session Times as far as they decide which bars exist.
	bool SameSessionTimes(const n_ACSIL::s_ChartSessionTimes& a, const n_ACSIL::s_ChartSessionTimes& b)
	{
		if (a.StartTime.GetTimeInSeconds() != b.StartTime.GetTimeInSeconds() || a.EndTime.GetTimeInSeconds() != b.EndTime.GetTimeInSeconds()
			|| (a.UseEveningSessionTimes != 0) != (b.UseEveningSessionTimes != 0) || a.LoadWeekendDataSetting != b.LoadWeekendDataSetting)
			return false;
		return a.UseEveningSessionTimes == 0 || (a.EveningStartTime.GetTimeInSeconds() == b.EveningStartTime.GetTimeInSeconds()
			&& a.EveningEndTime.GetTimeInSeconds() == b.EveningEndTime.GetTimeInSeconds());
	}

	// Whether chart `chartNumber` holds the source bars: intraday bars of the source's length with this chart's
	// Session Times and time zone, or 1-day Historical Daily bars, of this chart's symbol (`symbol`). NinjaTrader's
	// second series is always the chart's own instrument, so a chart of another symbol is never read.
	bool SourceChartMatches(SCStudyInterfaceRef sc, int chartNumber, const std::string& symbol, int kind, int sourceSeconds)
	{
		if (ChartSymbol(sc, chartNumber) != symbol)
			return false;
		n_ACSIL::s_BarPeriod period;
		sc.GetBarPeriodParametersForChart(chartNumber, period);
		if (kind == SRC_HIDDEN_DAILY)
			return period.ChartDataType == DAILY_DATA && period.HistoricalChartBarPeriodType == HISTORICAL_CHART_PERIOD_DAYS
				&& period.HistoricalChartDaysPerBar <= 1;
		if (period.ChartDataType != INTRADAY_DATA || period.IntradayChartBarPeriodType != IBPT_DAYS_MINS_SECS
			|| period.IntradayChartBarPeriodParameter1 != sourceSeconds)
			return false;
		n_ACSIL::s_ChartSessionTimes mine, theirs;
		sc.GetSessionTimesFromChart(sc.ChartNumber, mine);
		sc.GetSessionTimesFromChart(chartNumber, theirs);
		if (!SameSessionTimes(mine, theirs))
			return false;
		const SCString zone = sc.GetChartTimeZone(chartNumber);
		return zone == sc.GetChartTimeZone(sc.ChartNumber);
	}

	// The hidden intraday chart's Days to Load: 0 takes this chart's (Sierra Chart's documented meaning); with
	// Load Chart Data by Date Range, the days from its start date to today.
	int SourceDaysToLoad(SCStudyInterfaceRef sc)
	{
		if (sc.LoadChartDataByDateRange == 0 || sc.ChartDataStartDate <= 0)
			return 0;
		return (std::max)(1, sc.CurrentSystemDateTime.GetDate() - sc.ChartDataStartDate + 1);
	}

	// The hidden source chart, found or opened. Sierra Chart hands every chart and study asking for the same
	// settings the same chart, so it is never rewritten (UpdatePriorChartNumberParametersToMatch = 0): a chart
	// of another symbol or settings finds or opens another one.
	int OpenSourceChart(SCStudyInterfaceRef sc, int kind, int sourceSeconds, int prior)
	{
		s_ACSOpenChartParameters p;
		p.PriorChartNumber					= prior;
		p.Symbol							= sc.GetRealTimeSymbol();
		p.ContinuousFuturesContractOption	= sc.ContinuousFuturesContractOption;
		p.HideNewChart						= 1;
		p.UpdatePriorChartNumberParametersToMatch = 0;
		if (kind == SRC_HIDDEN_DAILY)
		{
			p.ChartDataType							= DAILY_DATA;
			p.HistoricalChartBarPeriod				= HISTORICAL_CHART_PERIOD_DAYS;
			p.HistoricalChartBarPeriodLengthInDays	= 1;
			p.DaysToLoad							= DAILY_DAYS_TO_LOAD;
			return sc.OpenChartOrGetChartReference(p);
		}
		n_ACSIL::s_ChartSessionTimes times;
		sc.GetSessionTimesFromChart(sc.ChartNumber, times);
		p.ChartDataType				= INTRADAY_DATA;
		p.IntradayBarPeriodType		= IBPT_DAYS_MINS_SECS;
		p.IntradayBarPeriodLength	= sourceSeconds;
		p.DaysToLoad				= SourceDaysToLoad(sc);
		p.SessionStartTime.SetTime(sc.StartTime1);
		p.SessionEndTime.SetTime(sc.EndTime1);
		p.EveningSessionStartTime.SetTime(sc.StartTime2);
		p.EveningSessionEndTime.SetTime(sc.EndTime2);
		p.UseEveningSession			= sc.UseSecondStartEndTimes != 0 ? 1 : 0;
		p.LoadWeekendData			= times.LoadWeekendDataSetting;
		p.ChartTimeZone				= sc.GetChartTimeZone(sc.ChartNumber);
		p.IncludeColumnsWithNoData	= 0;	// NinjaTrader's series has no empty bars
		return sc.OpenChartOrGetChartReference(p);
	}

	// The hidden chart's number (0: none), resolved on a full recalculation (as Sierra Chart advises), while
	// there is none, when this chart's symbol or the source changed, and when the chart no longer matches (another
	// symbol or settings written into it; then without it as the prior chart). A chart found that does not match,
	// a chart of another symbol included, is not used: it is looked for again on the next full recalculation.
	int ResolveSourceChart(SCStudyInterfaceRef sc, HtfState& st, int kind, int sourceSeconds)
	{
		int& chart = sc.GetPersistentInt(PI_SOURCE_CHART);
		const std::string symbol = sc.GetRealTimeSymbol().GetChars();
		const bool changed = !st.Resolved || symbol != st.Requested || kind != st.ResolvedKind || sourceSeconds != st.ResolvedSeconds;
		if (st.Mismatch && !sc.IsFullRecalculation && !changed)
			return 0;
		int prior = chart;
		bool resolve = sc.IsFullRecalculation || chart == 0 || changed;
		if (!resolve && !SourceChartMatches(sc, chart, symbol, kind, sourceSeconds))
		{
			resolve	= true;
			prior	= 0;
		}
		if (!resolve)
			return chart;
		st.Mismatch = false;
		for (int attempt = 0; attempt < 2; attempt++)
		{
			chart = OpenSourceChart(sc, kind, sourceSeconds, prior);
			if (chart == 0 || SourceChartMatches(sc, chart, symbol, kind, sourceSeconds))
				break;
			if (prior == 0 || attempt == 1)
			{
				chart			= 0;
				st.Mismatch		= true;
				break;
			}
			prior = 0;
		}
		st.Resolved			= true;
		st.Requested		= symbol;
		st.ResolvedKind		= kind;
		st.ResolvedSeconds	= sourceSeconds;
		return chart;
	}

	// Reads the hidden intraday chart's bars from this chart's first trading date on, each stamped with its
	// close (cut by the Session Times as NinjaTrader cuts them). Only the newest bars are read again on a call.
	void ReadHiddenIntraday(SCStudyInterfaceRef sc, HtfState& st, int chartNumber, int64_t sourceSeconds, const ChartSessions& sessions,
		int firstDate, int& firstChanged, int64_t& lowS)
	{
		SCGraphData data;
		sc.GetChartBaseData(chartNumber, data);
		SCDateTimeArray times;
		sc.GetChartDateTimeArray(chartNumber, times);
		const int count = (std::min)(times.GetArraySize(), data[SC_LAST].GetArraySize());
		const int cached = (int)st.HiddenStart.size();
		bool reread = cached == 0 || count < cached || chartNumber != st.Chart || firstDate != st.FirstDate;
		if (!reread && (Micros(times[0]) != st.HiddenStart[0] || Micros(times[cached - 1]) != st.HiddenStart[(size_t)cached - 1]))
			reread = true;	// reloaded, or history added in front
		int from = reread ? 0 : (std::max)(0, cached - 2);
		if (reread)
		{
			st.Src.Truncate(0, firstChanged, lowS);
			st.HiddenStart.clear();
			// The first bar of this chart's first trading date (trading dates rise with the bars).
			int lo = 0, hi = count;
			while (lo < hi)
			{
				const int mid = lo + (hi - lo) / 2;
				if (sc.GetTradingDayDate(times[mid]) < firstDate)
					lo = mid + 1;
				else
					hi = mid;
			}
			st.HiddenFirst = lo;
		}
		st.HiddenStart.resize((size_t)count);
		for (int k = from; k < count; k++)
			st.HiddenStart[(size_t)k] = Micros(times[k]);
		st.Src.Truncate((std::max)(0, count - st.HiddenFirst), firstChanged, lowS);
		for (int k = (std::max)(from, st.HiddenFirst); k < count; k++)
		{
			const int64_t start		= st.HiddenStart[(size_t)k];
			const bool hasNext		= k + 1 < count;
			const int64_t close		= TimeBarEnd(start, sourceSeconds, hasNext, hasNext ? st.HiddenStart[(size_t)k + 1] : 0,
				SessionCutAfter(FloorDiv(start, US_PER_SECOND), sessions));
			st.Src.Set(k - st.HiddenFirst, close, data[SC_LAST][k], sc.GetTradingDayDate(times[k]), firstChanged, lowS);
		}
		st.Chart		= chartNumber;
		st.FirstDate	= firstDate;
	}

	// Groups the hidden daily chart's days from this chart's first trading date on into the source's bars, each
	// stamped with its last day's session end. A source of several days, weeks... counts unit changes from there.
	void ReadHiddenDaily(SCStudyInterfaceRef sc, HtfState& st, int chartNumber, int unit, int period, const ChartSessions& sessions,
		int firstDate, int& firstChanged, int64_t& lowS)
	{
		SCGraphData data;
		sc.GetChartBaseData(chartNumber, data);
		SCDateTimeArray times;
		sc.GetChartDateTimeArray(chartNumber, times);
		const int count = (std::min)(times.GetArraySize(), data[SC_LAST].GetArraySize());
		if (chartNumber != st.Chart || firstDate != st.FirstDate)
			st.Src.Truncate(0, firstChanged, lowS);
		st.Days.clear();
		int groups = 0, units = 0, lastDate = 0;
		int64_t key = 0;
		double lastPrice = 0;
		bool open = false;
		for (int k = 0; k < count; k++)
		{
			const int date = times[k].GetDate();
			if (date < firstDate)
				continue;
			st.Days.push_back(date);
			const int64_t dayKey = DateUnitKey(date, unit);
			if (!open)
			{
				open	= true;
				key		= dayKey;
			}
			else if (dayKey != key)
			{
				key = dayKey;
				if (++units >= period)
				{
					st.Src.Set(groups++, TradingDateClose(lastDate, sessions), lastPrice, lastDate, firstChanged, lowS);
					units = 0;
				}
			}
			lastDate	= date;
			lastPrice	= data[SC_LAST][k];
		}
		if (open)
			st.Src.Set(groups++, TradingDateClose(lastDate, sessions), lastPrice, lastDate, firstChanged, lowS);
		st.Src.Truncate(groups, firstChanged, lowS);
		st.Chart		= chartNumber;
		st.FirstDate	= firstDate;
	}

	// ---- A daily chart of several days, weekly or monthly, on its own (Smooth Scaled) ----

	// Monday to Friday.
	bool IsWeekday(int date)
	{
		const int day = SCDateTime(date, 0).GetDayOfWeek();
		return day >= 1 && day <= 5;
	}

	// Smooth Scaled on a daily chart of several days, weekly or monthly reads no hidden chart (Live and Exact read
	// one), and its bars don't tell which days they hold. Its trading days are taken as the weekdays from its first
	// bar's date to its newest's, as NinjaTrader's are but for holidays: they place the bars' closes (ChartBarClose).
	// A day, week, month or year source's bars are grouped from them as ReadHiddenDaily groups the daily chart's days;
	// Smooth Scaled needs only where the first one closes, so they carry no price.
	void UpdateWeekdays(SCStudyInterfaceRef sc, HtfState& st)
	{
		st.Days.clear();
		const int last = sc.BaseDateTimeIn[sc.ArraySize - 1].GetDate();
		for (int date = sc.BaseDateTimeIn[0].GetDate(); date <= last; date++)
			if (IsWeekday(date))
				st.Days.push_back(date);
	}

	void UpdateWeekdaySource(HtfState& st, int unit, int period, const ChartSessions& sessions, int& firstChanged, int64_t& lowS)
	{
		int groups = 0, units = 0;
		int64_t key = 0;
		for (size_t k = 0; k < st.Days.size(); k++)
		{
			const int64_t dayKey = DateUnitKey(st.Days[k], unit);
			if (k > 0 && dayKey != key && ++units >= period)
			{
				st.Src.Set(groups++, TradingDateClose(st.Days[k - 1], sessions), 0.0, st.Days[k - 1], firstChanged, lowS);
				units = 0;
			}
			key = dayKey;
		}
		if (!st.Days.empty())
			st.Src.Set(groups++, TradingDateClose(st.Days.back(), sessions), 0.0, st.Days.back(), firstChanged, lowS);
		st.Src.Truncate(groups, firstChanged, lowS);
	}

	// ---- The chart's bars ----

	// A chart bar's close as NinjaTrader stamps it: a time bar's end (cut by the session); a tick, volume or
	// range bar's last trade; a daily bar's session end. A bar of several days, a week or a month closes at its last
	// trading date's session end: the last of `days` (the trading dates, rising) before the next bar's date. Sierra
	// Chart dates such a bar by its first day. The newest such bar is open-ended: the forming rule decides.
	int64_t ChartBarClose(SCStudyInterfaceRef sc, const ChartInfo& c, const ChartSessions& sessions, const std::vector<int>& days, int i)
	{
		const int n				= sc.ArraySize;
		const bool hasNext		= i + 1 < n;
		const int64_t start		= Micros(sc.BaseDateTimeIn[i]);
		if (c.Intraday)
		{
			const int64_t next = hasNext ? Micros(sc.BaseDateTimeIn[i + 1]) : 0;
			if (c.TimeBars)
				return TimeBarEnd(start, c.SecondsPerBar, hasNext, next, SessionCutAfter(FloorDiv(start, US_PER_SECOND), sessions));
			if (c.EndTimes)
				return Micros(sc.BaseDataEndDateTime[i]);
			// Without end times (they need the chart reloaded once): the next bar's start.
			return hasNext ? next - 1 : (std::max)(start, Micros(sc.LatestDateTimeForLastBar));
		}
		const int date = sc.BaseDateTimeIn[i].GetDate();
		if (c.OneDayBars)
			return TradingDateClose(date, sessions);
		if (!hasNext)
			return INT64_MAX;
		int lastDate = sc.BaseDateTimeIn[i + 1].GetDate() - 1;
		const auto it = std::upper_bound(days.begin(), days.end(), lastDate);
		if (it != days.begin() && *(it - 1) >= date)
			lastDate = *(it - 1);
		return TradingDateClose(lastDate, sessions);
	}

	// The newest trade of the last bar (sc.LatestDateTimeForLastBar when it lies in the bar), else its start
	// (its last trade on tick, volume and range bars).
	int64_t LatestTrade(SCStudyInterfaceRef sc, const ChartInfo& c, int64_t lastClose)
	{
		const int last			= sc.ArraySize - 1;
		const int64_t start		= Micros(sc.BaseDateTimeIn[last]);
		const int64_t latest	= Micros(sc.LatestDateTimeForLastBar);
		// A daily bar's session starts the evening before its date.
		if (latest > 0 && (c.Daily || latest >= start) && latest <= lastClose)
			return latest;
		if (c.Intraday && !c.TimeBars && c.EndTimes)
			return Micros(sc.BaseDataEndDateTime[last]);
		return start;
	}

	// How many source bars NinjaTrader has closed by a chart bar stamped `close`: those stamped before it (a
	// source bar with the same stamp runs after the chart bar). On the forming bar, those whose close a trade has
	// reached: a trade on a source bar's close opens the next source bar, and NinjaTrader runs it on the source
	// series first. A forming tick, volume or range bar is stamped with that same trade but is still open
	// (openEnded), so its stamp doesn't hold the source bar back; once it closes there, the reload's rule applies.
	int ClosedSourceBars(const SourceBars& src, int64_t close, bool forming, int64_t latest, bool openEnded)
	{
		int64_t limit = close;
		if (forming && latest < INT64_MAX && (openEnded || latest + 1 < limit))
			limit = latest + 1;
		return (int)(std::lower_bound(src.Close.begin(), src.Close.end(), limit) - src.Close.begin());
	}
}

SCSFExport scsf_TatankaHtfEma(SCStudyInterfaceRef sc)
{
	SCSubgraphRef Subgraph_HtfEma = sc.Subgraph[0];

	SCInputRef Input_HtfUnit	= sc.Input[0];
	SCInputRef Input_HtfPeriod	= sc.Input[1];
	SCInputRef Input_EmaLength	= sc.Input[2];
	SCInputRef Input_Mode		= sc.Input[3];

	if (sc.SetDefaults)
	{
		sc.GraphName		= "Tatanka HTF EMA (1hr 21 EMA)";
		sc.StudyDescription	= "Tatanka HTF EMA v1.0.1: the 1-hour 21-period EMA (by default) on any chart timeframe. "
							  "Live HTF = the developing source EMA: one EMA step from the last closed source bar's EMA at the chart's price. "
							  "Exact HTF = the EMA through the last closed source bar: it steps once per source bar, at the first chart bar after that bar closes. "
							  "Smooth Scaled = a chart-timeframe EMA with the length scaled to match. "
							  "Free and open source (MPL 2.0). tatankatrading.com";
		sc.GraphRegion		= 0;
		sc.ValueFormat		= VALUEFORMAT_INHERITED;
		sc.AutoLoop			= 0;
		sc.UpdateAlways		= 0;
		// Tick, volume and range bars are stamped with their last trade (sc.BaseDataEndDateTime), which Sierra
		// Chart keeps only when this is set here.
		sc.MaintainAdditionalChartDataArrays = 1;

		Subgraph_HtfEma.Name			= "HTF EMA";
		Subgraph_HtfEma.DrawStyle		= DRAWSTYLE_LINE;
		Subgraph_HtfEma.PrimaryColor	= RGB(128, 128, 128);
		Subgraph_HtfEma.LineWidth		= 2;
		Subgraph_HtfEma.DrawZeros		= 0;
		// NinjaTrader's price marker: the last value on the price scale.
		Subgraph_HtfEma.LineLabel		= LL_DISPLAY_VALUE | LL_VALUE_ALIGN_VALUES_SCALE | LL_VALUE_ALIGN_CENTER;

		Input_HtfUnit.Name = "Source Timeframe Unit";
		Input_HtfUnit.SetCustomInputStrings("Seconds;Minutes;Days;Weeks;Months;Years");
		Input_HtfUnit.SetCustomInputIndex(UNIT_MINUTES);
		Input_HtfUnit.SetDescription("Pine input.timeframe type. Default Minutes + 60 = 1 hour.");

		Input_HtfPeriod.Name = "Source Timeframe";
		Input_HtfPeriod.SetInt(60);
		Input_HtfPeriod.SetIntLimits(1, 100000);
		Input_HtfPeriod.SetDescription("Pine input.timeframe value. 60 with Minutes = 1 hour.");

		Input_EmaLength.Name = "EMA Length";
		Input_EmaLength.SetInt(21);
		Input_EmaLength.SetIntLimits(1, MAX_STUDY_LENGTH);
		Input_EmaLength.SetDescription("Pine i_len. Default 21.");

		Input_Mode.Name = "Mode";
		Input_Mode.SetCustomInputStrings("Live HTF;Exact HTF;Smooth Scaled");
		Input_Mode.SetCustomInputIndex(MODE_SMOOTH_SCALED);
		Input_Mode.SetDescription("Live HTF = the developing source EMA: one EMA step from the last closed source bar's EMA at the chart's price. "
								  "Exact HTF = the EMA through the last closed source bar: it steps once per source bar, at the first chart bar after that bar closes. "
								  "Smooth Scaled = chart-TF EMA with scaled length.");

		return;
	}

	if (sc.LastCallToFunction)
	{
		// The hidden chart stays: other charts and studies of the symbol may read it, and it closes with the
		// chartbook.
		DeleteState(sc);
		return;
	}

	HtfState& st		= StateOf(sc);
	const int n			= sc.ArraySize;
	sc.UpdateAlways		= 0;
	if (n <= 0)
		return;

	const int unit		= (std::min)((int)Input_HtfUnit.GetIndex(), (int)UNIT_YEARS);
	const int period	= (std::max)(1, Input_HtfPeriod.GetInt());
	const int length	= (std::max)(1, Input_EmaLength.GetInt());
	const int mode		= (int)Input_Mode.GetIndex();
	const double alpha	= 2.0 / (length + 1.0);

	const ChartInfo chart			= ChartInfoOf(sc);
	const ChartSessions sessions	= SessionsOf(sc);
	const int64_t sourceSeconds		= (int64_t)period * (unit == UNIT_MINUTES ? 60 : 1);
	const int scaledLength			= ScaledLength(length, period * UnitSeconds(unit), chart.PeriodSeconds);
	// Smooth Scaled needs the source only to know where its first bar closes: the chart's own bars tell.
	const int kind = mode == MODE_SMOOTH_SCALED ? SRC_OWN : ChooseSource(unit, sourceSeconds, chart);

	// Bars before `start` are as last computed. The bar before it is redone too: its close can depend on the
	// next bar's start, and the bar that was forming is final now.
	const bool full = sc.IsFullRecalculation || sc.UpdateStartIndex <= 0 || n < (int)st.ChartClose.size() || kind != st.Kind;
	if (full)
	{
		st.ChartClose.clear();
		st.Smooth.clear();
		st.LastLive = -1;
		st.ResetSource();
		st.Kind = kind;
	}
	int start = full ? 0 : (std::min)(sc.UpdateStartIndex, (int)st.ChartClose.size());
	if (st.LastLive >= 0)
		start = (std::min)(start, st.LastLive);
	start = (std::max)(0, start - 1);

	// Tick, volume and range bars without their end times: the next bar's start stands in (ChartBarClose).
	const bool noEndTimes = chart.Intraday && !chart.TimeBars && !chart.EndTimes;
	if (noEndTimes && !st.EndTimesLogged)
		sc.AddMessageToLog((std::string(LOG_PREFIX) + MSG_NO_END_TIMES).c_str(), 0);
	st.EndTimesLogged = noEndTimes;

	// The bars holding trades. NinjaTrader's bar number of bar i is Real[i] - 1.
	st.Empty.resize((size_t)n);
	st.Real.resize((size_t)n);
	for (int i = start; i < n; i++)
	{
		const bool empty = IsEmptyColumn(sc.Volume[i], sc.NumberOfTrades[i], sc.Open[i], sc.High[i], sc.Low[i], sc.Close[i], i > 0,
			i > 0 ? sc.Close[i - 1] : 0.0);
		st.Empty[(size_t)i]	= empty ? 1 : 0;
		st.Real[(size_t)i]	= (i > 0 ? st.Real[(size_t)i - 1] : 0) + (empty ? 0 : 1);
	}
	// NinjaTrader's first bar (n when no bar holds a trade yet).
	const int firstReal = (int)(std::lower_bound(st.Real.begin(), st.Real.end(), 1) - st.Real.begin());

	// The source.
	int firstChanged	= INT_MAX;
	int64_t lowS		= INT64_MAX;
	bool sourceReady	= true;
	const int firstDate	= TradingDateOfBar(sc, chart, firstReal < n ? firstReal : 0);
	const bool severalDays = chart.Daily && !chart.OneDayBars;
	if (kind == SRC_OWN && severalDays)
	{
		UpdateWeekdays(sc, st);
		if (IsIntradayUnit(unit))
			UpdateOwnSource(sc, st, chart, sessions, unit, period, start, firstChanged, lowS);
		else
			UpdateWeekdaySource(st, unit, period, sessions, firstChanged, lowS);
	}
	else if (kind == SRC_OWN)
		UpdateOwnSource(sc, st, chart, sessions, unit, period, start, firstChanged, lowS);
	else
	{
		const int chartNumber = ResolveSourceChart(sc, st, kind, (int)sourceSeconds);
		if (chartNumber == 0)
		{
			sourceReady = false;
			if (!st.Logged)
				sc.AddMessageToLog((std::string(LOG_PREFIX) + "couldn't open a hidden chart of this symbol at the source timeframe, so Live and Exact show nothing.").c_str(), 0);
			st.Logged = true;
		}
		else
		{
			st.Logged = false;
			SCDateTimeArray times;
			sc.GetChartDateTimeArray(chartNumber, times);
			// Nothing while the source history loads: a half-loaded source would seed the EMA elsewhere.
			if (times.GetArraySize() == 0 || sc.ChartIsDownloadingHistoricalData(chartNumber) != 0
				|| sc.ChartIsDownloadingHistoricalData(sc.ChartNumber) != 0)
			{
				sourceReady		= false;
				sc.UpdateAlways	= 1;
			}
			else if (kind == SRC_HIDDEN_INTRADAY)
				ReadHiddenIntraday(sc, st, chartNumber, sourceSeconds, sessions, firstDate, firstChanged, lowS);
			else
				ReadHiddenDaily(sc, st, chartNumber, unit, period, sessions, firstDate, firstChanged, lowS);
		}
		if (!sourceReady)
		{
			st.Src.Truncate(0, firstChanged, lowS);
			st.HiddenStart.clear();
			st.Days.clear();
			st.Chart = 0;
		}
	}

	// NinjaTrader's EMA through each source bar, from the first one that changed.
	SourceBars& src = st.Src;
	for (int k = firstChanged; k < src.Count(); k++)
	{
		const double price = src.Price[(size_t)k];
		src.Ema[(size_t)k] = k == 0 ? price : price * alpha + (1 - alpha) * src.Ema[(size_t)k - 1];
	}

	// Chart bars that counted a changed source bar are done again.
	if (lowS != INT64_MAX && start > 0)
	{
		const int affected = (int)(std::upper_bound(st.ChartClose.begin(), st.ChartClose.begin() + start, lowS) - st.ChartClose.begin());
		start = (std::min)(start, affected);
	}

	st.ChartClose.resize((size_t)n);
	st.Smooth.resize((size_t)n);
	for (int i = start; i < n; i++)
		st.ChartClose[(size_t)i] = ChartBarClose(sc, chart, sessions, kind == SRC_HIDDEN_INTRADAY ? src.Date : st.Days, i);

	const int64_t latest = LatestTrade(sc, chart, st.ChartClose[(size_t)n - 1]);
	// The source closed by the chart's first bar (its first bar with trades): NinjaTrader skipped those (it had no
	// chart bar yet). A closed bar is ready only past them, so never the first bar.
	const int closedAtFirst = firstReal < n ? ClosedSourceBars(src, st.ChartClose[(size_t)firstReal], false, latest, false) : 0;
	if (kind != SRC_OWN && src.Count() > 0)
	{
		// Still loading: the hidden chart has no bar for this chart's newest trade yet. Shown meanwhile is what it
		// has; the bars are done again when it catches up.
		if (src.Close.back() <= latest)
			sc.UpdateAlways = 1;
	}

	const double smoothAlpha = 2.0 / (1 + scaledLength);
	for (int i = start; i < n; i++)
	{
		if (st.Empty[(size_t)i])
		{
			// No bar to NinjaTrader: the EMA stands still and the line holds the previous bar's value.
			st.Smooth[(size_t)i]	= i > 0 ? st.Smooth[(size_t)i - 1] : 0.0;
			Subgraph_HtfEma[i]		= i > 0 ? Subgraph_HtfEma[i - 1] : 0;
			continue;
		}
		const int bar		= st.Real[(size_t)i] - 1;	// NinjaTrader's CurrentBars[0]
		const double close	= sc.Close[i];
		st.Smooth[(size_t)i] = bar == 0 ? close : close * smoothAlpha + (1 - (2.0 / (1 + scaledLength))) * st.Smooth[(size_t)i - 1];

		const bool forming	= i == n - 1;
		const int closed	= ClosedSourceBars(src, st.ChartClose[(size_t)i], forming, latest, chart.Intraday && !chart.TimeBars);
		// NinjaTrader runs nothing on a chart bar before its source series has a bar; on the forming bar the
		// source's forming bar counts.
		const bool seen		= forming ? src.Count() > 0 : closed > 0;
		const bool ready	= closed >= length && (forming || closed > closedAtFirst);
		double value = 0.0;
		if (seen && sourceReady)
		{
			if (mode == MODE_SMOOTH_SCALED)
			{
				if (bar >= scaledLength - 1)
					value = st.Smooth[(size_t)i];
			}
			else if (ready)
			{
				const double ema = src.Ema[(size_t)closed - 1];
				value = mode == MODE_EXACT_HTF ? ema : alpha * close + (1.0 - alpha) * ema;
			}
		}
		Subgraph_HtfEma[i] = static_cast<t_ChartArrayDataType>(value);
	}
	st.LastLive = n - 1;
}

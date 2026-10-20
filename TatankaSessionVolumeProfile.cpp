// Copyright (c) 2026 Tatanka Trading LLC.
// This Source Code Form is subject to the Mozilla Public License, v. 2.0.
// If a copy of the MPL was not distributed with this file, obtain one at https://mozilla.org/MPL/2.0/.
// Tatanka Session Volume Profile v1.0.0 for Sierra Chart - tatankatrading.com
// Sierra Chart port of the NinjaTrader 8 "Session Volume Profile" (chart label "Tatanka SVP").
//
// Right-aligned volume profiles for a custom session window (08:30-15:00 Chicago by default),
// built from every trade, with the POC, the value area and up/down volume per row. The engine
// below (session windows, trade to row, the tick rule, per-session rows, sessions to retain,
// POC, value area, per-bar levels, live updates) is NinjaTrader's (TatankaSessionVolumeProfile.cs,
// its TatankaVpCore namespace) with no Sierra Chart calls, so the tests can include this file.
// Where it differs on purpose, the comment says so (svp_parity_spec.md section A).
//
// Data: NinjaTrader reads a 1-tick series. Sierra Chart's equivalent is the chart's own intraday
// file at 1 Tick storage, one record per trade, read by file index (spec C). The engine takes
// the records through a small reader interface, so the tests feed it synthetic records; sessions
// that cannot be read as single trades are built from Sierra Chart's volume at price instead.
//
// Times are microseconds since Sierra Chart's base date, in the chart's time zone unless a
// comment says otherwise. Sierra bars are stamped at their START; NinjaTrader stamps them at
// their end, so a bar's value is the levels after every trade before its end.
//
// Drawing (spec D): the profiles, level lines, labels and messages are drawn by the study's
// drawing callback, opaque as NinjaTrader's default colors are, over the bars; a translucent
// histogram box is a Sierra Chart translucent range per session (SessionRight) or blended with
// the chart background (ChartRightLatest). POC, VAH and VAL per bar are three label-only
// subgraphs: their price-scale markers and the Values windows, NinjaTrader's PriceBox plots.

#include "sierrachart.h"

#include <algorithm>
#include <chrono>
#include <climits>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <functional>
#include <map>
#include <string>
#include <utility>
#include <vector>

SCDLLName("Tatanka Session Volume Profile")

namespace
{
	enum InputIndex
	{
		IN_SESSION_START,
		IN_SESSION_END,
		IN_TIME_ZONE,
		IN_VA_PERCENT,
		IN_VA_METHOD,
		IN_TICKS_PER_ROW,
		IN_SESSIONS,
		IN_VOLUME_DATA,
		IN_PLACEMENT,
		IN_WIDTH,
		IN_PADDING,
		IN_ROW_GAP,
		IN_SHOW_PROFILE,
		IN_ROW_VOLUMES,
		IN_SHOW_POC,
		IN_SHOW_VAH,
		IN_SHOW_VAL,
		IN_EXTEND_POC,
		IN_EXTEND_VAH,
		IN_EXTEND_VAL,
		IN_LINE_WIDTH,
		IN_LEVEL_LABELS,
		IN_INPUTS_IN_LABEL,
		IN_VALUES_IN_LABEL,
		IN_UP_COLOR,
		IN_DOWN_COLOR,
		IN_VA_UP_COLOR,
		IN_VA_DOWN_COLOR,
		IN_VA_LINE_COLOR,
		IN_POC_LINE_COLOR,
		IN_TEXT_COLOR,
		IN_BOX_COLOR,
		IN_BOX_OPACITY
	};

	enum SubgraphIndex { SG_POC, SG_VAH, SG_VAL };

	// The Session time zone input, in NinjaTrader's order and with its names (NT:25).
	// ExchangeTemplate is America/Chicago here: Sierra Chart has no trading-hours time zone.
	enum TimeZoneOption { TZO_EXCHANGE, TZO_CENTRAL, TZO_EASTERN, TZO_CHART, TZO_UTC };
	enum VaMethodOption { VAM_TRADINGVIEW, VAM_ATLEAST };
	enum VolumeDataOption { VD_TICK_RULE, VD_BID_ASK, VD_VAP };
	enum PlacementOption { PL_SESSION_RIGHT, PL_CHART_RIGHT_LATEST };

	const char* const ZONE_NAMES[]		= {"ExchangeTemplate", "Central", "Eastern", "Chart", "UTC"};
	const char* const PLACEMENT_NAMES[]	= {"SessionRight", "ChartRightLatest"};

	// Persistent variable keys
	const int PI_ERROR_LOGGED = 1;
	const int PP_STATE = 1;

	const int64_t US_PER_SECOND	= 1000000;
	const int64_t US_PER_HOUR	= 3600 * US_PER_SECOND;
	const int64_t US_PER_DAY	= 86400 * US_PER_SECOND;
	const int NO_DATE			= INT_MIN;

	// A session spanning more rows than this is a bad tick, not a market (ES at 1-tick rows:
	// 250,000 points). Such a trade is dropped; NinjaTrader would try to draw it (TPO precedent).
	const int64_t MAX_SESSION_ROWS	= 1000000;
	// Per-bar deltas kept per session read from ticks (spec C.7): past this, a value-area input
	// change re-reads it.
	const size_t MAX_DELTAS			= 2000000;
	// A session built from volume at price keeps all its deltas (spec C.5): there are no more of
	// them than the volume at price elements Sierra Chart keeps for its bars anyway, and they let
	// its forming bar be taken back on every call. This bound only keeps a row's 32-bit delta
	// position valid. Not const, so the tests can reach it.
	size_t	g_MaxVapDeltas			= UINT32_MAX;
	// |price / tick| beyond this is not a price (NinjaTrader's checked cast would throw).
	const double MAX_TICK_RATIO		= 4.0e15;

	const char* const MSG_NOT_INTRADAY	= "Use an intraday chart (for example, 30 Minute).";
	const char* const MSG_MULTI_DAY		= "Use bars of 1 day or shorter (for example, 30 Minute).";
	const char* const MSG_BAD_SIZE		= "Tick size, ticks per row, and session count must be positive.";
	const char* const MSG_NO_END_TIMES	= "Reload the chart (Chart >> Reload and Recalculate). Tick, volume and range bars need their end times.";
	// NinjaTrader's no-session text (NT:278), with Sierra Chart's name for Trading Hours.
	const char* const MSG_NO_TICKS		= "Tatanka SVP: no ticks in the custom session. Check historical tick data, Session Times, and session time zone.";
	const char* const MSG_READING		= "Tatanka SVP: reading tick data...";
	const char* const MSG_WAITING_VAP	= "Tatanka SVP: waiting for volume at price...";
	// Every session from volume at price (whole bars by their start time) and no bar starting in
	// any window, as 1-day bars of an ETH chart (they start at 17:00): the ticks are there.
	const char* const MSG_NO_BAR_STARTS	= "Tatanka SVP: no bar starts inside the custom session. Volume at price takes whole bars by their "
		"start time: use shorter bars (for example, 30 Minute).";
	const char* const MSG_NO_VAP		= "Volume at price is not available on this chart.";

	// Reading the chart's tick records (spec C.7): at most this long per study call, checking the
	// clock every so many records. Not const, so the tests can drive the reading in small slices.
	int		g_ReadBudgetMs		= 150;
	int64_t	g_ChunkRecords		= 20000;
	// The live path skips the records between session windows (none of them can count) with a
	// binary search when more than this many are left to read.
	const int64_t SKIP_MIN_RECORDS	= 64;
	// A history window's records must add up to the chart's volume of the bars inside it, within
	// this fraction (spec C.4 step 4): tick, volume and range bars sharing a time across the
	// window's edge can move a few trades between bars inside and outside it.
	const double VOLUME_TOLERANCE	= 0.02;
	// Time base evidence (spec C.4 step 1): completed bars checked, and the most records summed
	// for one bar's volume. The volume only breaks a tie of the first and last trades (a flat
	// market): the calibration holds the file lock outside the reading budget, so it stays at a
	// few dozen reads per bar, and a few thousand at most.
	const int		EVIDENCE_BARS		= 4;
	const int64_t	EVIDENCE_MAX_RECORDS = 5000;

	// ---- Logic (no Sierra Chart calls, so it can be unit tested) ----

	uint32_t Fnv1a(uint32_t hash, const void* data, size_t size)
	{
		const unsigned char* bytes = (const unsigned char*)data;
		for (size_t i = 0; i < size; i++)
			hash = (hash ^ bytes[i]) * 16777619u;
		return hash;
	}

	int64_t FloorDiv(int64_t value, int64_t divisor)
	{
		const int64_t quotient = value / divisor;
		return (value % divisor != 0 && (value < 0) != (divisor < 0)) ? quotient - 1 : quotient;
	}

	// Half up: 2.5 -> 3, exact for |x| < 2^52 (floor(x + 0.5) would turn 0.49999999999999994 into 1).
	double RoundHalfUp(double x)
	{
		const double f = std::floor(x);
		return x - f >= 0.5 ? f + 1 : f;
	}

	// .NET's Math.Round(x, MidpointRounding.AwayFromZero), NinjaTrader's price to tick (NT:534):
	// 2.5 -> 3, -2.5 -> -3.
	double RoundHalfAway(double x)
	{
		return x >= 0 ? RoundHalfUp(x) : -RoundHalfUp(-x);
	}

	// Sierra's tick size is a float (0.01f is 0.0099999998). This is the decimal tick it stands for.
	double DecimalTickSize(float tickSize)
	{
		if (!(tickSize > 0))
			return 0;
		char text[32];
		snprintf(text, sizeof(text), "%.6g", (double)tickSize);
		return strtod(text, nullptr);
	}

	// Sierra stores prices as floats (GC 2650.1f is 2650.10009765625). Snapped to the tick grid
	// they match NinjaTrader's tick-rounded doubles: whole ticks divided by the ticks per point
	// when that is a whole number, so 75.43 is 7543 / 100, the double nearest 75.43.
	double SnapToTick(double value, double tick)
	{
		if (!(tick > 0))
			return value;
		const double ticks		= std::round(value / tick);
		const double perPoint	= std::round(1.0 / tick);
		if (perPoint >= 1 && std::fabs(perPoint * tick - 1.0) < 1e-9)
			return ticks / perPoint;
		return ticks * tick;
	}

	// The tick index of a price, NinjaTrader's checked((long)Math.Round(price / tickSize,
	// AwayFromZero)) (NT:534). False for a price that is not a number or out of range.
	bool TickIndexOf(double price, double tick, int64_t& index)
	{
		if (!(tick > 0))
			return false;
		const double q = price / tick;
		if (!(std::fabs(q) < MAX_TICK_RATIO))
			return false;
		index = (int64_t)RoundHalfAway(q);
		return true;
	}

	// The row of a tick index: floor(tick / ticks per row) (NT:535). Rows are anchored at price 0.
	int64_t RowKeyOf(int64_t tickIndex, int ticksPerRow)
	{
		return FloorDiv(tickIndex, (int64_t)(std::max)(1, ticksPerRow));
	}

	// ---- Bars (spec B.3) ----

	// A column Sierra Chart adds with Include Columns With No Data: no volume, no trades, and
	// either all zero or flat at the previous close. It holds no trades (spec A #51) but takes
	// its place on the time axis (TatankaTpoProfile's test).
	bool IsEmptyColumn(double volume, double trades, double open, double high, double low, double close, bool hasPrevious,
		double previousClose)
	{
		if (volume != 0 || trades != 0)
			return false;
		if (open == 0 && high == 0 && low == 0 && close == 0)
			return true;
		return hasPrevious && open == previousClose && high == previousClose && low == previousClose && close == previousClose;
	}

	// Sierra Chart's Session Times in the chart's time zone: seconds since midnight, each end
	// the session's last second. The evening session is "Use Evening Session".
	struct ChartSessions
	{
		int		DayStart				= 0;
		int		DayEnd					= 0;
		int		EveningStart			= 0;
		int		EveningEnd				= 0;
		bool	UseEvening				= false;
		bool	NewBarAtSessionStart	= false;
	};

	// start..end inclusive; a range may cross midnight.
	bool InClockRange(int clock, int start, int end)
	{
		return start <= end ? clock >= start && clock <= end : clock >= start || clock <= end;
	}

	// The first instant after barStart (chart time, seconds since Sierra's base date) at which
	// a time bar ends early: each session end that no session continues, and, with New Bar at
	// Session Start, the trading day's start. INT64_MAX when there is none or the session times
	// are unset. NinjaTrader's bars end at its session boundaries too, and it stamps them there.
	int64_t SessionCutAfter(int64_t barStart, const ChartSessions& s)
	{
		if (s.DayStart == s.DayEnd)
			return INT64_MAX;
		auto trading = [&s](int clock)
		{
			clock %= SECONDS_PER_DAY;
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

	// A time bar's end, NinjaTrader's close stamp: its start plus the bar length, or earlier
	// where the next bar starts inside it (a bar cut by the data) or where the Session Times
	// cut it (cutSeconds from SessionCutAfter). Microseconds.
	int64_t TimeBarEnd(int64_t startUs, int secondsPerBar, bool hasNext, int64_t nextStartUs, int64_t cutSeconds)
	{
		int64_t end = startUs + (int64_t)secondsPerBar * US_PER_SECOND;
		if (hasNext && startUs < nextStartUs && nextStartUs < end)
			end = nextStartUs;
		if (cutSeconds != INT64_MAX && cutSeconds * US_PER_SECOND < end)
			end = cutSeconds * US_PER_SECOND;
		return end;
	}

	// The chart's bars as the engine sees them: start S, end E (NinjaTrader's close stamp), the
	// end of the time the bar covers C, and the tick-snapped low and high. A trade counts only
	// inside some bar's [S, C): times outside every bar are outside the chart's Session Times,
	// as NinjaTrader's tick series loads only the Trading Hours template's hours (spec A #20).
	// Open, Close and Volume (Sierra Chart's, as the bar shows them) check the records against
	// the chart: the records' time base and a history window's volume (spec C.4). Bars without
	// them (shorter vectors) are not checked.
	struct BarTable
	{
		std::vector<int64_t>	S;
		std::vector<int64_t>	E;
		std::vector<int64_t>	C;
		std::vector<double>		Low;
		std::vector<double>		High;
		std::vector<double>		Open;
		std::vector<double>		Close;
		std::vector<double>		Volume;

		int Count() const { return (int)S.size(); }

		void Resize(int count)
		{
			const size_t n = (size_t)(std::max)(0, count);
			S.resize(n);
			E.resize(n);
			C.resize(n);
			Low.resize(n);
			High.resize(n);
			if (!Volume.empty())
			{
				Open.resize(n);
				Close.resize(n);
				Volume.resize(n);
			}
		}

		// Bar i's open, close (tick-snapped) and volume.
		void SetTrades(int i, double open, double close, double volume)
		{
			const size_t n = (size_t)Count();
			Open.resize(n);
			Close.resize(n);
			Volume.resize(n);
			if (i < 0 || (size_t)i >= n)
				return;
			Open[(size_t)i]		= open;
			Close[(size_t)i]	= close;
			Volume[(size_t)i]	= volume;
		}

		bool HasTrades(int i) const { return i >= 0 && (size_t)i < Volume.size(); }

		void Set(int i, int64_t start, int64_t end, int64_t coverEnd, double low, double high)
		{
			if (i >= Count())
				Resize(i + 1);
			S[(size_t)i]	= start;
			E[(size_t)i]	= end;
			C[(size_t)i]	= coverEnd;
			Low[(size_t)i]	= low;
			High[(size_t)i]	= high;
		}

		// A time-based bar: it covers its whole span, [S, E).
		void SetTimeBar(int i, int64_t start, int secondsPerBar, bool hasNext, int64_t nextStart, const ChartSessions& sessions,
			double low, double high)
		{
			const int64_t end = TimeBarEnd(start, secondsPerBar, hasNext, nextStart, SessionCutAfter(FloorDiv(start, US_PER_SECOND), sessions));
			Set(i, start, end, end, low, high);
		}

		// A tick, volume or range bar: it ends at its last trade and covers up to that trade,
		// [S, min(E + 1 us, next S)): trades sharing a time with the next bar's first trade
		// count in the next bar (time cannot split them).
		void SetTradeBar(int i, int64_t start, int64_t lastTrade, bool hasNext, int64_t nextStart, double low, double high)
		{
			int64_t cover = lastTrade + 1;
			if (hasNext)
				cover = (std::min)(cover, nextStart);
			Set(i, start, lastTrade, cover, low, high);
		}

		// The last bar starting at or before t, -1 if none. hint: the previous answer (records
		// arrive in time order, so this is usually a step or two).
		int BarOf(int64_t t, int& hint) const
		{
			const int n = Count();
			if (n == 0 || t < S[0])
				return -1;
			if (hint >= 0 && hint < n && S[(size_t)hint] <= t)
			{
				for (int step = 0; step < 4; step++)
				{
					if (hint + 1 >= n || S[(size_t)hint + 1] > t)
						return hint;
					hint++;
				}
			}
			hint = (int)(std::upper_bound(S.begin(), S.end(), t) - S.begin()) - 1;
			return hint;
		}

		bool Covers(int i, int64_t t) const
		{
			return i >= 0 && i < Count() && S[(size_t)i] <= t && t < C[(size_t)i];
		}

		// Whether some bar covers part of [start, end). C never decreases (a bar's coverage ends
		// at or before the next bar's start), so the last bar starting before `end` decides.
		bool Overlaps(int64_t start, int64_t end) const
		{
			const size_t j = (size_t)(std::lower_bound(S.begin(), S.end(), end) - S.begin());
			return j > 0 && C[j - 1] > start;
		}
	};

	// ---- Session windows (spec B.4) ----

	// The Session time zone option as a Sierra Chart time zone (spec A #8): ExchangeTemplate and
	// Central are America/Chicago (Sierra Chart has no trading-hours time zone; every CME product
	// trades on Chicago's), Eastern is New York, UTC is UTC. Chart is this chart's own zone: no
	// conversion at all (IsChartZoneOption), as NinjaTrader's sessionZone = chartZone.
	TimeZonesEnum ZoneOf(int option)
	{
		switch (option)
		{
			case TZO_EASTERN:	return TIMEZONE_NEW_YORK;
			case TZO_UTC:		return TIMEZONE_UTC;
			default:			return TIMEZONE_CHICAGO;
		}
	}

	bool IsChartZoneOption(int option)
	{
		return option == TZO_CHART;
	}

	// One custom session window, in chart time: start included, end excluded. Date: the
	// session-zone date the window opens on (its identity, NinjaTrader's StartLocal).
	struct SessionWindow
	{
		int		Date		= NO_DATE;
		int64_t	StartChart	= 0;
		int64_t	EndChart	= 0;
	};

	// The windows over the chart's dates. NinjaTrader tests each trade's local time
	// (SessionClock.TryWindow, NT:463-473); converting each window's two ends to chart time once
	// gives the same membership for every trade time that converts one to one (all CME hours).
	struct WindowTable
	{
		int								StartSeconds	= 30600;	// 08:30, session zone
		int								EndSeconds		= 54000;	// 15:00
		std::vector<SessionWindow>		Windows;
		int								FirstDate		= 0;
		int								LastDate		= -1;		// < FirstDate: none generated

		void Reset(int startSeconds, int endSeconds)
		{
			StartSeconds	= startSeconds;
			EndSeconds		= endSeconds;
			Windows.clear();
			FirstDate		= 0;
			LastDate		= -1;
		}

		// Window d in session-zone wall clock: [d + start, d + end) when start < end; otherwise
		// [d + start, d + 1 day + end): overnight, or 24 hours when they are equal (NT:467-471).
		int64_t BeginLocal(int date) const { return (int64_t)date * US_PER_DAY + (int64_t)StartSeconds * US_PER_SECOND; }
		int64_t EndLocal(int date) const
		{
			const int64_t day = StartSeconds < EndSeconds ? (int64_t)date : (int64_t)date + 1;
			return day * US_PER_DAY + (int64_t)EndSeconds * US_PER_SECOND;
		}

		// Generates the windows of dates firstDate..lastDate (session zone), keeping those already
		// made. toChart: session-zone wall clock -> chart time (identity for the Chart option).
		// Windows stay increasing and disjoint; one whose converted end is not after its start
		// (a conversion artifact) is skipped.
		template <typename ToChart>
		void Cover(int firstDate, int lastDate, ToChart toChart)
		{
			if (LastDate < FirstDate || firstDate < FirstDate)
			{
				Windows.clear();
				FirstDate	= firstDate;
				LastDate	= firstDate - 1;
			}
			for (int d = LastDate + 1; d <= lastDate; d++)
			{
				SessionWindow w;
				w.Date			= d;
				w.StartChart	= toChart(BeginLocal(d));
				w.EndChart		= toChart(EndLocal(d));
				if (!Windows.empty() && w.StartChart < Windows.back().EndChart)
					w.StartChart = Windows.back().EndChart;
				if (w.EndChart > w.StartChart)
					Windows.push_back(w);
			}
			LastDate = (std::max)(LastDate, lastDate);
		}

		// The windows for chart times firstChart..lastChart (the first bar's start, the last bar's
		// end): session-zone dates from the first one's date - 1 to the last one's date + 1, so an
		// overnight window that began the evening before is there too. fromChart: chart time ->
		// session-zone wall clock; toChart: back.
		template <typename FromChart, typename ToChart>
		void CoverSpan(int64_t firstChart, int64_t lastChart, FromChart fromChart, ToChart toChart)
		{
			const int firstDate	= (int)FloorDiv((int64_t)fromChart(firstChart), US_PER_DAY) - 1;
			const int lastDate	= (int)FloorDiv((int64_t)fromChart(lastChart), US_PER_DAY) + 1;
			Cover(firstDate, lastDate, toChart);
		}

		// The window containing chart time t, -1 if none. hint as BarTable::BarOf.
		int Find(int64_t t, int& hint) const
		{
			const int n = (int)Windows.size();
			if (n == 0)
				return -1;
			if (!(hint >= 0 && hint < n && Windows[(size_t)hint].StartChart <= t && (hint + 1 >= n || Windows[(size_t)hint + 1].StartChart > t)))
			{
				hint = (int)(std::upper_bound(Windows.begin(), Windows.end(), t,
					[](int64_t value, const SessionWindow& w) { return value < w.StartChart; }) - Windows.begin()) - 1;
				if (hint < 0)
				{
					hint = 0;
					return -1;
				}
			}
			return t < Windows[(size_t)hint].EndChart ? hint : -1;
		}

		int Find(int64_t t) const
		{
			int hint = -1;
			return Find(t, hint);
		}

		// The start of the first window that starts after t, INT64_MAX if none.
		int64_t NextStart(int64_t t) const
		{
			const auto it = std::upper_bound(Windows.begin(), Windows.end(), t, [](int64_t value, const SessionWindow& w) { return value < w.StartChart; });
			return it == Windows.end() ? INT64_MAX : it->StartChart;
		}

		const SessionWindow* ByDate(int date) const
		{
			auto it = std::lower_bound(Windows.begin(), Windows.end(), date, [](const SessionWindow& w, int d) { return w.Date < d; });
			return it != Windows.end() && it->Date == date ? &*it : nullptr;
		}
	};

	// Whether a bar (not an empty column) starts inside a session window: a session built from
	// volume at price needs one, since it takes whole bars by their start time (spec C.5).
	bool AnyBarStartsInWindow(const WindowTable& windows, const BarTable& bars)
	{
		int hint = -1;
		for (int i = 0; i < bars.Count(); i++)
			if (bars.C[(size_t)i] > bars.S[(size_t)i] && windows.Find(bars.S[(size_t)i], hint) >= 0)
				return true;
		return false;
	}

	// ---- Time base of the intraday records (spec C.4 step 1) ----

	// TB_EITHER: the newest trade fits the chart's last bars both ways (the first step of the
	// calibration only; the bars' trades then decide).
	enum TimeBase { TB_UNKNOWN, TB_CHART, TB_UTC, TB_EITHER };

	// UTC -> chart time by segments of constant offset, so a record's chart time costs no
	// Sierra Chart call: the offset is probed hourly and each change bisected to the second
	// (time zones change at whole seconds).
	struct OffsetTable
	{
		std::vector<int64_t>	From;	// UTC, ascending: where each segment starts
		std::vector<int64_t>	Offset;	// chart - UTC

		template <typename UtcToChart>
		void Build(int64_t fromUtc, int64_t toUtc, UtcToChart convert)
		{
			From.clear();
			Offset.clear();
			auto offsetAt = [&convert](int64_t utc) { return (int64_t)convert(utc) - utc; };
			int64_t t = FloorDiv(fromUtc, US_PER_HOUR) * US_PER_HOUR - US_PER_HOUR;
			int64_t current = offsetAt(t);
			From.push_back(t);
			Offset.push_back(current);
			for (; t <= toUtc + US_PER_HOUR; t += US_PER_HOUR)
			{
				const int64_t next = offsetAt(t + US_PER_HOUR);
				if (next == current)
					continue;
				int64_t lo = t / US_PER_SECOND;						// offset == current
				int64_t hi = (t + US_PER_HOUR) / US_PER_SECOND;		// offset != current
				while (hi - lo > 1)
				{
					const int64_t mid = lo + (hi - lo) / 2;
					if (offsetAt(mid * US_PER_SECOND) == current)
						lo = mid;
					else
						hi = mid;
				}
				From.push_back(hi * US_PER_SECOND);
				Offset.push_back(next);
				current = next;
			}
		}

		bool Empty() const { return From.empty(); }

		int64_t ToChart(int64_t utc, size_t& hint) const
		{
			if (From.empty())
				return utc;
			if (!(hint < From.size() && From[hint] <= utc && (hint + 1 >= From.size() || From[hint + 1] > utc)))
			{
				const size_t i = (size_t)(std::upper_bound(From.begin(), From.end(), utc) - From.begin());
				hint = i == 0 ? 0 : i - 1;
			}
			return utc + Offset[hint];
		}

		int64_t ToChart(int64_t utc) const
		{
			size_t hint = 0;
			return ToChart(utc, hint);
		}
	};

	// Whether the record time t (the newest trade at or before FileRecordIndexOfLastDataRecordInChart)
	// is chart time or UTC: inside a bar's [S, C] as is -> chart time; converted from UTC -> UTC;
	// both -> TB_EITHER (a chart time zone at UTC+0 now, as London in winter, or bars longer than
	// the zone's UTC offset: one time cannot tell). spans: the last non-empty bars.
	template <typename UtcToChart>
	int CalibrateTimeBase(int64_t t, const std::vector<std::pair<int64_t, int64_t>>& spans, UtcToChart convert)
	{
		const int64_t c = convert(t);
		bool asIs = false, fromUtc = false;
		for (const std::pair<int64_t, int64_t>& s : spans)
		{
			asIs	= asIs || (s.first <= t && t <= s.second);
			fromUtc	= fromUtc || (s.first <= c && c <= s.second);
		}
		return asIs && fromUtc ? TB_EITHER : asIs ? TB_CHART : fromUtc ? TB_UTC : TB_UNKNOWN;
	}

	// The first record index in [first, last + 1] whose chart time is at or after t (records are
	// in time order). timeAt(index): one record read.
	template <typename TimeAt>
	int64_t FirstRecordAtOrAfter(int64_t first, int64_t last, int64_t t, TimeAt timeAt)
	{
		int64_t lo = first, hi = last + 1;
		while (lo < hi)
		{
			const int64_t mid = lo + (hi - lo) / 2;
			if ((int64_t)timeAt(mid) < t)
				lo = mid + 1;
			else
				hi = mid;
		}
		return lo;
	}

	// ---- Profile math (NT:560-627) ----

	// The POC (NT:565-578): the row with the most volume; on a tie the tied row nearest the
	// middle of the lowest..highest traded row, the lower one if equally close. In row keys:
	// the smallest |2k - (kMin + kMax)|, a strict "<" keeping the lower row. TatankaTpoProfile's
	// tested PickPoc, on the volume type.
	template <typename T>
	int PickPoc(const std::vector<int64_t>& keys, const std::vector<T>& totals, T maxTotal)
	{
		if (keys.empty())
			return -1;
		const int64_t span = keys.front() + keys.back();
		int best = -1;
		int64_t bestDistance = INT64_MAX;
		for (size_t i = 0; i < keys.size(); i++)
		{
			if (totals[i] != maxTotal)
				continue;
			const int64_t d = 2 * keys[i] - span;
			const int64_t distance = d < 0 ? -d : d;
			if (distance < bestDistance)
			{
				bestDistance	= distance;
				best			= (int)i;
			}
		}
		return best;
	}

	// NinjaTrader's value area (NT:579-620), line for line: from the POC, the neighbor row with
	// more volume (untraded rows count 0); on equal volume the side whose next row is nearer the
	// POC, up when equally near; TradingViewStyle stops before a row would pass the target
	// (1e-12 relative tolerance, and the stop is final), AtLeastTarget adds that row. Runs of
	// untraded rows on both sides are crossed in one step (NT:588-609), which gives the same
	// boundaries as stepping one row at a time. TatankaTpoProfile's ValueArea has another rule
	// (ties down, integer target), so it is not reused.
	void NtValueArea(const std::vector<int64_t>& keys, const std::vector<double>& totals, int pocIndex, double totalVolume, double percent,
		bool atLeast, int64_t& valKey, int64_t& vahKey, double& included)
	{
		const int count		= (int)keys.size();
		const int64_t minKey = keys[0];
		const int64_t maxKey = keys[(size_t)count - 1];
		const int64_t poc	= keys[(size_t)pocIndex];
		int64_t low = poc, high = poc;
		int below = pocIndex - 1, above = pocIndex + 1;
		included = totals[(size_t)pocIndex];
		const double target = totalVolume * (std::max)(1.0, (std::min)(100.0, percent)) / 100.0;
		while (included < target && (low > minKey || high < maxKey))
		{
			const bool hasUp	= high < maxKey;
			const bool hasDown	= low > minKey;
			const double upVolume	= hasUp && above < count && keys[(size_t)above] == high + 1 ? totals[(size_t)above] : 0;
			const double downVolume	= hasDown && below >= 0 && keys[(size_t)below] == low - 1 ? totals[(size_t)below] : 0;
			if (upVolume == 0 && downVolume == 0)
			{
				if (!hasUp)
					low = keys[(size_t)below] + 1;
				else if (!hasDown)
					high = keys[(size_t)above] - 1;
				else
				{
					const int64_t upDistance	= keys[(size_t)above] - poc;
					const int64_t downDistance	= poc - keys[(size_t)below];
					if (upDistance <= downDistance)
					{
						high	= keys[(size_t)above] - 1;
						low		= (std::min)(low, poc - (std::min)(downDistance - 1, upDistance - 2));
					}
					else
					{
						low		= keys[(size_t)below] + 1;
						high	= (std::max)(high, poc + (std::min)(upDistance - 1, downDistance - 1));
					}
				}
				continue;
			}
			const bool takeUp = hasUp && (!hasDown || upVolume > downVolume || (upVolume == downVolume && high + 1 - poc <= poc - (low - 1)));
			const double candidate = takeUp ? upVolume : downVolume;
			if (!atLeast && included + candidate > target + totalVolume * 1e-12)
				break;
			included += candidate;
			if (takeUp)
			{
				high++;
				if (above < count && keys[(size_t)above] == high)
					above++;
			}
			else
			{
				low--;
				if (below >= 0 && keys[(size_t)below] == low)
					below--;
			}
		}
		valKey = low;
		vahKey = high;
	}

	// Everything NinjaTrader's Snapshot carries but the rows (NT:498-504).
	struct ProfileStats
	{
		int64_t	MinKey			= 0;
		int64_t	MaxKey			= 0;
		int64_t	PocKey			= 0;
		int64_t	ValKey			= 0;
		int64_t	VahKey			= 0;
		double	RowSize			= 0;
		double	MaxVolume		= 0;
		double	TotalVolume		= 0;
		double	ValueAreaVolume	= 0;
		double	Poc				= 0;
		double	Vah				= 0;
		double	Val				= 0;
		double	LowEdge			= 0;
		double	HighEdge		= 0;
	};

	// The snapshot of the traded rows (keys ascending, totals = up + down), the same double
	// expressions as NT:562-627. keys must not be empty (NinjaTrader's zero snapshot, NT:564,
	// is never reached: a session exists only after a trade).
	ProfileStats ProfileOf(const std::vector<int64_t>& keys, const std::vector<double>& totals, double tick, int ticksPerRow, double percent,
		bool atLeast)
	{
		ProfileStats p;
		p.RowSize = tick * ticksPerRow;
		for (double total : totals)
			p.TotalVolume += total;
		for (double total : totals)
			p.MaxVolume = (std::max)(p.MaxVolume, total);
		const int poc	= PickPoc(keys, totals, p.MaxVolume);
		p.MinKey		= keys.front();
		p.MaxKey		= keys.back();
		p.PocKey		= keys[(size_t)poc];
		NtValueArea(keys, totals, poc, p.TotalVolume, percent, atLeast, p.ValKey, p.VahKey, p.ValueAreaVolume);
		p.Poc		= (double)p.PocKey * p.RowSize + (ticksPerRow - 1) / 2.0 * tick;
		p.Val		= (double)p.ValKey * p.RowSize;
		p.Vah		= (double)p.VahKey * p.RowSize + (ticksPerRow - 1) * tick;
		p.LowEdge	= (double)p.MinKey * p.RowSize - tick / 2;
		p.HighEdge	= (double)p.MaxKey * p.RowSize + (ticksPerRow - 0.5) * tick;
		return p;
	}

	// The three plotted levels of a session at some moment.
	struct Levels
	{
		double	Poc	= 0;
		double	Vah	= 0;
		double	Val	= 0;
	};

	// ---- Session rows ----

	// One price row: up and down volume, and where the current bar's delta for it is (so each
	// bar keeps one delta per row however the trades alternate between rows).
	struct RowCell
	{
		double		Up		= 0;
		double		Down	= 0;
		int			SlotBar	= -1;
		uint32_t	SlotPos	= 0;

		bool Traded() const { return Up > 0 || Down > 0; }
	};

	// A session's rows: a dense array indexed by key - BaseKey (NinjaTrader keeps a dictionary;
	// the order and sums are the same). MinKey..MaxKey: every key ever touched.
	struct RowGrid
	{
		int64_t					BaseKey	= 0;
		std::vector<RowCell>	Cells;
		int64_t					MinKey	= 0;
		int64_t					MaxKey	= -1;	// < MinKey: none
		int						Present	= 0;	// traded rows

		bool Empty() const { return Present == 0; }

		// Whether adding key keeps the session within MAX_SESSION_ROWS rows.
		bool Fits(int64_t key) const
		{
			if (MaxKey < MinKey)
				return true;
			const int64_t lo = (std::min)(key, MinKey);
			const int64_t hi = (std::max)(key, MaxKey);
			return hi - lo < MAX_SESSION_ROWS;
		}

		RowCell& Cell(int64_t key)
		{
			const int64_t size = (int64_t)Cells.size();
			if (size == 0)
			{
				BaseKey = key - 8;
				Cells.resize(17);
			}
			else if (key < BaseKey)
			{
				const int64_t grow = (std::max)(BaseKey - key, size / 2 + 8);
				Cells.insert(Cells.begin(), (size_t)grow, RowCell());
				BaseKey -= grow;
			}
			else if (key >= BaseKey + size)
				Cells.resize((size_t)(size + (std::max)(key - (BaseKey + size) + 1, size / 2 + 8)));
			if (MaxKey < MinKey)
				MinKey = MaxKey = key;
			else
			{
				MinKey = (std::min)(MinKey, key);
				MaxKey = (std::max)(MaxKey, key);
			}
			return Cells[(size_t)(key - BaseKey)];
		}

		const RowCell* Find(int64_t key) const
		{
			if (key < BaseKey || key - BaseKey >= (int64_t)Cells.size())
				return nullptr;
			return &Cells[(size_t)(key - BaseKey)];
		}

		// The traded rows, ascending: keys and totals (up + down, NinjaTrader's Row.Total).
		void Collect(std::vector<int64_t>& keys, std::vector<double>& totals) const
		{
			keys.clear();
			totals.clear();
			if (MaxKey < MinKey)
				return;
			for (int64_t k = MinKey; k <= MaxKey; k++)
			{
				const RowCell& c = Cells[(size_t)(k - BaseKey)];
				if (!c.Traded())
					continue;
				keys.push_back(k);
				totals.push_back(c.Up + c.Down);
			}
		}
	};

	// What one bar added to one row: a session's history, from which the per-bar levels are
	// recomputed when a value-area input changes (no file reading).
	struct Delta
	{
		int		Bar		= 0;
		int64_t	Key		= 0;
		double	Up		= 0;
		double	Down	= 0;
	};

	// The levels from bar Bar on (until the next run).
	struct LevelRun
	{
		int		Bar	= 0;
		Levels	L;
	};

	// NinjaTrader's tick rule state (NT:513-514, NT:536-540), per session: the first trade is up,
	// a higher price up, a lower one down, an unchanged price keeps the direction. On tick
	// indices instead of raw doubles: identical for exchange prices, immune to float storage.
	struct TickRuleState
	{
		bool	HasLast		= false;
		int64_t	LastTick	= 0;
		bool	LastUp		= true;
	};

	// The engine inputs a session is built with (a change of Tick, TicksPerRow or Mode rebuilds;
	// Percent and AtLeast only recompute levels).
	struct ProfileConfig
	{
		double	Tick		= 0.25;
		int		TicksPerRow	= 1;
		int		Mode		= VD_TICK_RULE;
		double	Percent		= 68;
		bool	AtLeast		= false;
	};

	enum SessionSource { SRC_TRADES, SRC_VAP };

	// Why a session is not built from single trades (spec C.6).
	enum FallbackReason
	{
		FR_NONE,
		FR_STORAGE_UNIT,	// Intraday Data Storage Time Unit is not 1 Tick
		FR_BEFORE_FILE,		// before this chart's tick data file (continuous contract)
		FR_MULTI_TRADE,		// stored as N-second records, not ticks
		FR_PRICE_MISMATCH,	// trade prices do not match the chart's bars
		FR_TIME_BASE,		// cannot match the tick data to the chart
		FR_VOLUME_MISMATCH	// the trades do not add up to the chart's volume
	};

	// A session older than retention keeps only its per-bar levels (Compact). When its rows or
	// levels are needed again it is stale until it is read again (spec C.7): STALE_ROWS, it is
	// retained again (its levels are still right); STALE_LEVELS, a value-area input changed (its
	// levels are dropped too).
	enum StaleState { STALE_NONE, STALE_ROWS, STALE_LEVELS };

	// One trade for the engine (from a record, spec C.4): chart time, tick-snapped price.
	struct TradeInput
	{
		int64_t	Time		= 0;
		double	Price		= 0;
		double	Volume		= 0;
		double	BidVolume	= 0;
		double	AskVolume	= 0;
		int		Bar			= 0;
	};

	// One volume-at-price element of a bar (Sierra Chart's s_VolumeAtPriceV2).
	struct VapElement
	{
		int			PriceInTicks	= 0;
		uint32_t	Volume			= 0;
		uint32_t	BidVolume		= 0;
		uint32_t	AskVolume		= 0;
	};

	// One row of a snapshot.
	struct ProfileRow
	{
		int64_t	Key		= 0;
		double	Up		= 0;
		double	Down	= 0;
	};

	// What the drawing needs of a session (NinjaTrader's Snapshot, NT:498-504).
	struct VpSnapshot
	{
		bool					Valid		= false;
		std::vector<ProfileRow>	Rows;		// traded rows, ascending
		ProfileStats			Stats;
		int64_t					StartChart	= 0;
		int64_t					EndChart	= 0;
		int64_t					LastChart	= 0;
	};

	// Session versions come from one sequence: a session made again (a tail record taken back and
	// processed again, spec C.8) never repeats a version the drawing has a snapshot of.
	volatile LONG64 g_VersionSequence = 0;

	int64_t NextVersion()
	{
		return (int64_t)InterlockedIncrement64(&g_VersionSequence);
	}

	// What one Add changed, to take it back (spec C.8: the tail's records are provisional).
	struct SessionUndo
	{
		bool			Applied			= false;
		int64_t			Key				= 0;
		RowCell			PrevCell;
		int				PrevPresent		= 0;
		int64_t			PrevMinKey		= 0;
		int64_t			PrevMaxKey		= -1;
		size_t			PrevDeltaCount	= 0;
		bool			Merged			= false;
		uint32_t		MergedPos		= 0;
		Delta			PrevDelta;
		bool			PrevComplete	= true;
		size_t			PrevRunCount	= 0;
		int				PrevFirstBar	= -1;
		int				PrevCurBar		= -1;
		TickRuleState	PrevTickRule;
		int64_t			PrevLastChart	= 0;
	};

	// A session (NinjaTrader's Session, NT:506-631): one custom window with at least one counted
	// trade. Rows, the deltas per bar and row, the levels per bar, the tick rule state.
	struct VpSession
	{
		int					Date			= NO_DATE;	// the window's identity
		int64_t				StartChart		= 0;
		int64_t				EndChart		= 0;
		int64_t				LastChart		= 0;		// time of the last added trade (NT:549)
		ProfileConfig		Cfg;
		int					FirstBar		= -1;		// bar of its first trade
		int					CurBar			= -1;		// bar of its latest delta
		RowGrid				Rows;
		std::vector<Delta>	Deltas;
		bool				DeltasComplete	= true;		// false past the delta limit (MAX_DELTAS from ticks)
		std::vector<LevelRun> Runs;						// levels of bars before CurBar (all, once compacted)
		TickRuleState		TickRule;
		int64_t				Version			= NextVersion();	// a new one with every change
		int					Source			= SRC_TRADES;
		bool				NeedsVap		= false;	// the trades cannot build it: volume at price must
		int					Reason			= FR_NONE;
		bool				Compacted		= false;	// older than retention: only its per-bar levels are kept
		int					Stale			= STALE_NONE;	// to be read again (StaleState)
		// The first bar whose levels changed since ChangedFrom was last cleared (the per-bar
		// values written, spec C.8); INT_MIN: the whole session (made anew or replaced).
		int					ChangedFrom		= INT_MIN;

		mutable int64_t				CachedVersion	= -1;
		mutable bool				CachedValid		= false;
		mutable Levels				Cached;
		mutable std::vector<int64_t> ScratchKeys;
		mutable std::vector<double>	ScratchTotals;

		VpSession() = default;

		VpSession(const SessionWindow& w, const ProfileConfig& cfg)
			: Date(w.Date), StartChart(w.StartChart), EndChart(w.EndChart), Cfg(cfg)
		{
		}

		bool HasRows() const { return !Rows.Empty(); }

		// NinjaTrader's Session.Add (NT:528-551) on a trade of this session. False (nothing
		// changed) for a trade without volume or price, or one that would make the session span
		// more than MAX_SESSION_ROWS rows. Tick rule (NinjaTrader): all of the volume is up or
		// down. Bid/ask: the ask volume up, the bid volume down, the rest by the tick rule.
		bool Add(const TradeInput& t, SessionUndo* undo)
		{
			int64_t tickIndex = 0;
			if (!(t.Volume > 0) || !TickIndexOf(t.Price, Cfg.Tick, tickIndex))
				return false;
			const int64_t key = RowKeyOf(tickIndex, Cfg.TicksPerRow);
			if (!Rows.Fits(key))
				return false;
			bool up = TickRule.LastUp;
			if (TickRule.HasLast)
			{
				if (tickIndex > TickRule.LastTick)
					up = true;
				else if (tickIndex < TickRule.LastTick)
					up = false;
			}
			double upVolume, downVolume;
			if (Cfg.Mode == VD_BID_ASK)
			{
				const double ask	= (std::min)((std::max)(t.AskVolume, 0.0), t.Volume);
				const double bid	= (std::min)((std::max)(t.BidVolume, 0.0), t.Volume - ask);
				const double rest	= t.Volume - ask - bid;
				upVolume	= ask + (up ? rest : 0);
				downVolume	= bid + (up ? 0 : rest);
			}
			else
			{
				upVolume	= up ? t.Volume : 0;
				downVolume	= t.Volume - upVolume;
			}
			if (undo != nullptr)
			{
				undo->Applied		= true;
				undo->PrevTickRule	= TickRule;
				undo->PrevLastChart	= LastChart;
			}
			Accumulate(t.Bar, key, upVolume, downVolume, undo, MAX_DELTAS);
			TickRule.HasLast	= true;
			TickRule.LastTick	= tickIndex;
			TickRule.LastUp		= up;
			LastChart			= t.Time;
			return true;
		}

		// Takes back the Add that filled undo (the newest change of this session).
		void Undo(const SessionUndo& u)
		{
			if (!u.Applied)
				return;
			// The bars from the one the Add went to (with its first trade, the session's first bar)
			// get their levels back.
			ChangedFrom			= (std::min)(ChangedFrom, u.PrevCurBar >= 0 ? u.PrevCurBar : CurBar);
			Rows.Cell(u.Key)	= u.PrevCell;
			Rows.Present		= u.PrevPresent;
			Rows.MinKey			= u.PrevMinKey;
			Rows.MaxKey			= u.PrevMaxKey;
			if (u.Merged && u.MergedPos < Deltas.size())
				Deltas[u.MergedPos] = u.PrevDelta;
			if (Deltas.size() > u.PrevDeltaCount)
				Deltas.resize(u.PrevDeltaCount);
			DeltasComplete	= u.PrevComplete;
			if (Runs.size() > u.PrevRunCount)
				Runs.resize(u.PrevRunCount);
			FirstBar		= u.PrevFirstBar;
			CurBar			= u.PrevCurBar;
			TickRule		= u.PrevTickRule;
			LastChart		= u.PrevLastChart;
			Version = NextVersion();
		}

		// One bar's volume at price (spec C.5): the ask volume up, the bid volume down, volume
		// with neither side split evenly (bid and ask are clamped to the volume, so the row total
		// is the volume, as in every mode). PriceInTicks is the price in the chart's ticks (Sierra
		// Chart: price / sc.TickSize, with or without a Volume at Price Multiplier, which only
		// spaces the elements that many ticks apart). lastChart: the session's newest time so far.
		// Its deltas are all kept (g_MaxVapDeltas), so RemoveBarsFrom can always take it back.
		bool AddVapBar(int bar, const std::vector<VapElement>& elements, int64_t lastChart)
		{
			bool added = false;
			for (const VapElement& e : elements)
			{
				if (e.Volume == 0)
					continue;
				const int64_t key = RowKeyOf((int64_t)e.PriceInTicks, Cfg.TicksPerRow);
				if (!Rows.Fits(key))
					continue;
				const double volume	= (double)e.Volume;
				const double ask	= (std::min)((double)e.AskVolume, volume);
				const double bid	= (std::min)((double)e.BidVolume, volume - ask);
				const double rest	= volume - ask - bid;
				Accumulate(bar, key, ask + rest / 2, bid + rest / 2, nullptr, g_MaxVapDeltas);
				added = true;
			}
			if (added)
				LastChart = lastChart;
			return added;
		}

		// Removes the deltas of bars >= bar (a volume-at-price session's forming bar, before it
		// is added again with its current volume). False when the deltas are incomplete.
		bool RemoveBarsFrom(int bar)
		{
			if (!DeltasComplete)
				return false;
			ChangedFrom = (std::min)(ChangedFrom, bar);
			while (!Deltas.empty() && Deltas.back().Bar >= bar)
			{
				const Delta d = Deltas.back();
				Deltas.pop_back();
				RowCell& c = Rows.Cell(d.Key);
				const bool was = c.Traded();
				c.Up	-= d.Up;
				c.Down	-= d.Down;
				c.SlotBar = -1;
				if (was && !c.Traded())
					Rows.Present--;
			}
			CurBar = Deltas.empty() ? -1 : Deltas.back().Bar;
			if (Deltas.empty())
				FirstBar = -1;
			while (!Runs.empty() && Runs.back().Bar >= CurBar)
				Runs.pop_back();
			Version = NextVersion();
			return true;
		}

		// The levels of the rows as they are (NT's GetSnapshot Poc/Vah/Val). False without rows.
		bool CurrentLevels(Levels& out) const
		{
			if (CachedVersion != Version)
			{
				CachedVersion	= Version;
				CachedValid		= LevelsOf(Rows, Cached);
			}
			out = Cached;
			return CachedValid;
		}

		// The levels as of bar `bar`'s end (spec B.7): after every trade of this session up to it.
		// False before the session's first bar.
		bool LevelsAt(int bar, Levels& out) const
		{
			if (FirstBar < 0 || bar < FirstBar)
				return false;
			if (!Compacted && bar >= CurBar)
				return CurrentLevels(out);
			auto it = std::upper_bound(Runs.begin(), Runs.end(), bar, [](int b, const LevelRun& r) { return b < r.Bar; });
			if (it == Runs.begin())
				return false;
			out = (it - 1)->L;
			return true;
		}

		VpSnapshot Snapshot() const
		{
			VpSnapshot s;
			s.StartChart	= StartChart;
			s.EndChart		= EndChart;
			s.LastChart		= LastChart;
			Rows.Collect(ScratchKeys, ScratchTotals);
			if (ScratchKeys.empty())
				return s;
			s.Valid = true;
			s.Stats = ProfileOf(ScratchKeys, ScratchTotals, Cfg.Tick, Cfg.TicksPerRow, Cfg.Percent, Cfg.AtLeast);
			s.Rows.reserve(ScratchKeys.size());
			for (int64_t k : ScratchKeys)
			{
				const RowCell* c = Rows.Find(k);
				ProfileRow r;
				r.Key	= k;
				r.Up	= c->Up;
				r.Down	= c->Down;
				s.Rows.push_back(r);
			}
			return s;
		}

		// Recomputes the per-bar levels from the deltas (a value-area input change). False when
		// they are gone (compacted, or past MAX_DELTAS): the session must be read again.
		bool Replay()
		{
			if (Compacted || !DeltasComplete)
				return false;
			if (FirstBar >= 0)
				ChangedFrom = (std::min)(ChangedFrom, FirstBar);
			RowGrid grid;
			Runs.clear();
			int bar = -1;
			Levels l;
			for (const Delta& d : Deltas)
			{
				if (d.Bar != bar)
				{
					if (bar != -1 && LevelsOf(grid, l))
						Runs.push_back(LevelRun{bar, l});
					bar = d.Bar;
				}
				RowCell& c = grid.Cell(d.Key);
				if (!c.Traded())
					grid.Present++;
				c.Up	+= d.Up;
				c.Down	+= d.Down;
			}
			Version = NextVersion();
			return true;
		}

		// Older than retention: keep the per-bar levels, free the rows and deltas. No bar's levels
		// change (the last run is the levels the rows gave).
		void Compact()
		{
			if (Compacted)
				return;
			Levels l;
			if (FirstBar >= 0 && CurrentLevels(l))
				Runs.push_back(LevelRun{CurBar, l});
			Rows			= RowGrid();
			std::vector<Delta>().swap(Deltas);
			std::vector<int64_t>().swap(ScratchKeys);
			std::vector<double>().swap(ScratchTotals);
			DeltasComplete	= false;
			Compacted		= true;
			Version = NextVersion();
		}

		// Needed again after it lost its rows (spec C.7): kept as it is until it is read again.
		// dropLevels (a value-area input changed) drops its per-bar levels meanwhile, so its bars
		// show no value rather than the levels of the old inputs.
		void MarkStale(bool dropLevels)
		{
			Stale = (std::max)(Stale, dropLevels ? (int)STALE_LEVELS : (int)STALE_ROWS);
			if (!dropLevels)
				return;
			Runs.clear();
			if (FirstBar >= 0)
				ChangedFrom = (std::min)(ChangedFrom, FirstBar);
			Version = NextVersion();
		}

		// Stale and built from the file's records: its window is read again.
		bool ReadAgain() const { return Stale != STALE_NONE && Source == SRC_TRADES && !NeedsVap; }

		// To be built from volume at price: never built from it yet, or stale.
		bool WantsVap() const { return NeedsVap && (Source != SRC_VAP || Stale != STALE_NONE); }

	private:
		bool LevelsOf(const RowGrid& grid, Levels& out) const
		{
			grid.Collect(ScratchKeys, ScratchTotals);
			if (ScratchKeys.empty())
				return false;
			const ProfileStats p = ProfileOf(ScratchKeys, ScratchTotals, Cfg.Tick, Cfg.TicksPerRow, Cfg.Percent, Cfg.AtLeast);
			out.Poc	= p.Poc;
			out.Vah	= p.Vah;
			out.Val	= p.Val;
			return true;
		}

		// Adds volume to a row as bar `bar`'s. A bar after the current one first freezes the
		// current bar's levels (a run). Bars never go back within a session (records are in time
		// order); an older bar counts as the current one. Past maxDeltas the deltas are incomplete.
		void Accumulate(int bar, int64_t key, double upVolume, double downVolume, SessionUndo* undo, size_t maxDeltas)
		{
			if (undo != nullptr)
			{
				undo->Key				= key;
				undo->PrevPresent		= Rows.Present;
				undo->PrevMinKey		= Rows.MinKey;
				undo->PrevMaxKey		= Rows.MaxKey;
				undo->PrevDeltaCount	= Deltas.size();
				undo->PrevComplete		= DeltasComplete;
				undo->PrevRunCount		= Runs.size();
				undo->PrevFirstBar		= FirstBar;
				undo->PrevCurBar		= CurBar;
				undo->Merged			= false;
			}
			if (CurBar >= 0 && bar > CurBar)
			{
				Levels l;
				if (CurrentLevels(l))
					Runs.push_back(LevelRun{CurBar, l});
			}
			if (bar < CurBar)
				bar = CurBar;
			if (FirstBar < 0)
				FirstBar = bar;
			CurBar		= bar;
			ChangedFrom	= (std::min)(ChangedFrom, bar);	// the bars before keep their levels (runs)

			RowCell& c = Rows.Cell(key);
			if (undo != nullptr)
				undo->PrevCell = c;
			if (!c.Traded())
				Rows.Present++;
			c.Up	+= upVolume;
			c.Down	+= downVolume;
			if (!c.Traded())
				Rows.Present--;	// nothing was added after all

			if (DeltasComplete)
			{
				if (c.SlotBar == bar && c.SlotPos < Deltas.size())
				{
					Delta& d = Deltas[c.SlotPos];
					if (undo != nullptr)
					{
						undo->Merged	= true;
						undo->MergedPos	= c.SlotPos;
						undo->PrevDelta	= d;
					}
					d.Up	+= upVolume;
					d.Down	+= downVolume;
				}
				else if (Deltas.size() < maxDeltas)
				{
					Delta d;
					d.Bar	= bar;
					d.Key	= key;
					d.Up	= upVolume;
					d.Down	= downVolume;
					Deltas.push_back(d);
					c.SlotBar	= bar;
					c.SlotPos	= (uint32_t)(Deltas.size() - 1);
				}
				else
					DeltasComplete = false;
			}
			Version = NextVersion();
		}
	};

	// ---- Records (spec C.4) ----

	enum RecordOutcome
	{
		RO_NO_TRADE,	// no volume (a bid/ask update, NT:181)
		RO_OUTSIDE,		// in no session window
		RO_MULTI,		// several trades in one record: the window cannot be built from ticks
		RO_UNCOVERED,	// in no chart bar (outside the Session Times)
		RO_MISMATCH,	// the price is outside its bar's range (back-adjusted or multiplied prices)
		RO_TRADE
	};

	// Turns intraday file records into trades: chart time, window, bar and price checks.
	struct RecordMapper
	{
		const WindowTable*	Windows	= nullptr;
		const BarTable*		Bars	= nullptr;
		const OffsetTable*	Offsets	= nullptr;	// with TB_UTC
		int					Base	= TB_CHART;
		double				Tick	= 0.25;

		mutable int		BarHint		= -1;
		mutable int		WindowHint	= -1;
		mutable size_t	OffsetHint	= 0;

		int64_t ChartTime(const s_IntradayRecord& r) const
		{
			const int64_t t = r.DateTime.AsMicrosecondsSinceBaseDate();
			return Base == TB_UTC && Offsets != nullptr ? Offsets->ToChart(t, OffsetHint) : t;
		}

		RecordOutcome Map(const s_IntradayRecord& r, TradeInput& trade, int& window) const
		{
			window = -1;
			if (r.TotalVolume == 0)
				return RO_NO_TRADE;
			const int64_t t = ChartTime(r);
			window = Windows->Find(t, WindowHint);
			if (window < 0)
				return RO_OUTSIDE;
			if (r.NumTrades > 1)
				return RO_MULTI;
			const int bar = Bars->BarOf(t, BarHint);
			if (!Bars->Covers(bar, t))
				return RO_UNCOVERED;
			// The price must be in its bar's range. A trade sharing its time with a tick, volume or
			// range bar's first trade may be the previous bar's last one (time cannot split them):
			// that bar's range counts too.
			const double price = SnapToTick((double)r.Close, Tick);
			if (!InRange(price, bar) && !(bar > 0 && t == Bars->S[(size_t)bar] && InRange(price, bar - 1)))
				return RO_MISMATCH;
			trade.Time		= t;
			trade.Price		= price;
			trade.Volume	= (double)r.TotalVolume;
			trade.BidVolume	= (double)r.BidVolume;
			trade.AskVolume	= (double)r.AskVolume;
			trade.Bar		= bar;
			return RO_TRADE;
		}

		bool InRange(double price, int bar) const
		{
			return price >= Bars->Low[(size_t)bar] - Tick / 2 && price <= Bars->High[(size_t)bar] + Tick / 2;
		}
	};

	// Reads intraday file records by index. Sierra Chart: ReadIntradayFileRecordAtIndex with its
	// lock held for one study call; tests: a vector.
	struct RecordReader
	{
		virtual bool Read(int64_t index, s_IntradayRecord& record) = 0;

	protected:
		~RecordReader() = default;
	};

	bool SameRecord(const s_IntradayRecord& a, const s_IntradayRecord& b)
	{
		return a.DateTime.AsMicrosecondsSinceBaseDate() == b.DateTime.AsMicrosecondsSinceBaseDate() && a.Open == b.Open && a.High == b.High
			&& a.Low == b.Low && a.Close == b.Close && a.NumTrades == b.NumTrades && a.TotalVolume == b.TotalVolume
			&& a.BidVolume == b.BidVolume && a.AskVolume == b.AskVolume;
	}

	int64_t StoredTime(const s_IntradayRecord& r)
	{
		return r.DateTime.AsMicrosecondsSinceBaseDate();
	}

	// The records stamped (as stored) in [a, b): indices [Lo, Hi), by two binary searches.
	struct RecordSpan
	{
		int64_t	Lo	= 0;
		int64_t	Hi	= 0;
	};

	RecordSpan SpanOf(RecordReader& reader, int64_t last, int64_t a, int64_t b)
	{
		auto timeAt = [&reader](int64_t k)
		{
			s_IntradayRecord r;
			return reader.Read(k, r) ? StoredTime(r) : INT64_MAX;
		};
		RecordSpan span;
		span.Lo = FirstRecordAtOrAfter(0, last, a, timeAt);
		span.Hi = FirstRecordAtOrAfter(span.Lo, last, b, timeAt);
		return span;
	}

	// How many of a completed bar's open and close the records of its span reproduce: the first
	// and last trade's price. 0 when no trade is there. A few reads.
	int PriceEvidence(RecordReader& reader, const RecordSpan& span, const BarTable& bars, int i, double tick)
	{
		int matches = 0;
		s_IntradayRecord r;
		for (int64_t k = span.Lo; k < span.Hi && k < span.Lo + 64; k++)
			if (reader.Read(k, r) && r.TotalVolume > 0)
			{
				matches += SnapToTick((double)r.Close, tick) == bars.Open[(size_t)i];
				break;
			}
		for (int64_t k = span.Hi - 1; k >= span.Lo && k > span.Hi - 1 - 64; k--)
			if (reader.Read(k, r) && r.TotalVolume > 0)
			{
				matches += SnapToTick((double)r.Close, tick) == bars.Close[(size_t)i];
				break;
			}
		return matches;
	}

	// 1 when the records of a completed bar's span add up to its volume. Not tried past
	// EVIDENCE_MAX_RECORDS records (0).
	int VolumeEvidence(RecordReader& reader, const RecordSpan& span, const BarTable& bars, int i)
	{
		if (!(span.Hi > span.Lo && span.Hi - span.Lo <= EVIDENCE_MAX_RECORDS))
			return 0;
		double volume = 0;
		s_IntradayRecord r;
		for (int64_t k = span.Lo; k < span.Hi; k++)
			if (reader.Read(k, r))
				volume += (double)r.TotalVolume;
		return volume == bars.Volume[(size_t)i] ? 1 : 0;
	}

	// The completed bars that can tell the two time bases apart: non-empty, with volume, at a
	// time when the chart's time zone is not at UTC+0, newest first. When it is at UTC+0 now (as
	// London in winter), the newest bars before that (assuming one change in the loaded bars).
	template <typename ChartToUtc>
	std::vector<int> EvidenceBars(const BarTable& bars, ChartToUtc toUtc)
	{
		std::vector<int> out;
		const int lastDone = bars.Count() - 2;	// the last bar may still be forming
		if (lastDone < 0)
			return out;
		auto offset = [&bars, &toUtc](int i) { return (int64_t)toUtc(bars.S[(size_t)i]) != bars.S[(size_t)i]; };
		int from = lastDone;
		if (!offset(from))
		{
			if (!offset(0))
				return out;		// UTC+0 over the whole chart: both time bases read the same times
			int lo = 0, hi = lastDone;	// offset at lo, none at hi
			while (hi - lo > 1)
			{
				const int mid = lo + (hi - lo) / 2;
				(offset(mid) ? lo : hi) = mid;
			}
			from = lo;
		}
		for (int i = from; i >= 0 && from - i < 256 && (int)out.size() < EVIDENCE_BARS; i--)
			if (bars.C[(size_t)i] > bars.S[(size_t)i] && bars.HasTrades(i) && bars.Volume[(size_t)i] > 0 && offset(i))
				out.push_back(i);
		return out;
	}

	// The records' time base (spec C.4 step 1): the newest trade at or before `last` must fall in
	// one of the chart's last non-empty bars, as it is (chart time) or converted from UTC. When it
	// fits both ways, completed bars decide: under the right time base the records inside a bar's
	// time span start at its open and end at its close; when that cannot tell (a flat market),
	// they add up to its volume (bars of up to EVIDENCE_MAX_RECORDS records). Equal evidence (or
	// none: a chart at UTC+0 throughout, where both read the same times) means chart time. The
	// reads: a few dozen per evidence bar and time base, at most EVIDENCE_MAX_RECORDS more on a tie.
	template <typename UtcToChart, typename ChartToUtc>
	int CalibrateRecords(RecordReader& reader, int64_t last, const BarTable& bars, double tick, UtcToChart toChart, ChartToUtc toUtc)
	{
		if (last < 0 || bars.Count() == 0)
			return TB_UNKNOWN;
		int64_t t = 0;
		bool found = false;
		for (int64_t i = last; i >= 0 && i > last - 256 && !found; i--)
		{
			s_IntradayRecord r;
			if (!reader.Read(i, r))
				break;
			if (r.TotalVolume > 0)
			{
				t		= StoredTime(r);
				found	= true;
			}
		}
		if (!found)
			return TB_UNKNOWN;
		std::vector<std::pair<int64_t, int64_t>> spans;
		for (int i = bars.Count() - 1; i >= 0 && spans.size() < 4; i--)
			if (bars.C[(size_t)i] > bars.S[(size_t)i])
				spans.push_back({bars.S[(size_t)i], bars.C[(size_t)i]});
		const int fit = CalibrateTimeBase(t, spans, toChart);
		if (fit != TB_EITHER)
			return fit;
		const std::vector<int> evidence = EvidenceBars(bars, toUtc);
		std::vector<RecordSpan> asIsSpans, fromUtcSpans;
		int asIs = 0, fromUtc = 0;
		for (int i : evidence)
		{
			asIsSpans.push_back(SpanOf(reader, last, bars.S[(size_t)i], bars.C[(size_t)i]));
			fromUtcSpans.push_back(SpanOf(reader, last, (int64_t)toUtc(bars.S[(size_t)i]), (int64_t)toUtc(bars.C[(size_t)i])));
			asIs	+= PriceEvidence(reader, asIsSpans.back(), bars, i, tick);
			fromUtc	+= PriceEvidence(reader, fromUtcSpans.back(), bars, i, tick);
		}
		if (asIs == fromUtc)
			for (size_t k = 0; k < evidence.size(); k++)
			{
				asIs	+= VolumeEvidence(reader, asIsSpans[k], bars, evidence[k]);
				fromUtc	+= VolumeEvidence(reader, fromUtcSpans[k], bars, evidence[k]);
			}
		return fromUtc > asIs ? TB_UTC : TB_CHART;
	}

	// What processing one record of the provisional tail changed (spec C.8).
	struct EngineUndo
	{
		bool					Valid	= false;
		int						Date	= NO_DATE;
		bool					Created	= false;	// it created the session
		SessionUndo				Add;
		std::vector<VpSession>	Before;				// the session before the record sent it to volume at price (rare)
	};

	// Volume at price by bar (spec C.5). Sierra Chart: sc.VolumeAtPriceForBars; tests: vectors.
	struct VapSource
	{
		// The bars whose volume at price is built (Sierra Chart: GetNumberOfBars()).
		virtual int BarCount() = 0;
		// Bar `bar`'s elements, ascending by price. False when it has none.
		virtual bool Elements(int bar, std::vector<VapElement>& out) = 0;

	protected:
		~VapSource() = default;
	};

	enum VapStatus
	{
		VS_DONE,
		VS_WAITING		// the volume at price is not built for every bar yet: try again on a later call
	};

	// When a volume-at-price bar's trades end (spec C.5): its covered end, within the window; the
	// forming bar's newest trade (the file's last record) when known.
	int64_t VapBarTime(const BarTable& bars, int i, const SessionWindow& w, int64_t formingLast)
	{
		const int64_t end = (std::min)(bars.C[(size_t)i], w.EndChart);
		return i == bars.Count() - 1 && formingLast > 0 ? (std::min)(formingLast, end) : end;
	}

	// The order history is read in (spec C.7). The newest window that has begun by the file's
	// last record goes through the live path (it may still be forming), from its first record.
	// The older windows are read on their own, newest first, so the developing and the retained
	// sessions appear first and those older than retention (per-bar values only) last; sessions
	// are independent, so the order cannot change them. Windows no chart bar overlaps are left
	// out: none of their trades can count (spec A #20). A window that starts before the file's
	// first record (fileStart; a continuous contract stitched from older files) cannot be read
	// whole: it is built from volume at price instead.
	struct LoadPlan
	{
		int					Stream				= -1;		// window index for the live path; -1: no windows
		bool				StreamBeforeFile	= false;
		std::vector<int>	History;						// newest first, read from the file
		std::vector<int>	BeforeFile;						// newest first, from volume at price
	};

	LoadPlan PlanLoad(const WindowTable& windows, const BarTable& bars, int64_t lastRecordTime, int64_t fileStart)
	{
		LoadPlan plan;
		const std::vector<SessionWindow>& w = windows.Windows;
		if (w.empty())
			return plan;
		const int newest = (int)(std::upper_bound(w.begin(), w.end(), lastRecordTime,
			[](int64_t value, const SessionWindow& x) { return value < x.StartChart; }) - w.begin()) - 1;
		plan.Stream				= (std::max)(0, newest);
		plan.StreamBeforeFile	= w[(size_t)plan.Stream].StartChart < fileStart;
		for (int k = newest - 1; k >= 0; k--)
		{
			if (!bars.Overlaps(w[(size_t)k].StartChart, w[(size_t)k].EndChart))
				continue;
			(w[(size_t)k].StartChart < fileStart ? plan.BeforeFile : plan.History).push_back(k);
		}
		return plan;
	}

	// A window read on its own from history (spec C.7): records [Next, Hi).
	struct WindowBuild
	{
		int			Window	= -1;	// index in the window table
		int64_t		Next	= 0;
		int64_t		Hi		= 0;
		VpSession	Session;
		bool		Done	= false;
		double		Counted	= 0;	// the volume of its trades in the bars inside the window
	};

	enum StreamStatus { SS_CAUGHT_UP, SS_PENDING, SS_REBUILD };

	// The sessions and the live record cursor (NT's sessions list, currentSession, TickCounter).
	struct VpEngine
	{
		ProfileConfig				Cfg;
		int							Retain			= 20;
		std::map<int, VpSession>	Sessions;		// by window date, oldest first

		// Live cursor (spec C.8): the last record processed. The records from TailStart on (the
		// tail) share the time the file's last record had when they were read: a tick, volume or
		// range bar that opens later at that time takes them (spec B.3), and the last record can
		// still grow (1-second storage merges trades into it). So they were processed with undo
		// records, and the next call that brings new records, or finds the last one changed,
		// takes them back and processes them again; every other record is counted once.
		int64_t					CursorIndex		= -1;
		bool					CursorKnown		= false;	// CursorRecord holds the record at CursorIndex
		s_IntradayRecord		CursorRecord;
		int64_t					TailStart		= -1;		// -1: no tail yet (the cursor is before it)
		int64_t					LastSeen		= -1;		// the file's last record at the latest call (the tail read up to it)
		std::vector<EngineUndo>	Tail;						// one per tail record, in file order

		VpEngine() = default;
		VpEngine(const ProfileConfig& cfg, int retain) : Cfg(cfg), Retain((std::max)(1, retain)) {}

		const VpSession* Newest() const { return Sessions.empty() ? nullptr : &Sessions.rbegin()->second; }

		// The session a live record of window w goes to (NT:189-200): the newest session, a new
		// one for a newer window; an older window is regressing data and dropped (nullptr).
		VpSession* Target(const SessionWindow& w, EngineUndo* undo)
		{
			if (!Sessions.empty())
			{
				const int newest = Sessions.rbegin()->first;
				if (w.Date < newest)
					return nullptr;
				if (w.Date == newest)
					return &Sessions.rbegin()->second;
			}
			VpSession& s = Sessions[w.Date];
			s = VpSession(w, Cfg);
			if (undo != nullptr)
				undo->Created = true;
			return &s;
		}

		// One record through the live path.
		RecordOutcome Process(const s_IntradayRecord& r, const RecordMapper& mapper, EngineUndo* undo)
		{
			TradeInput trade;
			int window = -1;
			const RecordOutcome outcome = mapper.Map(r, trade, window);
			if (outcome != RO_TRADE && outcome != RO_MULTI && outcome != RO_MISMATCH)
				return outcome;
			const SessionWindow& w = mapper.Windows->Windows[(size_t)window];
			if (undo != nullptr)
			{
				*undo		= EngineUndo();
				undo->Date	= w.Date;
			}
			VpSession* s = Target(w, undo);
			if (s == nullptr)
				return outcome;
			if (undo != nullptr)
				undo->Valid = true;
			if (s->NeedsVap)
				return outcome;		// built from volume at price: its trades do not count
			if (outcome == RO_TRADE)
				s->Add(trade, undo != nullptr ? &undo->Add : nullptr);
			else
			{
				if (undo != nullptr && !undo->Created)
					undo->Before.assign(1, *s);
				MarkVap(*s, outcome == RO_MULTI ? FR_MULTI_TRADE : FR_PRICE_MISMATCH);
			}
			return outcome;
		}

		// The session cannot be built from single trades (spec C.6). Its trades so far are
		// dropped, so a partial profile never shows: it has no rows and no levels until it is
		// built from volume at price (BuildFromVap).
		static void MarkVap(VpSession& s, int reason)
		{
			SessionWindow w;
			w.Date			= s.Date;
			w.StartChart	= s.StartChart;
			w.EndChart		= s.EndChart;
			s			= VpSession(w, s.Cfg);		// a new version, every bar changed
			s.NeedsVap	= true;
			s.Reason	= reason;
		}

		// A window known not to be readable from the file (before it, spec C.4 step 3): its
		// session waits for volume at price, and the live path leaves its trades alone.
		void MarkWindowVap(const SessionWindow& w, int reason)
		{
			auto it = Sessions.find(w.Date);
			if (it == Sessions.end())
				it = Sessions.emplace(w.Date, VpSession(w, Cfg)).first;
			if (!it->second.NeedsVap)
				MarkVap(it->second, reason);
		}

		void Undo(EngineUndo& u)
		{
			if (!u.Valid)
				return;
			auto it = Sessions.find(u.Date);
			if (it == Sessions.end())
				return;
			if (u.Created)
				Sessions.erase(it);
			else if (!u.Before.empty())
			{
				it->second				= std::move(u.Before[0]);
				it->second.Version		= NextVersion();
				it->second.ChangedFrom	= INT_MIN;
			}
			else
				it->second.Undo(u.Add);
		}

		// Takes the tail back, its newest record first.
		void UndoTail()
		{
			for (auto it = Tail.rbegin(); it != Tail.rend(); ++it)
				Undo(*it);
			Tail.clear();
			TailStart = -1;
		}

		// Whether a tail record made a session (it may go away with it).
		bool TailCreated() const
		{
			return std::any_of(Tail.begin(), Tail.end(), [](const EngineUndo& u) { return u.Valid && u.Created; });
		}

		// Starts the live path at record `from` (the newest window's first record).
		void StartStream(int64_t from)
		{
			CursorIndex	= from - 1;
			CursorKnown	= false;
			TailStart	= -1;
			LastSeen	= -1;
			Tail.clear();
		}

		// Processes the records after the cursor up to `last` (sc.FileRecordIndexOfLastDataRecordInChart),
		// at most maxRecords of them. Each record is counted once, but for the tail (see the
		// cursor), which is taken back and processed again when new records arrive. The records
		// between session windows are skipped with a binary search: none of them can count.
		// SS_REBUILD when the file no longer matches what was read (rewritten, backfilled, shrunk).
		StreamStatus Stream(RecordReader& reader, const RecordMapper& mapper, int64_t last, int64_t maxRecords)
		{
			int64_t start = CursorIndex + 1;
			if (CursorKnown)
			{
				if (last < CursorIndex || last < LastSeen)
					return SS_REBUILD;	// the file shrank
				s_IntradayRecord r;
				if (!reader.Read(CursorIndex, r))
					return SS_REBUILD;
				if (TailStart >= 0)
				{
					// The tail's newest record may have grown; any other change, or less volume,
					// means the file was rewritten.
					if (StoredTime(r) != StoredTime(CursorRecord) || r.TotalVolume < CursorRecord.TotalVolume)
						return SS_REBUILD;
					if (last != LastSeen || !SameRecord(r, CursorRecord))
					{
						start = TailStart;
						UndoTail();
					}
					else if (CursorIndex >= last)
						return SS_CAUGHT_UP;	// nothing new: the tail stands
				}
				else if (!SameRecord(r, CursorRecord))
					return SS_REBUILD;
			}
			if (start > last)
				return SS_CAUGHT_UP;
			s_IntradayRecord newest;
			if (!reader.Read(last, newest))
				return SS_REBUILD;
			const int64_t tailTime = StoredTime(newest);
			const int64_t end = last - start + 1 > maxRecords ? start + (std::max)((int64_t)1, maxRecords) - 1 : last;
			auto chartAt = [&reader, &mapper](int64_t k)
			{
				s_IntradayRecord x;
				return reader.Read(k, x) ? mapper.ChartTime(x) : INT64_MAX;
			};
			for (int64_t i = start; i <= end; i++)
			{
				s_IntradayRecord r;
				if (!reader.Read(i, r))
					return SS_REBUILD;
				// Once the tail begins every later record is in it, so the undo records are
				// always taken back in the reverse of the order they were made.
				const bool tail = TailStart >= 0 || StoredTime(r) >= tailTime;
				EngineUndo* undo = nullptr;
				if (tail)
				{
					if (TailStart < 0)
						TailStart = i;
					Tail.emplace_back();
					undo = &Tail.back();
				}
				const RecordOutcome outcome = Process(r, mapper, undo);
				CursorIndex		= i;
				CursorRecord	= r;
				CursorKnown		= true;
				if (outcome != RO_OUTSIDE || tail || last - i <= SKIP_MIN_RECORDS)
					continue;
				// Outside every window: on to the first record of the next one (past this call's
				// share too: nothing between is processed).
				const int64_t next	= mapper.Windows->NextStart(mapper.ChartTime(r));
				const int64_t to	= FirstRecordAtOrAfter(i + 1, last, next, chartAt) - 1;
				if (to <= i)
					continue;
				s_IntradayRecord x;
				if (!reader.Read(to, x))
					return SS_REBUILD;
				i				= to;
				CursorIndex		= to;
				CursorRecord	= x;
				if (StoredTime(x) >= tailTime)
				{
					TailStart = to;		// outside every window: nothing to take back
					Tail.emplace_back();
				}
			}
			LastSeen = last;
			ApplyRetention();
			return CursorIndex >= last ? SS_CAUGHT_UP : SS_PENDING;
		}

		// Reads up to maxRecords more of a history window into its own session (sessions are
		// independent, each with a fresh tick rule state, so the order windows are read in cannot
		// change them). True when the window is done; then Insert it.
		static bool RunBuild(WindowBuild& b, RecordReader& reader, const RecordMapper& mapper, int64_t maxRecords)
		{
			const SessionWindow& w = mapper.Windows->Windows[(size_t)b.Window];
			if (b.Session.Date != w.Date)
				b.Session = VpSession(w, b.Session.Cfg);
			const BarTable& bars	= *mapper.Bars;
			const int insideFirst	= (int)(std::lower_bound(bars.S.begin(), bars.S.end(), w.StartChart) - bars.S.begin());
			const int insideLast	= (int)(std::upper_bound(bars.C.begin(), bars.C.end(), w.EndChart) - bars.C.begin()) - 1;
			int64_t budget = (std::max)((int64_t)1, maxRecords);
			while (!b.Done && b.Next < b.Hi && budget-- > 0)
			{
				s_IntradayRecord r;
				if (!reader.Read(b.Next++, r))
				{
					b.Done = true;
					break;
				}
				TradeInput trade;
				int window = -1;
				const RecordOutcome outcome = mapper.Map(r, trade, window);
				if (window != b.Window)
					continue;
				if (outcome == RO_TRADE)
				{
					b.Session.Add(trade, nullptr);
					if (trade.Bar >= insideFirst && trade.Bar <= insideLast)
						b.Counted += trade.Volume;
				}
				else if (outcome == RO_MULTI || outcome == RO_MISMATCH)
				{
					MarkVap(b.Session, outcome == RO_MULTI ? FR_MULTI_TRADE : FR_PRICE_MISMATCH);
					b.Done = true;
				}
			}
			if (b.Next >= b.Hi)
				b.Done = true;
			// The trades must add up to the chart's volume of the bars inside the window (spec C.4
			// step 4). On a continuous contract the chart's older bars come from an older
			// contract's file, while these records are this contract's from when it was the next
			// month: back-adjusted, their prices can pass the bars' range check.
			if (b.Done && !b.Session.NeedsVap && insideLast >= insideFirst && bars.HasTrades(insideLast))
			{
				double expected = 0;
				for (int i = insideFirst; i <= insideLast; i++)
					expected += bars.Volume[(size_t)i];
				if (std::fabs(b.Counted - expected) > VOLUME_TOLERANCE * expected)
					MarkVap(b.Session, FR_VOLUME_MISMATCH);
			}
			return b.Done;
		}

		// A finished history window joins the sessions if it got trades (or needs volume at
		// price): as a new session, or read again in place of its stale one; never in place of
		// one the live path made.
		bool Insert(WindowBuild& b)
		{
			if (!b.Done)
				return false;
			const int date		= b.Session.Date;
			const auto it		= Sessions.find(date);
			const bool replace	= it != Sessions.end() && it->second.Stale != STALE_NONE;
			if (it != Sessions.end() && !replace)
				return false;
			if (!b.Session.HasRows() && !b.Session.NeedsVap)
			{
				if (replace)
					Sessions.erase(it);		// its trades are gone (the file changed)
				return false;
			}
			if (replace)
				it->second = std::move(b.Session);
			else
				Sessions.emplace(date, std::move(b.Session));
			b.Session = VpSession();
			ApplyRetention();
			return true;
		}

		// Builds window w's session from volume at price (spec C.5, C.6): every bar that starts
		// in the window (Sierra Chart's own Volume by Price period rule; exact for bars that
		// divide the window). It replaces the session waiting since MarkVap or stale (even with no
		// volume yet: later bars join it through UpdateVap) and keeps `reason`; without such a
		// session, one is made only when the bars hold volume. formingLast: the time of the file's
		// last record, 0 if unknown.
		VapStatus BuildFromVap(const SessionWindow& w, const BarTable& bars, VapSource& src, int64_t formingLast, int reason)
		{
			if (src.BarCount() < bars.Count())
				return VS_WAITING;
			VpSession s(w, Cfg);
			s.Source	= SRC_VAP;
			s.NeedsVap	= true;
			s.Reason	= reason;
			std::vector<VapElement> elements;
			for (int i = (int)(std::lower_bound(bars.S.begin(), bars.S.end(), w.StartChart) - bars.S.begin());
				i < bars.Count() && bars.S[(size_t)i] < w.EndChart; i++)
			{
				if (src.Elements(i, elements))
					s.AddVapBar(i, elements, VapBarTime(bars, i, w, formingLast));
			}
			auto it = Sessions.find(w.Date);
			if (it != Sessions.end())
				it->second = std::move(s);
			else if (s.HasRows())
				Sessions.emplace(w.Date, std::move(s));
			ApplyRetention();
			return VS_DONE;
		}

		// Volume at price from bar `from` on (spec C.5, C.8), called with the first bar that
		// changed (the forming one live, 0 on a full build). allWindows (the Volume at price
		// option, or every session falling back): each bar goes to the session of the window
		// holding its start, made when it has volume (`reason` says why it is not from trades).
		// Otherwise only the sessions already built from volume at price take their new bars (a
		// fallback window still forming). Bars added before are taken out first and added again
		// with their current volume (TatankaTpoProfile's live-bar checkpoint, by the deltas such a
		// session always keeps), so each bar counts once; a session whose bars cannot be taken
		// back all the same is built again from volume at price on its own (never the whole
		// engine). `fresh`: the windows (dates) built from volume at price earlier in this call,
		// through the last bar: left as they are. Sessions older than retention are left as they
		// are: their bars were complete when newer sessions pushed them out (a bar shared with the
		// next session's first trade shows that session's levels).
		VapStatus UpdateVap(const WindowTable& windows, const BarTable& bars, VapSource& src, int from, int64_t formingLast, bool allWindows,
			int reason, const std::vector<int>& fresh = std::vector<int>())
		{
			if (src.BarCount() < bars.Count())
				return VS_WAITING;
			from = (std::max)(0, from);
			std::vector<int> skip = fresh;
			auto skipped = [&skip](int date) { return std::find(skip.begin(), skip.end(), date) != skip.end(); };
			std::vector<int> again;
			for (auto it = Sessions.begin(); it != Sessions.end();)
			{
				VpSession& s = it->second;
				if (s.Source != SRC_VAP || s.Compacted || s.CurBar < from || skipped(it->first))
				{
					++it;
					continue;
				}
				if (allWindows && s.FirstBar >= from)
				{
					it = Sessions.erase(it);
					continue;
				}
				if (!s.RemoveBarsFrom(from))
					again.push_back(it->first);
				++it;
			}
			for (int date : again)
			{
				if (const SessionWindow* w = windows.ByDate(date))
					BuildFromVap(*w, bars, src, formingLast, Sessions[date].Reason);
				else
					Sessions.erase(date);	// no window to build it from: its bars must not count twice
				skip.push_back(date);
			}
			std::vector<VapElement> elements;
			int hint = -1;
			for (int i = from; i < bars.Count(); i++)
			{
				const int k = windows.Find(bars.S[(size_t)i], hint);
				if (k < 0)
					continue;
				const SessionWindow& w = windows.Windows[(size_t)k];
				if (skipped(w.Date))
					continue;
				auto it = Sessions.find(w.Date);
				if (it == Sessions.end() ? !allWindows : it->second.Source != SRC_VAP || it->second.Compacted)
					continue;
				if (!src.Elements(i, elements))
					continue;
				const int64_t time = VapBarTime(bars, i, w, formingLast);
				if (it != Sessions.end())
				{
					it->second.AddVapBar(i, elements, time);
					continue;
				}
				VpSession s(w, Cfg);
				s.Source	= SRC_VAP;
				s.NeedsVap	= true;
				s.Reason	= reason;
				if (s.AddVapBar(i, elements, time))
					Sessions.emplace(w.Date, std::move(s));
			}
			ApplyRetention();
			return VS_DONE;
		}

		// The retained sessions not built from trades (spec B.8, C.6): built from volume at price
		// in place of trades (the chart label's "not from ticks"; the Volume at price option is
		// the user's choice, not counted), and those still waiting for it.
		struct SourceCounts
		{
			int	Approximate	= 0;
			int	Waiting		= 0;
		};

		SourceCounts Counts() const
		{
			SourceCounts c;
			for (const VpSession* s : Retained())
			{
				if (s->Source == SRC_VAP && s->Reason != FR_NONE)
					c.Approximate++;
				else if (s->NeedsVap && s->Source != SRC_VAP)
					c.Waiting++;
			}
			return c;
		}

		// Sessions older than the newest Retain keep only their per-bar levels (spec B.6). One
		// more is kept whole while the newest was made by a tail record (it may go away).
		void ApplyRetention()
		{
			const int keep = Retain + (TailCreated() ? 1 : 0);
			int seen = 0;
			for (auto it = Sessions.rbegin(); it != Sessions.rend(); ++it)
				if (++seen > keep)
				{
					VpSession& s = it->second;
					if (s.Stale == STALE_ROWS)
						s.Stale = STALE_NONE;	// not retained after all: its levels are all it needs
					s.Compact();
				}
		}

		// NinjaTrader's sessions list (NT:199): the newest Retain sessions, oldest first.
		std::vector<const VpSession*> Retained() const
		{
			std::vector<const VpSession*> out;
			int seen = 0;
			for (auto it = Sessions.rbegin(); it != Sessions.rend() && seen < Retain; ++it, ++seen)
				out.push_back(&it->second);
			std::reverse(out.begin(), out.end());
			return out;
		}

		// The plotted levels of bar `bar` (spec B.7): the newest session whose first trade is in or
		// before it, as of the bar's end. False before any session (no value).
		bool LevelsAt(int bar, Levels& out) const
		{
			for (auto it = Sessions.rbegin(); it != Sessions.rend(); ++it)
			{
				const VpSession& s = it->second;
				if (s.FirstBar >= 0 && s.FirstBar <= bar)
					return s.LevelsAt(bar, out);
			}
			return false;
		}

		// A value-area input change (spec C.7): levels recomputed from the deltas. Returns the
		// dates of the sessions without them (compacted, or past MAX_DELTAS), to be read again.
		std::vector<int> SetValueArea(double percent, bool atLeast)
		{
			std::vector<int> reread;
			Cfg.Percent = percent;
			Cfg.AtLeast = atLeast;
			for (auto& entry : Sessions)
			{
				VpSession& s = entry.second;
				s.Cfg.Percent = percent;
				s.Cfg.AtLeast = atLeast;
				s.Version = NextVersion();
				if (s.FirstBar >= 0 && !s.Replay())
					reread.push_back(entry.first);
			}
			return reread;
		}

		// The compacted sessions among the newest `retain`: a larger retention needs their rows.
		std::vector<int> CompactedWithin(int retain) const
		{
			std::vector<int> out;
			int seen = 0;
			for (auto it = Sessions.rbegin(); it != Sessions.rend() && seen < retain; ++it, ++seen)
				if (it->second.Compacted)
					out.push_back(it->first);
			return out;
		}

		// The per-bar values were written: no session has changed since.
		void ClearChanges()
		{
			for (auto& e : Sessions)
				e.second.ChangedFrom = INT_MAX;
		}
	};

	// ---- Text ----

	// .NET Framework's custom formats "0" (decimals 0) and "0.#" (decimals 1), as NinjaTrader's
	// label and row text use them: the double rounded to 15 significant digits (half away from
	// zero, so 100000000000000.5 -> 100000000000001; zeros past the 15th: 2^52 -> 4503599627370500),
	// then half away from zero to the decimals, trailing zeros dropped. Checked against .NET.
	std::string FormatNet(double value, int decimals)
	{
		if (!(value == value))
			return "NaN";
		char text[64];
		if (!(std::fabs(value) < 1e18))
		{
			snprintf(text, sizeof(text), "%.0f", value);
			return text;
		}
		snprintf(text, sizeof(text), "%.30e", std::fabs(value));	// d.ddd (30 decimals) e+XX: the exact value's digits
		int digits[16];
		digits[0] = text[0] - '0';
		for (int k = 1; k < 16; k++)
			digits[k] = text[k + 1] - '0';
		const char* exponentText = strchr(text, 'e');
		int exponent = exponentText ? atoi(exponentText + 1) : 0;
		if (digits[0] == 0)
			return "0";
		if (digits[15] >= 5)
		{
			int k = 14;
			while (k >= 0 && digits[k] == 9)
				digits[k--] = 0;
			if (k >= 0)
				digits[k]++;
			else
			{
				digits[0] = 1;	// 999... -> 1000...
				exponent++;
			}
		}
		const int keep = exponent + 1 + decimals;	// significant digits through the last decimal
		if (keep < 0)
			return "0";
		unsigned long long scaled = 0;
		for (int k = 0; k < keep; k++)
			scaled = scaled * 10 + (unsigned long long)(k < 15 ? digits[k] : 0);
		if (keep < 15 && digits[keep] >= 5)
			scaled++;
		if (scaled == 0)
			return "0";
		unsigned long long unit = 1;
		for (int k = 0; k < decimals; k++)
			unit *= 10;
		const char* sign = value < 0 ? "-" : "";
		unsigned long long fraction = scaled % unit;
		int places = decimals;
		while (places > 0 && fraction % 10 == 0 && fraction != 0)
		{
			fraction /= 10;
			places--;
		}
		if (fraction == 0)
			snprintf(text, sizeof(text), "%s%llu", sign, scaled / unit);
		else
			snprintf(text, sizeof(text), "%s%llu.%0*llu", sign, scaled / unit, places, fraction);
		return text;
	}

	// A session time as NinjaTrader's label shows the typed string: HH:mm, or HH:mm:ss when the
	// seconds are not 0.
	std::string TimeText(int seconds)
	{
		char text[16];
		seconds = (std::max)(0, (std::min)(SECONDS_PER_DAY - 1, seconds));
		if (seconds % 60 != 0)
			snprintf(text, sizeof(text), "%02d:%02d:%02d", seconds / 3600, seconds / 60 % 60, seconds % 60);
		else
			snprintf(text, sizeof(text), "%02d:%02d", seconds / 3600, seconds / 60 % 60);
		return text;
	}

	// NinjaTrader's chart label (DisplayName, NT:152-165), plus the count of sessions not built
	// from ticks (Sierra Chart only).
	struct LabelParts
	{
		bool		ShowInputs	= true;
		bool		ShowValues	= true;
		int			Start		= 30600;
		int			End			= 54000;
		int			Zone		= TZO_EXCHANGE;
		double		Percent		= 68;
		int			Placement	= PL_SESSION_RIGHT;
		bool		HasValues	= false;
		std::string	Poc;
		std::string	Vah;
		std::string	Val;
		int			Approximate	= 0;	// built from volume at price in place of ticks
		int			Waiting		= 0;	// waiting for Sierra Chart to build the volume at price
		int			Unavailable	= 0;	// no volume at price on this chart
	};

	std::string ChartLabel(const LabelParts& p)
	{
		std::string label = "Tatanka SVP";
		if (p.ShowInputs)
			label += " (" + TimeText(p.Start) + "-" + TimeText(p.End) + ", " + ZONE_NAMES[(std::max)(0, (std::min)(4, p.Zone))] + ", VA "
				+ FormatNet(p.Percent, 1) + "%, " + PLACEMENT_NAMES[p.Placement == PL_CHART_RIGHT_LATEST ? 1 : 0] + ")";
		if (p.ShowValues && p.HasValues)
			label += "  POC " + p.Poc + "  VAH " + p.Vah + "  VAL " + p.Val;
		if (p.Approximate > 0)
			label += "  (" + std::to_string(p.Approximate) + " not from ticks)";
		if (p.Waiting > 0)
			label += "  (" + std::to_string(p.Waiting) + " waiting for volume at price)";
		if (p.Unavailable > 0)
			label += "  (" + std::to_string(p.Unavailable) + " without tick data)";
		return label;
	}

	// Why sessions were built from volume at price, and the fix (spec C.6), for the message log.
	const char* ReasonText(int reason)
	{
		switch (reason)
		{
			case FR_STORAGE_UNIT:
				return "Intraday Data Storage Time Unit is not 1 Tick (Global Settings >> Data/Trade Service Settings); then Edit >> Delete "
					"All Data and Download.";
			case FR_BEFORE_FILE:	return "before this chart's tick data file (continuous contract)";
			case FR_MULTI_TRADE:	return "stored as multi-trade (for example 1-second) records, not ticks";
			case FR_PRICE_MISMATCH:	return "trade prices do not match the chart's bars (back-adjusted or multiplied prices)";
			case FR_TIME_BASE:		return "cannot match the tick data to the chart";
			case FR_VOLUME_MISMATCH:
				return "the tick data does not add up to the chart's volume (an older contract on a continuous contract chart, or missing ticks)";
			default:				return "";
		}
	}

	// One message-log line per rebuild for the sessions of one reason (spec B.9).
	std::string FallbackMessage(int reason, int sessions)
	{
		std::string text = "Tatanka Session Volume Profile: " + std::to_string(sessions) + (sessions == 1 ? " session" : " sessions")
			+ " built from volume at price, not ticks: " + ReasonText(reason);
		if (text.back() != '.')
			text += ".";
		return text;
	}

	// Configuration errors in NinjaTrader's order (NT:122-141): not intraday, tick size; then
	// tick, volume and range bars without end times (their x positions need them). NinjaTrader
	// runs on any intraday bars, 1440-minute ones too: an intraday chart's 1-day bars are their
	// counterpart. Bars of several days are not (NinjaTrader's minute bars end at every session
	// end; one bar here would span several sessions and end at the first session end).
	const char* ConfigError(int chartDataType, int barPeriodType, int secondsPerBar, bool hasEndTimes, double tick)
	{
		if (chartDataType != INTRADAY_DATA || barPeriodType == IBPT_MONTHS_PER_BAR || barPeriodType == IBPT_HISTORICAL_DAILY_DATA_DAYS_PER_BAR
			|| (barPeriodType == IBPT_DAYS_MINS_SECS && !(secondsPerBar > 0)))
			return MSG_NOT_INTRADAY;
		if (barPeriodType == IBPT_DAYS_MINS_SECS && secondsPerBar > SECONDS_PER_DAY)
			return MSG_MULTI_DAY;
		if (!(tick > 0))
			return MSG_BAD_SIZE;
		if (barPeriodType != IBPT_DAYS_MINS_SECS && !hasEndTimes)
			return MSG_NO_END_TIMES;
		return "";
	}

	// ---- Drawing geometry (spec D; no Sierra Chart calls) ----

	// The pixel boundary at which an aliased fill of the float edge v starts or stops: Direct2D
	// paints a pixel when its center is inside the shape (spec D.4).
	int PixEdge(double v)
	{
		return (int)std::ceil(v - 0.5);
	}

	// Where time T falls on the chart (spec D.1): NinjaTrader's GetXByTime on its bars stamped at
	// their ends, so between the centers of the two bars whose ends bracket T (08:30 on 30-minute
	// bars is the center of the 08:00 bar, which ends at 08:30). As a fractional bar index: i + f
	// is f of the way from bar i's center to bar i + 1's. Before the first bar's end and after the
	// last one it extrapolates by that bar's length. Empty columns count: they are on Sierra
	// Chart's time axis. S and E: the bars' starts and ends (BarTable).
	double EndPosition(const std::vector<int64_t>& S, const std::vector<int64_t>& E, int64_t T)
	{
		const size_t n = E.size();
		if (n == 0 || S.size() < n)
			return 0;
		const size_t i = (size_t)(std::lower_bound(E.begin(), E.end(), T) - E.begin());
		double f;
		if (i == n)
		{
			const int64_t length = E[n - 1] - S[n - 1];
			f = (double)(n - 1) + (length > 0 ? (double)(T - E[n - 1]) / (double)length : 0.0);
		}
		else if (i == 0)
		{
			const int64_t length = E[0] - S[0];
			f = length > 0 ? -(double)(E[0] - T) / (double)length : (T < E[0] ? -1.0 : 0.0);
		}
		else
			f = (double)(i - 1) + (double)(T - E[i - 1]) / (double)(E[i] - E[i - 1]);
		return (std::max)(-1e7, (std::min)(1e7, f));
	}

	// A fractional bar position in pixels, between the centers of the bars around it, rounded
	// to whole pixels as NinjaTrader's GetXByTime returns them. center(i): bar i's center, also
	// past the loaded bars.
	template <typename BarCenter>
	int PositionX(double position, BarCenter center)
	{
		const double whole	= std::floor(position);
		const int i			= (int)whole;
		const double x0		= (double)center(i);
		const double x1		= (double)center(i + 1);
		return (int)RoundHalfUp(x0 + (position - whole) * (x1 - x0));
	}

	// The time a profile's right edge stands for (NT:297-299): its newest trade while it forms,
	// its scheduled end once the chart's last bar ends there or later (also when trading stopped
	// early). lastLoadedEnd: the end of the chart's last bar.
	int64_t EdgeTime(int64_t lastChart, int64_t endChart, int64_t lastLoadedEnd)
	{
		return lastLoadedEnd >= endChart ? endChart : (std::min)(lastChart, endChart);
	}

	// A session's horizontal layout in pixels (NT:302-309, spec D.3 and D.6). NinjaTrader's pixel
	// constants are DIPs: times scale.
	struct SessionLayout
	{
		double	Right		= 0;	// rows grow left from here
		double	Width		= 0;	// the longest row
		double	LineLeft	= 0;	// where the level lines start
		double	BoxLeft		= 0;	// the histogram box
		double	BoxRight	= 0;
	};

	SessionLayout LayoutSession(bool pinned, int sessionLeft, int sessionRight, double panelLeft, double panelRight, int padding,
		double widthPercent, double scale)
	{
		SessionLayout l;
		l.Right				= pinned ? panelRight - padding * scale : (double)sessionRight;
		const double span	= pinned ? panelRight - panelLeft : (std::max)(2 * scale, (double)(sessionRight - sessionLeft));
		l.Width				= (std::max)(1 * scale, span * widthPercent / 100);
		l.LineLeft			= pinned ? (std::max)(panelLeft, l.Right - l.Width) : (double)sessionLeft;
		l.BoxLeft			= pinned ? l.Right - l.Width : (double)sessionLeft;
		l.BoxRight			= pinned ? l.Right : sessionLeft + (std::max)(1 * scale, l.Right - sessionLeft);
		return l;
	}

	// The low edge of row `key`, which is also the high edge of the row below: one expression for
	// both, so neighboring rows share their boundary pixel (spec D.4).
	double EdgePrice(int64_t key, double rowSize, double tick)
	{
		return (double)key * rowSize - tick / 2;
	}

	// One row between the pixel rows of its high and low edges (NT:315-329, spec D.4): a gap of
	// RowGap DIPs (at most 35 % of the row) split above and below, rows below 0.2 DIPs kept
	// sub-pixel; the down volume touches the anchor, the up volume is outside it.
	struct RowLayout
	{
		bool	Visible		= false;
		double	Full		= 0;	// the row's height
		double	Y			= 0;	// top of the painted part
		double	H			= 0;	// its height
		double	Left		= 0;	// left end of the up part
		double	UpWidth		= 0;
		double	DownWidth	= 0;
	};

	RowLayout LayoutRow(int yHigh, int yLow, int panelTop, int panelBottom, double right, double width, double up, double down,
		double maxVolume, int rowGap, double scale)
	{
		RowLayout r;
		const int top		= (std::min)(yHigh, yLow);
		const int bottom	= (std::max)(yHigh, yLow);
		if (bottom < panelTop || top > panelBottom)
			return r;
		r.Visible	= true;
		r.Full		= (double)(bottom - top);
		r.H			= (std::max)(0.2 * scale, r.Full - (std::min)(rowGap * scale, r.Full * 0.35));
		r.Y			= top + (r.Full - r.H) / 2;
		r.UpWidth	= maxVolume > 0 ? width * up / maxVolume : 0;
		r.DownWidth	= maxVolume > 0 ? width * down / maxVolume : 0;
		r.Left		= right - r.UpWidth - r.DownWidth;
		return r;
	}

	// The level label's left edge (NT:354): 5 DIPs right of the profile, kept 110 DIPs from the
	// panel's right edge and 4 inside its left. dip(x): x DIPs in whole pixels.
	template <typename Dip>
	double LevelLabelX(double panelLeft, double panelRight, double right, Dip dip)
	{
		return (std::max)(panelLeft + dip(4), (std::min)(right + dip(5), panelRight - dip(110)));
	}

	// The loaded bar whose center is nearest a fractional bar position.
	int NearestBar(double position, int count)
	{
		return (int)(std::max)(0.0, (std::min)((double)(count - 1), std::floor(position + 0.5)));
	}

	// The bars a translucent box range runs between (spec D.6): those whose centers are nearest
	// the profile's left and right edges. False when both are one bar (the callback blends it).
	bool BoxBars(const VpSnapshot& p, const std::vector<int64_t>& S, const std::vector<int64_t>& E, int& startBar, int& endBar)
	{
		const int n = (int)E.size();
		if (n == 0)
			return false;
		startBar	= NearestBar(EndPosition(S, E, p.StartChart), n);
		endBar		= NearestBar(EndPosition(S, E, EdgeTime(p.LastChart, p.EndChart, E.back())), n);
		return startBar < endBar;
	}

	// One session's translucent box as a Sierra Chart range: from the start bar's center to the
	// end bar's, between the profile's high and low edges.
	struct BoxPiece
	{
		int		StartBar	= 0;
		int		EndBar		= 0;
		int		Id			= 1;
		double	Top			= 0;
		double	Bottom		= 0;
	};

	uint64_t RangeKey(int startBar, int id)
	{
		return ((uint64_t)(uint32_t)startBar << 32) | (uint64_t)(uint32_t)id;
	}

	// The box ranges of the drawn sessions (nullptr: none yet), sorted by RangeKey. Sessions sharing
	// a start bar get the next id.
	std::vector<BoxPiece> BoxPieces(const std::vector<const VpSnapshot*>& drawn, const std::vector<int64_t>& S, const std::vector<int64_t>& E)
	{
		std::vector<BoxPiece> out;
		for (const VpSnapshot* p : drawn)
		{
			BoxPiece b;
			if (p == nullptr || !p->Valid || !BoxBars(*p, S, E, b.StartBar, b.EndBar))
				continue;
			b.Top		= p->Stats.HighEdge;
			b.Bottom	= p->Stats.LowEdge;
			for (const BoxPiece& o : out)
				if (o.StartBar == b.StartBar)
					b.Id = (std::max)(b.Id, o.Id + 1);
			out.push_back(b);
		}
		std::sort(out.begin(), out.end(), [](const BoxPiece& a, const BoxPiece& b) { return RangeKey(a.StartBar, a.Id) < RangeKey(b.StartBar, b.Id); });
		return out;
	}

	// ---- Sierra Chart glue ----

	// The level colors and the hidden levels' scale labels (spec A #5, D.10): a hidden level
	// keeps its values, only its label goes.
	void UpdateSubgraphs(SCStudyInterfaceRef sc)
	{
		const int shows[3]			= {IN_SHOW_POC, IN_SHOW_VAH, IN_SHOW_VAL};
		const uint32_t colors[3]	= {sc.Input[IN_POC_LINE_COLOR].GetColor(), sc.Input[IN_VA_LINE_COLOR].GetColor(),
			sc.Input[IN_VA_LINE_COLOR].GetColor()};
		for (int k = 0; k < 3; k++)
		{
			SCSubgraphRef g = sc.Subgraph[k];
			g.PrimaryColor = colors[k];
			if (sc.Input[shows[k]].GetYesNo())
				g.LineLabel |= LL_DISPLAY_VALUE;
			else
				g.LineLabel &= ~(unsigned int)LL_DISPLAY_VALUE;
		}
	}

	LabelParts LabelOf(SCStudyInterfaceRef sc)
	{
		LabelParts p;
		p.ShowInputs	= sc.Input[IN_INPUTS_IN_LABEL].GetYesNo() != 0;
		p.ShowValues	= sc.Input[IN_VALUES_IN_LABEL].GetYesNo() != 0;
		p.Start			= sc.Input[IN_SESSION_START].GetTime();
		p.End			= sc.Input[IN_SESSION_END].GetTime();
		p.Zone			= (std::min)((int)sc.Input[IN_TIME_ZONE].GetIndex(), (int)TZO_UTC);
		p.Percent		= sc.Input[IN_VA_PERCENT].GetDouble();
		p.Placement		= (std::min)((int)sc.Input[IN_PLACEMENT].GetIndex(), (int)PL_CHART_RIGHT_LATEST);
		return p;
	}

	// A price as the chart shows it (NinjaTrader's FormatPrice, NT:167-171).
	std::string Price(SCStudyInterfaceRef sc, double price)
	{
		const SCString text = sc.FormatGraphValue(price, sc.BaseGraphValueFormat);
		return text.GetChars();
	}

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

	// The engine inputs (spec B.2): a change of anything in Key rebuilds the sessions; the value
	// area and retention are applied to the sessions as they are.
	struct EngineInputs
	{
		ProfileConfig	Cfg;
		int				Start		= 30600;
		int				End			= 54000;
		int				Zone		= TZO_EXCHANGE;
		int				Retain		= 20;
		bool			TimeBased	= true;
		uint32_t		Key			= 0;
	};

	EngineInputs ReadEngineInputs(SCStudyInterfaceRef sc, bool timeBased)
	{
		EngineInputs in;
		in.Start			= sc.Input[IN_SESSION_START].GetTime();
		in.End				= sc.Input[IN_SESSION_END].GetTime();
		in.Zone				= (std::min)((int)sc.Input[IN_TIME_ZONE].GetIndex(), (int)TZO_UTC);
		in.Retain			= (std::max)(1, (std::min)(100, sc.Input[IN_SESSIONS].GetInt()));
		in.TimeBased		= timeBased;
		in.Cfg.Tick			= DecimalTickSize(sc.TickSize);
		in.Cfg.TicksPerRow	= (std::max)(1, (std::min)(1000, sc.Input[IN_TICKS_PER_ROW].GetInt()));
		in.Cfg.Mode			= (std::min)((int)sc.Input[IN_VOLUME_DATA].GetIndex(), (int)VD_VAP);
		in.Cfg.Percent		= (std::max)(1.0, (std::min)(100.0, sc.Input[IN_VA_PERCENT].GetDouble()));
		in.Cfg.AtLeast		= (int)sc.Input[IN_VA_METHOD].GetIndex() == VAM_ATLEAST;
		// What the rows and deltas depend on: the window, the rows, the split, the bars (their
		// period and Session Times), the storage unit, the volume at price's granularity (Sierra
		// Chart rebuilds it when the multiplier changes) and the chart's time zone.
		const ChartSessions s = SessionsOf(sc);
		const int64_t numbers[] = {in.Start, in.End, in.Zone, in.Cfg.TicksPerRow, in.Cfg.Mode, timeBased, sc.SecondsPerBar, s.DayStart, s.DayEnd,
			s.EveningStart, s.EveningEnd, s.UseEvening, s.NewBarAtSessionStart, (int64_t)sc.IntradayDataStorageTimeUnit,
			(int64_t)sc.VolumeAtPriceMultiplier};
		uint32_t key = Fnv1a(2166136261u, numbers, sizeof(numbers));
		key = Fnv1a(key, &in.Cfg.Tick, sizeof(in.Cfg.Tick));
		const SCString zone = sc.GetChartTimeZone(sc.ChartNumber);
		key = Fnv1a(key, zone.GetChars(), (size_t)zone.GetLength());
		in.Key = key == 0 ? 1 : key;
		return in;
	}

	int64_t Micros(const SCDateTime& t)
	{
		return t.AsMicrosecondsSinceBaseDate();
	}

	// sc.ReadIntradayFileRecordAtIndex with the file locked for the reads of one study call (spec
	// C.4 step 4, Sierra Chart's own example): the first read takes the lock, the others keep it,
	// Release lets it go; the destructor releases it on every way out of the call, so the lock is
	// never held across calls (live data keeps flowing between them).
	struct SierraReader final : RecordReader
	{
		s_sc*	Sc		= nullptr;
		bool	Locked	= false;
		int64_t	Reads	= 0;

		explicit SierraReader(SCStudyInterfaceRef sc) : Sc(&sc) {}
		SierraReader(const SierraReader&) = delete;
		SierraReader& operator=(const SierraReader&) = delete;
		~SierraReader() { Release(); }

		bool Read(int64_t index, s_IntradayRecord& record) override
		{
			if (index < 0)
				return false;
			record = s_IntradayRecord();
			const int result = Sc->ReadIntradayFileRecordAtIndex(index, record, Locked ? IFLA_NO_CHANGE : IFLA_LOCK_READ_HOLD);
			Locked = true;
			Reads++;
			// The return value is not documented: a read that filled in nothing failed.
			return result != 0 || record.DateTime.AsMicrosecondsSinceBaseDate() != 0;
		}

		void Release()
		{
			if (!Locked)
				return;
			s_IntradayRecord unused;
			Sc->ReadIntradayFileRecordAtIndex(-1, unused, IFLA_RELEASE_AFTER_READ);	// -1: no read, only the release
			Locked = false;
		}
	};

	// Sierra Chart's volume at price per bar (sc.VolumeAtPriceForBars, spec C.5).
	struct SierraVap final : VapSource
	{
		const c_VAPContainer*	Vap	= nullptr;

		int BarCount() override
		{
			return Vap != nullptr ? (int)Vap->GetNumberOfBars() : 0;
		}

		bool Elements(int bar, std::vector<VapElement>& out) override
		{
			out.clear();
			if (Vap == nullptr || bar < 0 || (unsigned int)bar >= Vap->GetNumberOfBars())
				return false;
			const unsigned int count = Vap->GetSizeAtBarIndex((unsigned int)bar);
			for (unsigned int k = 0; k < count; k++)
			{
				const s_VolumeAtPriceV2* p = nullptr;
				if (!Vap->GetVAPElementAtIndex((unsigned int)bar, (int)k, &p) || p == nullptr)
					continue;
				VapElement e;
				e.PriceInTicks	= p->PriceInTicks;
				e.Volume		= p->Volume;
				e.BidVolume		= p->BidVolume;
				e.AskVolume		= p->AskVolume;
				out.push_back(e);
			}
			return !out.empty();
		}
	};

	struct SnapshotEntry
	{
		int64_t		Version	= -1;
		VpSnapshot	Snap;
	};

	// Everything the study keeps between calls (one heap object per study instance).
	struct StudyState
	{
		std::string		Error;							// configuration error for the drawing callback
		std::string		Message;						// drawn while no session has rows

		// The engine and what it was built with (spec B.5, C).
		bool			Built			= false;
		uint32_t		EngineKey		= 0;
		ProfileConfig	Cfg;
		int				Retain			= 20;
		WindowTable		Windows;
		BarTable		Bars;
		OffsetTable		Offsets;
		int64_t			OffsetsTo		= 0;			// UTC the offset table reaches
		RecordMapper	Mapper;
		VpEngine		Engine;
		int				TimeBase		= TB_UNKNOWN;
		int				AllVapReason	= -1;			// >= 0: every session from volume at price, and why
		int64_t			FirstIndex		= 0;			// the chart's first record in the file
		int64_t			FileStart		= INT64_MIN;	// > INT64_MIN: the chart starts before this file

		// Loading (spec C.7).
		bool			Planned			= false;
		LoadPlan		Plan;
		size_t			HistoryPos		= 0;
		bool			Building		= false;
		WindowBuild		Build;
		size_t			BeforeFilePos	= 0;
		int				VapFrom			= 0;			// the first bar volume at price still has to take
		bool			Pending			= false;		// more to read or wait for: Sierra Chart calls again
		bool			CaughtUp		= false;		// the live path reached the file's end in the last call
		bool			VapWaiting		= false;		// Sierra Chart's volume at price is not built for every bar yet
		bool			VapMissing		= false;		// sc.VolumeAtPriceForBars is not there
		bool			FallbackLogged	= false;

		// The per-bar values written: window date -> the session's first bar then; the first bar
		// still to write once the sessions are shown.
		std::map<int, int>	Written;
		int					ValuesFrom	= 0;

		// Drawing: the retained sessions oldest first (nullptr: no rows yet), snapshots by date.
		std::map<int, SnapshotEntry>		Snaps;
		std::vector<const VpSnapshot*>		Drawn;

		// Translucent box ranges sent to Sierra Chart: (start bar, id) -> signature.
		std::map<uint64_t, uint32_t>	Sent;
		uint32_t						RangesKey		= 0;

		// Diagnostics (tests, harness).
		int				Rebuilds		= 0;
		int				RangeAdds		= 0;
		int				RangeDeletes	= 0;
		int64_t			Reads			= 0;
		int64_t			ValuesWritten	= 0;			// bars whose subgraph values were written

		// Frees the engine (a configuration error, no bars): rebuilt from bar 0 next time.
		void ResetEngine()
		{
			Built		= false;
			EngineKey	= 0;
			Windows		= WindowTable();
			Bars		= BarTable();
			Offsets		= OffsetTable();
			Engine		= VpEngine();
			Plan		= LoadPlan();
			Build		= WindowBuild();
			Planned		= false;
			Building	= false;
			Pending		= false;
			VapWaiting	= false;
			Written.clear();
			Snaps.clear();
			Drawn.clear();
		}
	};

	StudyState& GetState(SCStudyInterfaceRef sc)
	{
		void*& slot = sc.GetPersistentPointer(PP_STATE);
		if (slot == nullptr)
			slot = new StudyState();
		return *static_cast<StudyState*>(slot);
	}

	// The state if the study function made one (the drawing callback never creates it).
	StudyState* PeekState(SCStudyInterfaceRef sc)
	{
		return static_cast<StudyState*>(sc.GetPersistentPointer(PP_STATE));
	}

	void DeleteState(SCStudyInterfaceRef sc)
	{
		void*& slot = sc.GetPersistentPointer(PP_STATE);
		delete static_cast<StudyState*>(slot);
		slot = nullptr;
	}

	// The chart's bars from `from` on (spec B.3): start, end (NinjaTrader's close stamp), the time
	// they cover, tick-snapped low and high. An empty column covers nothing.
	void ReadBars(SCStudyInterfaceRef sc, const EngineInputs& in, BarTable& bars, int from)
	{
		const int n = sc.ArraySize;
		bars.Resize(n);
		const ChartSessions sessions = SessionsOf(sc);
		for (int i = (std::max)(0, from); i < n; i++)
		{
			const int64_t start	= Micros(sc.BaseDateTimeIn[i]);
			const bool hasNext	= i + 1 < n;
			const int64_t next	= hasNext ? Micros(sc.BaseDateTimeIn[i + 1]) : 0;
			const double low	= SnapToTick(sc.Low[i], in.Cfg.Tick);
			const double high	= SnapToTick(sc.High[i], in.Cfg.Tick);
			if (in.TimeBased)
				bars.SetTimeBar(i, start, sc.SecondsPerBar, hasNext, next, sessions, low, high);
			else
				bars.SetTradeBar(i, start, Micros(sc.BaseDataEndDateTime[i]), hasNext, next, low, high);
			bars.SetTrades(i, SnapToTick(sc.Open[i], in.Cfg.Tick), SnapToTick(sc.Close[i], in.Cfg.Tick), (double)sc.Volume[i]);
			if (IsEmptyColumn(sc.Volume[i], sc.NumberOfTrades[i], sc.Open[i], sc.High[i], sc.Low[i], sc.Close[i], i > 0,
				i > 0 ? sc.Close[i - 1] : 0.0f))
				bars.C[(size_t)i] = start;
		}
	}

	// Whether the first `count` bars are the same in both tables.
	bool SameBars(const BarTable& a, const BarTable& b, int count)
	{
		if (count < 0 || a.Count() < count || b.Count() < count)
			return false;
		for (size_t i = 0; i < (size_t)count; i++)
			if (a.S[i] != b.S[i] || a.E[i] != b.E[i] || a.C[i] != b.C[i] || a.Low[i] != b.Low[i] || a.High[i] != b.High[i]
				|| a.HasTrades((int)i) != b.HasTrades((int)i)
				|| (a.HasTrades((int)i) && (a.Volume[i] != b.Volume[i] || a.Open[i] != b.Open[i] || a.Close[i] != b.Close[i])))
				return false;
		return true;
	}

	// The session windows over the chart's dates (spec B.4), extended as bars arrive.
	void CoverWindows(SCStudyInterfaceRef sc, StudyState& st, int zone)
	{
		if (st.Bars.Count() == 0)
			return;
		const bool identity		= IsChartZoneOption(zone);
		const TimeZonesEnum z	= ZoneOf(zone);
		st.Windows.CoverSpan(st.Bars.S.front(), st.Bars.E.back(),
			[&sc, identity, z](int64_t t) { return identity ? t : Micros(sc.ConvertDateTimeFromChartTimeZone(SCDateTime::MICROSECONDS(t), z)); },
			[&sc, identity, z](int64_t local) { return identity ? local : Micros(sc.ConvertDateTimeToChartTimeZone(SCDateTime::MICROSECONDS(local), z)); });
	}

	// UTC -> chart offsets for records stamped in UTC (spec C.4 step 1), a day or more past the
	// chart's last bar (rebuilt further as bars arrive).
	void UpdateOffsets(SCStudyInterfaceRef sc, StudyState& st)
	{
		if (st.TimeBase != TB_UTC || st.Bars.Count() == 0)
			return;
		if (!st.Offsets.Empty() && st.Bars.E.back() + US_PER_DAY <= st.OffsetsTo)
			return;
		st.OffsetsTo = st.Bars.E.back() + 3 * US_PER_DAY;
		st.Offsets.Build(st.Bars.S.front() - 2 * US_PER_DAY, st.OffsetsTo,
			[&sc](int64_t utc) { return Micros(sc.ConvertDateTimeUTCToChartTimeZone(SCDateTime::MICROSECONDS(utc))); });
	}

	// Whether the file's records are stamped in chart time or UTC (spec C.4 step 1, CalibrateRecords).
	int CalibrateFile(SCStudyInterfaceRef sc, const BarTable& bars, RecordReader& reader, int64_t last, double tick)
	{
		return CalibrateRecords(reader, last, bars, tick,
			[&sc](int64_t utc) { return Micros(sc.ConvertDateTimeUTCToChartTimeZone(SCDateTime::MICROSECONDS(utc))); },
			[&sc](int64_t chart) { return Micros(sc.ConvertDateTimeFromChartTimeZone(SCDateTime::MICROSECONDS(chart), TIMEZONE_UTC)); });
	}

	// The chart time of record `index` (one read), INT64_MAX when it cannot be read.
	int64_t ChartTimeAt(RecordReader& reader, const RecordMapper& mapper, int64_t index)
	{
		s_IntradayRecord r;
		return reader.Read(index, r) ? mapper.ChartTime(r) : INT64_MAX;
	}

	// Builds the engine anew (spec C.4, C.7): calibrates the records' time base, decides the data
	// path and plans the load. The bars are already read.
	void Rebuild(SCStudyInterfaceRef sc, StudyState& st, const EngineInputs& in, RecordReader& reader)
	{
		st.Rebuilds++;
		st.Built			= true;
		st.EngineKey		= in.Key;
		st.Cfg				= in.Cfg;
		st.Retain			= in.Retain;
		st.Engine			= VpEngine(in.Cfg, in.Retain);
		st.Windows.Reset(in.Start, in.End);
		CoverWindows(sc, st, in.Zone);
		st.Offsets			= OffsetTable();
		st.OffsetsTo		= 0;
		st.Planned			= false;
		st.CaughtUp			= false;
		st.Plan				= LoadPlan();
		st.HistoryPos		= 0;
		st.Building			= false;
		st.Build			= WindowBuild();
		st.BeforeFilePos	= 0;
		st.VapFrom			= 0;
		st.FileStart		= INT64_MIN;
		st.FirstIndex		= 0;
		st.FallbackLogged	= false;
		st.Written.clear();
		st.Snaps.clear();
		st.Drawn.clear();

		const int64_t last	= sc.FileRecordIndexOfLastDataRecordInChart;
		st.TimeBase			= CalibrateFile(sc, st.Bars, reader, last, in.Cfg.Tick);
		st.Mapper.Windows	= &st.Windows;
		st.Mapper.Bars		= &st.Bars;
		st.Mapper.Offsets	= &st.Offsets;
		st.Mapper.Base		= st.TimeBase == TB_UTC ? TB_UTC : TB_CHART;
		st.Mapper.Tick		= in.Cfg.Tick;
		UpdateOffsets(sc, st);

		if (in.Cfg.Mode == VD_VAP)
			st.AllVapReason = FR_NONE;			// the user's choice
		else if (sc.IntradayDataStorageTimeUnit != 0)
			st.AllVapReason = FR_STORAGE_UNIT;
		else if (st.TimeBase == TB_UNKNOWN)
			st.AllVapReason = FR_TIME_BASE;
		else
			st.AllVapReason = -1;
		if (st.AllVapReason >= 0)
			return;

		auto chartAt = [&reader, &st](int64_t i) { return ChartTimeAt(reader, st.Mapper, i); };
		// A file that begins after the chart's first bar with trades: the chart starts before
		// this file (a continuous contract stitched from older files, spec C.4 step 2).
		const int64_t first = chartAt(0);
		for (int i = 0; i < st.Bars.Count(); i++)
			if (st.Bars.C[(size_t)i] > st.Bars.S[(size_t)i])
			{
				if (first != INT64_MAX && first >= st.Bars.C[(size_t)i])
					st.FileStart = first;
				break;
			}
		st.FirstIndex	= FirstRecordAtOrAfter(0, last, st.Bars.S.front(), chartAt);
		st.Plan			= PlanLoad(st.Windows, st.Bars, chartAt(last), st.FileStart);
		if (st.Plan.Stream < 0)
			return;
		if (st.Plan.StreamBeforeFile)
			st.Engine.MarkWindowVap(st.Windows.Windows[(size_t)st.Plan.Stream], FR_BEFORE_FILE);
		st.Engine.StartStream(FirstRecordAtOrAfter(st.FirstIndex, last, st.Windows.Windows[(size_t)st.Plan.Stream].StartChart, chartAt));
		st.Planned	= true;
	}

	// Sessions that lost their rows (older than retention) and are needed again: for a value-area
	// change (dropLevels) or a larger retention (spec C.7). Each stays as it is until it is read
	// again in the background, the retained profiles stay shown meanwhile: those built from the
	// file are queued with the history windows, those from volume at price are built from it on
	// this call. False when one of them cannot be read again that way (the developing session past
	// MAX_DELTAS: it is still being read live): the engine must be rebuilt.
	bool RestoreSessions(StudyState& st, const std::vector<int>& dates, bool dropLevels)
	{
		bool queued = false;
		for (int date : dates)
		{
			const auto it = st.Engine.Sessions.find(date);
			if (it == st.Engine.Sessions.end())
				continue;
			VpSession& s = it->second;
			if (!s.Compacted && &s == st.Engine.Newest() && s.Source == SRC_TRADES)
				return false;
			s.MarkStale(dropLevels);
			if (!s.ReadAgain())
				continue;
			const SessionWindow* w = st.Windows.ByDate(date);
			if (w == nullptr || !st.Planned)
				return false;
			st.Plan.History.push_back((int)(w - st.Windows.Windows.data()));
			queued = true;
		}
		if (queued)
		{
			// Newest first, from the start: windows read before are skipped.
			std::vector<int>& h = st.Plan.History;
			std::sort(h.begin(), h.end(), [](int a, int b) { return a > b; });
			h.erase(std::unique(h.begin(), h.end()), h.end());
			st.HistoryPos	= 0;
			st.Building		= false;
		}
		return true;
	}

	enum LoadResult { LR_OK, LR_REBUILD };

	// One call's share of the work (spec C.7, C.8): the live path (the newest window from its
	// first record, then every new record), the older windows newest first while time is left,
	// then volume at price for the sessions that need it. Sierra Chart is asked to call again
	// while anything is left.
	LoadResult RunLoad(SCStudyInterfaceRef sc, StudyState& st, SierraReader& reader, int from)
	{
		const auto started = std::chrono::steady_clock::now();
		auto outOfTime = [&started]() { return std::chrono::steady_clock::now() - started >= std::chrono::milliseconds(g_ReadBudgetMs); };
		st.Pending		= false;
		st.VapWaiting	= false;
		const int64_t last = sc.FileRecordIndexOfLastDataRecordInChart;

		if (st.Planned)
		{
			bool caughtUp = false;
			for (;;)
			{
				const StreamStatus status = st.Engine.Stream(reader, st.Mapper, last, g_ChunkRecords);
				if (status == SS_REBUILD)
					return LR_REBUILD;
				if (status == SS_CAUGHT_UP)
				{
					caughtUp = true;
					break;
				}
				if (outOfTime())
					break;
			}
			// Behind the file's end (a first load, or many records at once: a historical download
			// or a backfill appended to the chart), the sessions are not shown: the ones still
			// being read would pass for complete (Showing).
			st.CaughtUp = caughtUp;
			// At least one chunk of history per call, so the load always moves on.
			auto chartAt = [&reader, &st](int64_t i) { return ChartTimeAt(reader, st.Mapper, i); };
			bool worked = false;
			while (caughtUp && st.HistoryPos < st.Plan.History.size() && (!worked || !outOfTime()))
			{
				const int k = st.Plan.History[st.HistoryPos];
				const SessionWindow& w = st.Windows.Windows[(size_t)k];
				if (!st.Building)
				{
					const auto existing = st.Engine.Sessions.find(w.Date);
					if (existing != st.Engine.Sessions.end() && !existing->second.ReadAgain())
					{
						st.HistoryPos++;	// read already (or the live path made it)
						continue;
					}
					st.Build			= WindowBuild();
					st.Build.Window		= k;
					st.Build.Session.Cfg = st.Engine.Cfg;
					st.Build.Next		= FirstRecordAtOrAfter(st.FirstIndex, last, w.StartChart, chartAt);
					st.Build.Hi			= FirstRecordAtOrAfter(st.FirstIndex, last, w.EndChart, chartAt);
					st.Building			= true;
				}
				worked = true;
				if (VpEngine::RunBuild(st.Build, reader, st.Mapper, g_ChunkRecords))
				{
					st.Engine.Insert(st.Build);
					st.Build	= WindowBuild();
					st.Building	= false;
					st.HistoryPos++;
				}
			}
			st.Pending = !caughtUp || st.HistoryPos < st.Plan.History.size();
		}

		// The forming bar's newest trade time, for volume-at-price sessions (spec C.5).
		int64_t formingLast = 0;
		if (st.TimeBase != TB_UNKNOWN && last >= 0)
		{
			const int64_t t = ChartTimeAt(reader, st.Mapper, last);
			formingLast = t == INT64_MAX ? 0 : t;
		}
		reader.Release();

		st.VapMissing = sc.VolumeAtPriceForBars == nullptr;
		if (st.VapMissing)
			return LR_OK;
		SierraVap source;
		source.Vap			= sc.VolumeAtPriceForBars;
		const int vapFrom	= (std::min)(st.VapFrom, from);
		VapStatus status	= VS_DONE;
		// Windows before the file; the sessions to build from volume at price (found not to be
		// single trades, or stale ones built from it before), those older than retention too, for
		// their per-bar values (spec A #36); then the new bars of every session built from it
		// (with the Volume at price option or every session falling back: of every window), but
		// for those just built through the last bar.
		std::vector<int> built;
		for (; st.BeforeFilePos < st.Plan.BeforeFile.size() && status == VS_DONE; st.BeforeFilePos++)
		{
			const SessionWindow& w = st.Windows.Windows[(size_t)st.Plan.BeforeFile[st.BeforeFilePos]];
			status = st.Engine.BuildFromVap(w, st.Bars, source, formingLast, FR_BEFORE_FILE);
			if (status != VS_DONE)
				break;
			built.push_back(w.Date);
		}
		std::vector<std::pair<int, int>> waiting;
		for (const auto& e : st.Engine.Sessions)
			if (e.second.WantsVap())
				waiting.push_back({e.first, e.second.Reason});
		for (size_t k = 0; k < waiting.size() && status == VS_DONE; k++)
			if (const SessionWindow* w = st.Windows.ByDate(waiting[k].first))
			{
				status = st.Engine.BuildFromVap(*w, st.Bars, source, formingLast, waiting[k].second);
				if (status == VS_DONE)
					built.push_back(w->Date);
			}
		if (status == VS_DONE)
		{
			const bool all = st.AllVapReason >= 0;
			status = st.Engine.UpdateVap(st.Windows, st.Bars, source, vapFrom, formingLast, all, all ? st.AllVapReason : FR_NONE, built);
		}
		st.VapWaiting = status == VS_WAITING;
		if (st.VapWaiting)
		{
			st.VapFrom	= vapFrom;
			st.Pending	= true;
		}
		else
			st.VapFrom = INT_MAX;
		return LR_OK;
	}

	// POC, VAH and VAL per bar into the subgraphs (spec B.7, C.8): from bar `from` on (the bars
	// Sierra Chart updates), and from the first bar whose levels changed since the last write in
	// any session (ChangedFrom; a session new, replaced or gone: from its first bar), to the
	// last bar. Live, that is the forming bar or two, however long the session.
	void WriteValues(SCStudyInterfaceRef sc, StudyState& st, int from)
	{
		int first = from;
		std::map<int, int> now;
		for (const auto& e : st.Engine.Sessions)
		{
			const VpSession& s	= e.second;
			const int bar		= s.FirstBar >= 0 ? s.FirstBar : INT_MAX;
			const auto it		= st.Written.find(e.first);
			if (it == st.Written.end())
				first = (std::min)(first, bar);
			else if (s.ChangedFrom != INT_MAX)
				first = (std::min)(first, s.ChangedFrom == INT_MIN ? (std::min)(it->second, bar) : s.ChangedFrom);
			now[e.first] = bar;
		}
		for (const auto& w : st.Written)
			if (now.count(w.first) == 0)
				first = (std::min)(first, w.second);
		st.Written.swap(now);
		st.Engine.ClearChanges();
		const int begin = (std::max)(0, first);
		for (int i = begin; i < sc.ArraySize; i++)
		{
			Levels l;
			const bool has = st.Engine.LevelsAt(i, l);
			sc.Subgraph[SG_POC][i] = has ? (float)l.Poc : 0.0f;
			sc.Subgraph[SG_VAH][i] = has ? (float)l.Vah : 0.0f;
			sc.Subgraph[SG_VAL][i] = has ? (float)l.Val : 0.0f;
		}
		st.ValuesWritten += (std::max)(0, sc.ArraySize - begin);
	}

	// Whether the sessions are shown: only while the live path is at the file's end (after a
	// first load, or many records at once, a profile half read would pass for the real one); the
	// older sessions then appear as they are read, newest first (spec C.7).
	bool Showing(const StudyState& st)
	{
		return !st.Planned || st.CaughtUp;
	}

	// Whether the chart's tick records are being read (the "reading tick data" message): the live
	// path is behind the file's end, or history windows are still to read.
	bool ReadingTicks(const StudyState& st)
	{
		return st.Planned && (!st.CaughtUp || st.HistoryPos < st.Plan.History.size());
	}

	// The retained sessions' snapshots for the drawing (spec A #33): a session's snapshot is made
	// again only when it changed (the developing one on each call that brings it trades).
	void UpdateSnapshots(StudyState& st)
	{
		const std::vector<const VpSession*> retained = Showing(st) ? st.Engine.Retained() : std::vector<const VpSession*>();
		for (auto it = st.Snaps.begin(); it != st.Snaps.end();)
		{
			const int date = it->first;
			const bool kept = std::any_of(retained.begin(), retained.end(), [date](const VpSession* s) { return s->Date == date && s->HasRows(); });
			it = kept ? std::next(it) : st.Snaps.erase(it);
		}
		st.Drawn.clear();
		for (const VpSession* s : retained)
		{
			if (!s->HasRows())
			{
				st.Drawn.push_back(nullptr);
				continue;
			}
			SnapshotEntry& e = st.Snaps[s->Date];
			if (e.Version != s->Version)
			{
				e.Version	= s->Version;
				e.Snap		= s->Snapshot();
			}
			st.Drawn.push_back(&e.Snap);
		}
	}

	bool HasDrawable(const StudyState& st)
	{
		for (const VpSnapshot* p : st.Drawn)
			if (p != nullptr && p->Valid && !p->Rows.empty())
				return true;
		return false;
	}

	// NinjaTrader's chart label (spec B.8) in the study's Short Name (D.9), rewritten only when
	// it changes.
	void UpdateLabel(SCStudyInterfaceRef sc, const StudyState* st)
	{
		LabelParts p = LabelOf(sc);
		if (st != nullptr && st->Built && st->Error.empty() && sc.ArraySize > 0 && Showing(*st))
		{
			Levels l;
			if (st->Engine.LevelsAt(sc.ArraySize - 1, l))
			{
				p.HasValues	= true;
				p.Poc		= Price(sc, l.Poc);
				p.Vah		= Price(sc, l.Vah);
				p.Val		= Price(sc, l.Val);
			}
			const VpEngine::SourceCounts counts = st->Engine.Counts();
			p.Approximate	= counts.Approximate;
			p.Waiting		= st->VapMissing ? 0 : counts.Waiting;
			p.Unavailable	= st->VapMissing ? counts.Waiting : 0;
		}
		const std::string label = ChartLabel(p);
		if (!(sc.GraphShortName == label.c_str()))
			sc.GraphShortName = label.c_str();
	}

	// One message-log line per reason once a load is done (spec B.9, C.6).
	void LogFallbacks(SCStudyInterfaceRef sc, StudyState& st)
	{
		if (st.Pending || st.FallbackLogged || !st.Built)
			return;
		st.FallbackLogged = true;
		std::map<int, int> byReason;
		int waiting = 0;
		for (const VpSession* s : st.Engine.Retained())
		{
			if (s->Source == SRC_VAP && s->Reason != FR_NONE)
				byReason[s->Reason]++;
			else if (s->NeedsVap && s->Source != SRC_VAP)
				waiting++;
		}
		for (const auto& e : byReason)
			sc.AddMessageToLog(FallbackMessage(e.first, e.second).c_str(), 0);
		if (st.VapMissing && waiting > 0)
			sc.AddMessageToLog((std::string("Tatanka Session Volume Profile: ") + MSG_NO_VAP).c_str(), 0);
	}

	// Reads the chart's bars and records into the engine and keeps everything the drawing needs
	// (spec C.7, C.8). A full recalculation (an input edit, a reload) keeps the engine when the
	// engine inputs and the bars it was built on are unchanged, so editing a color reads nothing
	// again and the value area or the retention reads again only the sessions older than
	// retention that need it, in the background; otherwise, and when the file no longer matches
	// what was read, it is rebuilt from bar 0.
	void ProcessCall(SCStudyInterfaceRef sc, StudyState& st, bool timeBased)
	{
		const EngineInputs in	= ReadEngineInputs(sc, timeBased);
		const int oldCount		= st.Bars.Count();
		bool rebuild = !st.Built || in.Key != st.EngineKey || sc.ArraySize < oldCount;
		int from = 0;
		if (rebuild)
			ReadBars(sc, in, st.Bars, 0);
		else if (sc.IsFullRecalculation || sc.UpdateStartIndex < oldCount - 1)
		{
			// Bars before the last one must be as the engine read them (deltas are per bar).
			BarTable fresh;
			ReadBars(sc, in, fresh, 0);
			rebuild		= !SameBars(st.Bars, fresh, oldCount - 1);
			st.Bars		= std::move(fresh);
			from		= rebuild ? 0 : (std::max)(0, oldCount - 1);
		}
		else
		{
			from = (std::max)(0, (std::min)(sc.UpdateStartIndex, oldCount - 1));
			ReadBars(sc, in, st.Bars, from);
		}
		int valuesFrom = sc.IsFullRecalculation || rebuild ? 0 : from;

		if (st.Bars.Count() == 0)
		{
			st.ResetEngine();
			st.Message = MSG_NO_TICKS;
			return;
		}

		SierraReader reader(sc);
		for (int attempt = 0; attempt < 2; attempt++)
		{
			if (rebuild)
			{
				Rebuild(sc, st, in, reader);
				from		= 0;
				valuesFrom	= 0;
			}
			else
			{
				CoverWindows(sc, st, in.Zone);
				UpdateOffsets(sc, st);
				std::vector<int> restore;
				bool dropLevels = false;
				if (in.Cfg.Percent != st.Cfg.Percent || in.Cfg.AtLeast != st.Cfg.AtLeast)
				{
					// The levels from the stored deltas (no reading). The sessions without them
					// (older than retention) are read again in the background for their per-bar
					// levels; the window being read is started again with the new inputs.
					st.Cfg.Percent	= in.Cfg.Percent;
					st.Cfg.AtLeast	= in.Cfg.AtLeast;
					st.Building		= false;
					restore			= st.Engine.SetValueArea(in.Cfg.Percent, in.Cfg.AtLeast);
					dropLevels		= true;
				}
				if (in.Retain != st.Retain)
				{
					// More sessions retained: those that lost their rows are read again (only
					// those). Fewer: the older ones keep only their per-bar levels.
					if (in.Retain > st.Retain)
						for (int date : st.Engine.CompactedWithin(in.Retain))
							if (std::find(restore.begin(), restore.end(), date) == restore.end())
								restore.push_back(date);
					st.Retain			= in.Retain;
					st.Engine.Retain	= in.Retain;
					st.Engine.ApplyRetention();
				}
				if (!restore.empty() && !RestoreSessions(st, restore, dropLevels))
				{
					rebuild = true;
					continue;
				}
			}
			if (RunLoad(sc, st, reader, from) == LR_OK)
				break;
			rebuild = true;
			if (attempt == 1)
				st.Built = false;	// try again on the next call
		}
		reader.Release();
		st.Reads += reader.Reads;

		// The per-bar values wait for the sessions to be shown, as the drawing and the label do;
		// a rebuild clears them meanwhile, so no marker shows the values of other inputs.
		st.ValuesFrom = (std::min)(st.ValuesFrom, valuesFrom);
		if (Showing(st))
		{
			WriteValues(sc, st, st.ValuesFrom);
			st.ValuesFrom = INT_MAX;
		}
		else
		{
			if (valuesFrom == 0)
				for (int i = 0; i < sc.ArraySize; i++)
					sc.Subgraph[SG_POC][i] = sc.Subgraph[SG_VAH][i] = sc.Subgraph[SG_VAL][i] = 0.0f;
			st.Written.clear();
		}
		UpdateSnapshots(st);
		// Shown while no session can be drawn: reading the tick file, waiting for Sierra Chart's
		// volume at price (no tick reading at all with the Volume at price option or non-tick
		// storage), every session from volume at price but no bar starting in a window, or none of
		// these: no trades in the window.
		const bool noBarStarts = st.AllVapReason >= 0 && st.Engine.Sessions.empty() && !AnyBarStartsInWindow(st.Windows, st.Bars);
		st.Message = ReadingTicks(st) ? MSG_READING : st.VapWaiting ? MSG_WAITING_VAP : noBarStarts ? MSG_NO_BAR_STARTS : MSG_NO_TICKS;
		LogFallbacks(sc, st);
	}

	// ---- Translucent histogram boxes (spec D.6) ----

	// On a full recalculation Sierra Chart has already deleted the study's ranges.
	void ForgetRangesOnFullRecalculation(SCStudyInterfaceRef sc, StudyState& st)
	{
		if (!sc.IsFullRecalculation)
			return;
		st.Sent.clear();
		st.RangesKey = 0;
	}

	void DeleteRanges(SCStudyInterfaceRef sc, StudyState& st)
	{
		ForgetRangesOnFullRecalculation(sc, st);
		for (const auto& entry : st.Sent)
		{
			sc.DeleteLineUntilFutureIntersection((int)(uint32_t)(entry.first >> 32), (int)(uint32_t)(entry.first & 0xFFFFFFFFu));
			st.RangeDeletes++;
		}
		st.Sent.clear();
		st.RangesKey = 0;
	}

	uint32_t BoxSignature(const BoxPiece& b, uint32_t color, int transparency)
	{
		const double values[2] = {b.Top, b.Bottom};
		const int64_t numbers[3] = {b.EndBar, color, transparency};
		return Fnv1a(Fnv1a(2166136261u, values, sizeof(values)), numbers, sizeof(numbers));
	}

	// A translucent box in SessionRight is a Sierra Chart range per session (TatankaTpoProfile's
	// translucent boxes): bars show through it, and the study's rows and lines are drawn over it.
	// Only ranges that changed are sent; none at all in ChartRightLatest, at opacity 0 or 100, or
	// while hidden (the callback draws those).
	void UpdateBoxRanges(SCStudyInterfaceRef sc, StudyState& st)
	{
		ForgetRangesOnFullRecalculation(sc, st);
		const int opacity	= (std::max)(0, (std::min)(100, sc.Input[IN_BOX_OPACITY].GetInt()));
		const bool pinned	= sc.Input[IN_PLACEMENT].GetIndex() == PL_CHART_RIGHT_LATEST;
		if (sc.HideStudy || !st.Built || !st.Error.empty() || pinned || opacity <= 0 || opacity >= 100)
		{
			DeleteRanges(sc, st);
			return;
		}
		const std::vector<BoxPiece> desired	= BoxPieces(st.Drawn, st.Bars.S, st.Bars.E);
		const uint32_t color				= sc.Input[IN_BOX_COLOR].GetColor();
		const int transparency				= 100 - opacity;
		uint32_t key = Fnv1a(2166136261u, &color, sizeof(color));
		key = Fnv1a(key, &transparency, sizeof(transparency));
		for (const BoxPiece& b : desired)
		{
			const uint32_t signature = BoxSignature(b, color, transparency);
			key = Fnv1a(Fnv1a(key, &b.StartBar, sizeof(b.StartBar)), &signature, sizeof(signature));
		}
		key = key == 0 ? 1 : key;
		if (key == st.RangesKey)
			return;

		auto wanted = [&desired](uint64_t rangeKey)
		{
			const auto found = std::lower_bound(desired.begin(), desired.end(), rangeKey,
				[](const BoxPiece& b, uint64_t k) { return RangeKey(b.StartBar, b.Id) < k; });
			return found != desired.end() && RangeKey(found->StartBar, found->Id) == rangeKey;
		};
		for (auto it = st.Sent.begin(); it != st.Sent.end();)
		{
			if (wanted(it->first))
			{
				++it;
				continue;
			}
			sc.DeleteLineUntilFutureIntersection((int)(uint32_t)(it->first >> 32), (int)(uint32_t)(it->first & 0xFFFFFFFFu));
			st.RangeDeletes++;
			it = st.Sent.erase(it);
		}
		for (const BoxPiece& b : desired)
		{
			const uint32_t signature = BoxSignature(b, color, transparency);
			uint32_t& sent = st.Sent[RangeKey(b.StartBar, b.Id)];
			if (sent == signature)
				continue;
			n_ACSIL::s_LineUntilFutureIntersection line;
			line.StartBarIndex					= b.StartBar;
			line.EndBarIndex					= b.EndBar;	// > 0: the range stops there and never extends
			line.LineIDForBar					= b.Id;
			line.LineValue						= (float)b.Top;
			line.UseLineValue2					= 1;
			line.LineValue2ForRange				= (float)b.Bottom;
			line.LineColor						= color;
			line.LineWidth						= 0;
			line.LineStyle						= 0;
			line.DrawValueLabel					= 0;
			line.DrawNameLabel					= 0;
			line.AlwaysExtendToEndOfChart		= 0;
			line.TransparencyLevel				= transparency;
			line.PerformCloseCrossoverComparison = 0;
			sc.AddLineUntilFutureIntersectionEx(line);
			st.RangeAdds++;
			sent = signature;
		}
		st.RangesKey = key;
	}

	// ---- Rendering helpers (TatankaTpoProfile.cpp) ----

	// The drawing callback has no transparency: a translucent color is blended over the chart
	// background instead.
	uint32_t Blend(uint32_t color, double opacity, uint32_t background)
	{
		opacity = (std::max)(0.0, (std::min)(1.0, opacity));
		auto mix = [opacity](int c, int b) { return (int)(c * opacity + b * (1.0 - opacity) + 0.5); };
		return RGB(mix(GetRValue(color), GetRValue(background)),
			mix(GetGValue(color), GetGValue(background)),
			mix(GetBValue(color), GetBValue(background)));
	}

	n_ACSIL::s_GraphicsColor GraphicsColor(uint32_t colorref)
	{
		n_ACSIL::s_GraphicsColor color;
		color.SetColorValue(colorref);
		return color;
	}

	void FillRect(SCStudyInterfaceRef sc, int left, int top, int right, int bottom, uint32_t colorref)
	{
		if (right <= left || bottom <= top)
			return;
		n_ACSIL::s_GraphicsRectangle rect;
		rect.Left	= left;
		rect.Top	= top;
		rect.Right	= right;
		rect.Bottom	= bottom;
		sc.Graphics.FillRectangleWithColor(rect, GraphicsColor(colorref));
	}

	// The chart region in pixels (NinjaTrader's ChartPanel, the price scale excluded), the DIP
	// scale and the chart background.
	struct Canvas
	{
		int			Left		= 0;
		int			Top			= 0;
		int			Right		= 0;
		int			Bottom		= 0;
		double		Scale		= 1;
		uint32_t	Background	= 0;

		int Dip(double dips) const { return (int)std::floor(dips * Scale + 0.5); }
		int Stroke(double dips) const { return (std::max)(1, Dip(dips)); }
	};

	// NinjaTrader lays everything out in DIPs (1/96 inch), so its paddings and line widths
	// grow on a scaled display. This is that scale: the window's DPI, or, when the window
	// reports 96 on a scaled display, how much wider the selected font drew a long line than
	// GetTextSizeWithFont measured it. Call after SetTextFont(font).
	double DipScale(SCStudyInterfaceRef sc, const n_ACSIL::s_GraphicsFont& font)
	{
		const int dpi = sc.Graphics.GetDeviceCaps(LOGPIXELSY);
		if (dpi > 96)
			return (std::min)(4.0, dpi / 96.0);

		const SCString sample("ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789");
		n_ACSIL::s_GraphicsSize selected, withFont;
		sc.Graphics.GetTextSize(sample, selected);
		sc.Graphics.GetTextSizeWithFont(sample, font, withFont);
		const double fromText = withFont.Width > 0 ? std::floor(4.0 * selected.Width / withFont.Width + 0.5) / 4.0 : 1.0;
		return (std::max)(1.0, (std::min)(4.0, fromText));
	}

	// Text size in the drawing font. Call after sc.Graphics.SetTextFont(font): GetTextSize
	// measures the selected font in the chart window, which is what DrawTextAt draws with.
	// GetTextSizeWithFont alone can come back several times too small on a scaled
	// (high-DPI) display, so the larger of the two is used.
	n_ACSIL::s_GraphicsSize MeasureLine(SCStudyInterfaceRef sc, const n_ACSIL::s_GraphicsFont& font, const std::string& text)
	{
		const SCString value(text.c_str());
		n_ACSIL::s_GraphicsSize selected, withFont;
		sc.Graphics.GetTextSize(value, selected);
		sc.Graphics.GetTextSizeWithFont(value, font, withFont);
		selected.Width	= (std::max)(selected.Width, withFont.Width);
		selected.Height	= (std::max)(selected.Height, withFont.Height);
		return selected;
	}

	int LineHeight(SCStudyInterfaceRef sc, const n_ACSIL::s_GraphicsFont& font)
	{
		return (std::max)(1, (std::max)(MeasureLine(sc, font, "Ag").Height, (int)sc.Graphics.GetTextHeight()));
	}

	int PriceY(SCStudyInterfaceRef sc, double price)
	{
		return sc.RegionValueToYPixelCoordinate((float)price, sc.GraphRegion);
	}

	// A bar's center; past the last loaded bar (the right-side fill space) and before bar 0,
	// one bar spacing per bar.
	int BarX(SCStudyInterfaceRef sc, int index)
	{
		const int last = sc.ArraySize - 1;
		if (last < 0 || (index >= 0 && index <= last))
			return sc.BarIndexToXPixelCoordinate(index);
		const int anchor	= index > last ? last : 0;
		const int x			= sc.BarIndexToXPixelCoordinate(anchor);
		const int step		= last > 0 ? sc.BarIndexToXPixelCoordinate(1) - sc.BarIndexToXPixelCoordinate(0) : (int)sc.ChartBarSpacing;
		const int64_t value	= (int64_t)x + (int64_t)(index - anchor) * (std::max)(1, step);
		return (int)(std::max)((int64_t)INT_MIN / 2, (std::min)((int64_t)INT_MAX / 2, value));
	}

	using TextMeasure = std::function<int(const std::string&)>;

	// Greedy word wrap at spaces: a line breaks before the word that would overflow it, and a
	// word wider than the width stays whole.
	std::vector<std::string> WrapWords(const std::string& text, int maxWidth, const TextMeasure& measure)
	{
		std::vector<std::string> lines;
		std::string rest = text;
		auto trimmed = [](const std::string& s, size_t length)
		{
			const size_t last = s.find_last_not_of(' ', length == 0 ? 0 : length - 1);
			return last == std::string::npos || length == 0 ? std::string() : s.substr(0, last + 1);
		};
		while (!rest.empty() && measure(rest) > maxWidth)
		{
			size_t cut = std::string::npos;
			for (size_t space = rest.find(' '); space != std::string::npos; space = rest.find(' ', space + 1))
			{
				const std::string head = trimmed(rest, space);
				if (head.empty())
					continue;
				if (measure(head) > maxWidth)
				{
					if (cut == std::string::npos)
						cut = space;  // the first word alone is too wide: it stays whole
					break;
				}
				cut = space;
			}
			if (cut == std::string::npos)
				break;
			lines.push_back(trimmed(rest, cut));
			const size_t next = rest.find_first_not_of(' ', cut);
			rest = next == std::string::npos ? std::string() : rest.substr(next);
		}
		if (!rest.empty() || lines.empty())
			lines.push_back(rest);
		return lines;
	}

	// ---- Drawing callback (spec D) ----

	// NinjaTrader's SimpleFont("Segoe UI", 11) (NT:269): 11 DIPs = 8.25 points, 8.
	n_ACSIL::s_GraphicsFont ProfileFont()
	{
		n_ACSIL::s_GraphicsFont font;
		font.m_FaceName	= "Segoe UI";
		font.m_Height	= 8;
		font.m_Weight	= FW_NORMAL;
		return font;
	}

	// The display inputs, read once per frame.
	struct DisplaySettings
	{
		bool		Pinned			= false;
		bool		ShowProfile		= true;
		bool		RowVolumes		= false;
		bool		Show[3]			= {true, true, true};		// POC, VAH, VAL
		bool		Extend[3]		= {false, false, false};
		bool		Labels			= false;
		int			Padding			= 12;
		int			RowGap			= 1;
		int			LineWidth		= 1;
		int			BoxOpacity		= 0;
		double		WidthPercent	= 20;
		uint32_t	Up				= 0;
		uint32_t	Down			= 0;
		uint32_t	VaUp			= 0;
		uint32_t	VaDown			= 0;
		uint32_t	VaLine			= 0;
		uint32_t	PocLine			= 0;
		uint32_t	Text			= 0;
		uint32_t	Box				= 0;
	};

	DisplaySettings ReadDisplay(SCStudyInterfaceRef sc)
	{
		DisplaySettings d;
		d.Pinned		= sc.Input[IN_PLACEMENT].GetIndex() == PL_CHART_RIGHT_LATEST;
		d.ShowProfile	= sc.Input[IN_SHOW_PROFILE].GetYesNo() != 0;
		d.RowVolumes	= sc.Input[IN_ROW_VOLUMES].GetYesNo() != 0;
		const int shows[3]		= {IN_SHOW_POC, IN_SHOW_VAH, IN_SHOW_VAL};
		const int extends[3]	= {IN_EXTEND_POC, IN_EXTEND_VAH, IN_EXTEND_VAL};
		for (int k = 0; k < 3; k++)
		{
			d.Show[k]	= sc.Input[shows[k]].GetYesNo() != 0;
			d.Extend[k]	= sc.Input[extends[k]].GetYesNo() != 0;
		}
		d.Labels		= sc.Input[IN_LEVEL_LABELS].GetYesNo() != 0;
		d.Padding		= (std::max)(0, (std::min)(500, sc.Input[IN_PADDING].GetInt()));
		d.RowGap		= (std::max)(0, (std::min)(5, sc.Input[IN_ROW_GAP].GetInt()));
		d.LineWidth		= (std::max)(1, (std::min)(5, sc.Input[IN_LINE_WIDTH].GetInt()));
		d.BoxOpacity	= (std::max)(0, (std::min)(100, sc.Input[IN_BOX_OPACITY].GetInt()));
		d.WidthPercent	= (std::max)(1.0, (std::min)(100.0, sc.Input[IN_WIDTH].GetDouble()));
		d.Up			= sc.Input[IN_UP_COLOR].GetColor();
		d.Down			= sc.Input[IN_DOWN_COLOR].GetColor();
		d.VaUp			= sc.Input[IN_VA_UP_COLOR].GetColor();
		d.VaDown		= sc.Input[IN_VA_DOWN_COLOR].GetColor();
		d.VaLine		= sc.Input[IN_VA_LINE_COLOR].GetColor();
		d.PocLine		= sc.Input[IN_POC_LINE_COLOR].GetColor();
		d.Text			= sc.Input[IN_TEXT_COLOR].GetColor();
		d.Box			= sc.Input[IN_BOX_COLOR].GetColor();
		return d;
	}

	// The text font, its line height and the current text color (set only when it changes).
	struct TextPainter
	{
		n_ACSIL::s_GraphicsFont	Font;
		int						LineHeight	= 1;
		uint32_t				Color		= 0;
		bool					HasColor	= false;

		// NinjaTrader's DrawText in a layout box at (x, y) maxWidth wide: word-wrapped, top-left
		// aligned, not clipped.
		void Draw(SCStudyInterfaceRef sc, const std::string& text, int x, int y, int maxWidth, uint32_t color)
		{
			if (!HasColor || Color != color)
			{
				sc.Graphics.SetTextColor(GraphicsColor(color));
				Color		= color;
				HasColor	= true;
			}
			const TextMeasure measure = [&sc, this](const std::string& t) { return MeasureLine(sc, Font, t).Width; };
			const std::vector<std::string> lines = WrapWords(text, (std::max)(1, maxWidth), measure);
			for (size_t i = 0; i < lines.size(); i++)
				if (!lines[i].empty())
					sc.Graphics.DrawTextAt(SCString(lines[i].c_str()), x, y + (int)i * LineHeight);
		}
	};

	// A level line (NT:344-358, spec D.7): from lineLeft to the profile's anchor or, extended, to
	// the panel's right edge, LineWidth DIPs centered on the price's pixel row; and on the newest
	// session its name and price above the line, in the line's color.
	void DrawLevel(SCStudyInterfaceRef sc, const Canvas& c, TextPainter& text, double price, const char* name, double lineLeft, double right,
		bool extend, int lineWidth, uint32_t color, bool label)
	{
		const int y = PriceY(sc, price);
		if (y < c.Top || y > c.Bottom)
			return;
		const double end = extend ? (double)c.Right : right;
		if (end >= c.Left && lineLeft <= c.Right)
		{
			const int width = c.Stroke(lineWidth);
			FillRect(sc, (std::max)(c.Left, PixEdge(lineLeft)), y - width / 2, (std::min)(c.Right, PixEdge(end)), y - width / 2 + width, color);
		}
		if (label)
		{
			const double x = LevelLabelX(c.Left, c.Right, right, [&c](double dips) { return c.Dip(dips); });
			text.Draw(sc, std::string(name) + " " + Price(sc, price), (int)RoundHalfUp(x), y - c.Dip(15), c.Dip(110), color);
		}
	}

	// One session (NT:295-337): the box, the rows (up, down, row text), VAH, VAL, POC.
	void DrawSession(SCStudyInterfaceRef sc, const Canvas& c, const DisplaySettings& d, TextPainter& text, const VpSnapshot& p, const BarTable& bars,
		double tick, bool newest)
	{
		auto center = [&sc](int i) { return BarX(sc, i); };
		const int64_t edge		= EdgeTime(p.LastChart, p.EndChart, bars.E.back());
		const int sessionLeft	= PositionX(EndPosition(bars.S, bars.E, p.StartChart), center);
		const int sessionRight	= PositionX(EndPosition(bars.S, bars.E, edge), center);
		const SessionLayout l	= LayoutSession(d.Pinned, sessionLeft, sessionRight, c.Left, c.Right, d.Padding, d.WidthPercent, c.Scale);
		const ProfileStats& s	= p.Stats;

		// The box (NT:306-309): opaque, or translucent where no range draws it (ChartRightLatest,
		// or a session within one bar), blended with the chart background.
		int startBar = 0, endBar = 0;
		if (d.BoxOpacity > 0 && (d.BoxOpacity >= 100 || d.Pinned || !BoxBars(p, bars.S, bars.E, startBar, endBar)))
		{
			const int yTop = PriceY(sc, s.HighEdge), yBottom = PriceY(sc, s.LowEdge);
			const uint32_t color = d.BoxOpacity >= 100 ? d.Box : Blend(d.Box, d.BoxOpacity / 100.0, c.Background);
			FillRect(sc, PixEdge(l.BoxLeft), (std::min)(yTop, yBottom), PixEdge(l.BoxRight), (std::max)(yTop, yBottom), color);
		}

		if (d.ShowProfile && s.MaxVolume > 0)
		{
			int64_t previousKey	= INT64_MIN;
			int previousHigh	= 0;
			for (const ProfileRow& row : p.Rows)
			{
				const int yLow	= row.Key == previousKey + 1 ? previousHigh : PriceY(sc, EdgePrice(row.Key, s.RowSize, tick));
				const int yHigh	= PriceY(sc, EdgePrice(row.Key + 1, s.RowSize, tick));
				previousKey		= row.Key;
				previousHigh	= yHigh;
				const RowLayout r = LayoutRow(yHigh, yLow, c.Top, c.Bottom, l.Right, l.Width, row.Up, row.Down, s.MaxVolume, d.RowGap, c.Scale);
				if (!r.Visible)
					continue;
				const bool inVa	= row.Key >= s.ValKey && row.Key <= s.VahKey;
				const int y0	= PixEdge(r.Y);
				const int y1	= PixEdge(r.Y + r.H);
				if (r.UpWidth > 0)
					FillRect(sc, PixEdge(r.Left), y0, PixEdge(r.Left + r.UpWidth), y1, inVa ? d.VaUp : d.Up);
				if (r.DownWidth > 0)
					FillRect(sc, PixEdge(l.Right - r.DownWidth), y0, PixEdge(l.Right), y1, inVa ? d.VaDown : d.Down);
				if (d.RowVolumes && r.Full >= 12 * c.Scale && r.UpWidth + r.DownWidth >= 60 * c.Scale)
					text.Draw(sc, FormatNet(row.Up, 0) + " / " + FormatNet(row.Down, 0), (int)RoundHalfUp(r.Left) + c.Dip(3), (int)RoundHalfUp(r.Y),
						(int)(r.UpWidth + r.DownWidth - 3 * c.Scale), d.Text);
			}
		}

		const bool labels = d.Labels && newest;
		if (d.Show[1])
			DrawLevel(sc, c, text, s.Vah, "VAH", l.LineLeft, l.Right, d.Extend[1], d.LineWidth, d.VaLine, labels);
		if (d.Show[2])
			DrawLevel(sc, c, text, s.Val, "VAL", l.LineLeft, l.Right, d.Extend[2], d.LineWidth, d.VaLine, labels);
		if (d.Show[0])
			DrawLevel(sc, c, text, s.Poc, "POC", l.LineLeft, l.Right, d.Extend[0], d.LineWidth, d.PocLine, labels);
	}

	// Which sessions are drawn (NT:285-293, spec D.2): SessionRight every retained session that
	// meets the visible bars; ChartRightLatest only the newest, unless the view is scrolled back
	// before it began.
	void DrawProfiles(SCStudyInterfaceRef sc, const Canvas& c, const StudyState& st, TextPainter& text)
	{
		const DisplaySettings d	= ReadDisplay(sc);
		const BarTable& bars	= st.Bars;
		const int n				= bars.Count();
		const int firstVisible	= (std::max)(0, (std::min)(n - 1, sc.IndexOfFirstVisibleBar));
		const int lastVisible	= (std::max)(0, (std::min)(n - 1, sc.IndexOfLastVisibleBar));
		const int64_t visibleFirst	= bars.E[(size_t)firstVisible];
		const int64_t visibleLast	= bars.E[(size_t)lastVisible];
		const int count = (int)st.Drawn.size();
		for (int k = 0; k < count; k++)
		{
			const VpSnapshot* p = st.Drawn[(size_t)k];
			if (p == nullptr || !p->Valid || p->Rows.empty())
				continue;
			if (d.Pinned && (k != count - 1 || visibleLast < p->StartChart))
				continue;
			if (!d.Pinned && (p->EndChart < visibleFirst || p->StartChart > visibleLast))
				continue;
			DrawSession(sc, c, d, text, *p, bars, st.Engine.Cfg.Tick, k == count - 1);
		}
	}

	void DrawSessionVolumeProfile(HWND, HDC, SCStudyInterfaceRef sc)
	{
		const StudyState* state = PeekState(sc);
		if (sc.HideStudy || state == nullptr)
			return;

		Canvas c;
		c.Left		= sc.StudyRegionLeftCoordinate;
		c.Top		= sc.StudyRegionTopCoordinate;
		c.Right		= sc.StudyRegionRightCoordinate;
		c.Bottom	= sc.StudyRegionBottomCoordinate;
		if (c.Right <= c.Left || c.Bottom <= c.Top)
			return;

		TextPainter text;
		text.Font = ProfileFont();
		sc.Graphics.SetTextFont(text.Font);  // before any measuring: see MeasureLine
		c.Scale			= DipScale(sc, text.Font);
		text.LineHeight	= LineHeight(sc, text.Font);
		uint32_t unusedWidth = 0;
		SubgraphLineStyles unusedStyle = LINESTYLE_SOLID;
		sc.GetGraphicsSetting(sc.ChartNumber, n_ACSIL::GRAPHICS_SETTING_CHART_BACKGROUND, c.Background, unusedWidth, unusedStyle);

		n_ACSIL::s_GraphicsRectangle clip;
		clip.Left	= c.Left;
		clip.Top	= c.Top;
		clip.Right	= c.Right;
		clip.Bottom	= c.Bottom;
		sc.Graphics.SetClippingRegionFromRectangle(clip);
		sc.Graphics.SetBackgroundMode(TRANSPARENT);
		sc.Graphics.SetTextAlign(TA_NOUPDATECP | TA_LEFT | TA_TOP);

		// A configuration error or no session: the message alone (NT:276-282), at 12, 35 DIPs.
		const std::string message = !state->Error.empty() ? state->Error : HasDrawable(*state) && state->Bars.Count() > 0 ? std::string()
			: state->Message.empty() ? std::string(MSG_NO_TICKS) : state->Message;
		if (!message.empty())
			text.Draw(sc, message, c.Left + c.Dip(12), c.Top + c.Dip(35), (int)(std::max)(100 * c.Scale, c.Right - c.Left - 24 * c.Scale),
				sc.Input[IN_TEXT_COLOR].GetColor());
		else
			DrawProfiles(sc, c, *state, text);

		sc.Graphics.ResetTextAlign();
		sc.Graphics.ResetBackgroundMode();
		sc.Graphics.ResetTextColor();
		sc.Graphics.ResetClippingRegion();
		sc.Graphics.ResetTextFont();
	}
}

SCSFExport scsf_TatankaSessionVolumeProfile(SCStudyInterfaceRef sc)
{
	if (sc.SetDefaults)
	{
		sc.GraphName		= "Tatanka Session Volume Profile";
		sc.GraphShortName	= "";
		sc.StudyDescription	= "Tatanka Session Volume Profile v1.0.0: right-aligned volume profiles for a custom session window, built from "
							  "every trade, with POC, value area and up/down volume. Needs tick-by-tick data (Intraday Data Storage Time "
							  "Unit = 1 Tick). Free and open source (MPL 2.0). tatankatrading.com";
		sc.GraphRegion		= 0;
		sc.AutoLoop			= 0;
		sc.ValueFormat		= VALUEFORMAT_INHERITED;
		sc.ScaleRangeType	= SCALE_SAMEASREGION;
		sc.DisplayStudyName	= 1;
		sc.DisplayStudyInputValues				= 0;	// the chart label carries NinjaTrader's chosen inputs
		sc.DrawStudyUnderneathMainPriceGraph	= 0;	// over the bars, as NinjaTrader draws
		sc.UpdateAlways		= 0;
		// Tick, volume and range bars end at their last trade (NinjaTrader's close stamp), from
		// sc.BaseDataEndDateTime, which Sierra Chart keeps only when this is set here.
		sc.MaintainAdditionalChartDataArrays	= 1;
		// Volume at price: the fallback for sessions not stored as ticks, and the third Volume
		// data option, available without a chart reload.
		sc.MaintainVolumeAtPriceData			= 1;

		// NinjaTrader's PriceBox plots (NT:95-98): a value label in the price scale, no line.
		const char* const names[3] = {"POC", "VAH", "VAL"};
		const uint32_t colors[3] = {RGB(183, 157, 214), RGB(237, 20, 97), RGB(237, 20, 97)};
		for (int k = 0; k < 3; k++)
		{
			SCSubgraphRef g = sc.Subgraph[k];
			g.Name				= names[k];
			g.DrawStyle			= DRAWSTYLE_SUBGRAPH_NAME_AND_VALUE_LABELS_ONLY;
			g.PrimaryColor		= colors[k];
			g.LineWidth			= 1;
			g.DrawZeros			= 0;
			g.LineLabel			= LL_DISPLAY_VALUE | LL_VALUE_ALIGN_VALUES_SCALE | LL_VALUE_ALIGN_CENTER;
			g.DisplayNameValueInWindowsFlags = SNV_DISPLAY_IN_WINDOWS;
		}

		sc.Input[IN_SESSION_START].Name = "Session start";
		sc.Input[IN_SESSION_START].SetTime(30600);
		sc.Input[IN_SESSION_START].SetDescription("In the Session time zone. The start is included.");

		sc.Input[IN_SESSION_END].Name = "Session end";
		sc.Input[IN_SESSION_END].SetTime(54000);
		sc.Input[IN_SESSION_END].SetDescription("Excluded. Earlier than the start = overnight window; equal = 24 hours.");

		sc.Input[IN_TIME_ZONE].Name = "Session time zone";
		sc.Input[IN_TIME_ZONE].SetCustomInputStrings("ExchangeTemplate;Central;Eastern;Chart;UTC");
		sc.Input[IN_TIME_ZONE].SetCustomInputIndex(TZO_EXCHANGE);
		sc.Input[IN_TIME_ZONE].SetDescription("ExchangeTemplate = America/Chicago here (Sierra Chart has no trading-hours time zone; right for "
			"CME, CBOT, NYMEX, COMEX). Central/Eastern = Chicago/New York with daylight saving. Chart = this chart's time zone.");

		sc.Input[IN_VA_PERCENT].Name = "Value area volume (%)";
		sc.Input[IN_VA_PERCENT].SetDouble(68);
		sc.Input[IN_VA_PERCENT].SetDoubleLimits(1, 100);

		sc.Input[IN_VA_METHOD].Name = "Value area method";
		sc.Input[IN_VA_METHOD].SetCustomInputStrings("TradingViewStyle;AtLeastTarget");
		sc.Input[IN_VA_METHOD].SetCustomInputIndex(VAM_TRADINGVIEW);
		sc.Input[IN_VA_METHOD].SetDescription("TradingViewStyle stops before the next row exceeds the target. AtLeastTarget includes that row.");

		sc.Input[IN_TICKS_PER_ROW].Name = "Ticks per row";
		sc.Input[IN_TICKS_PER_ROW].SetInt(1);
		sc.Input[IN_TICKS_PER_ROW].SetIntLimits(1, 1000);

		sc.Input[IN_SESSIONS].Name = "Sessions to retain";
		sc.Input[IN_SESSIONS].SetInt(20);
		sc.Input[IN_SESSIONS].SetIntLimits(1, 100);
		sc.Input[IN_SESSIONS].SetDescription("Days to Load still limits how many there are.");

		sc.Input[IN_VOLUME_DATA].Name = "Volume data";
		sc.Input[IN_VOLUME_DATA].SetCustomInputStrings("Trades: tick rule (NinjaTrader);Trades: bid/ask;Volume at price: bid/ask (fastest)");
		sc.Input[IN_VOLUME_DATA].SetCustomInputIndex(VD_TICK_RULE);
		sc.Input[IN_VOLUME_DATA].SetDescription("Trades need Intraday Data Storage Time Unit = 1 Tick. Tick rule: a trade above the previous one "
			"is up, below is down, unchanged keeps the direction. Bid/ask: trades at the ask are up, at the bid down. Volume at price: from "
			"each bar's volume at price, whole bars by their start time (exact on bars that divide the session, for example 30 Minute "
			"for 08:30-15:00).");

		sc.Input[IN_PLACEMENT].Name = "Placement";
		sc.Input[IN_PLACEMENT].SetCustomInputStrings("SessionRight;ChartRightLatest");
		sc.Input[IN_PLACEMENT].SetCustomInputIndex(PL_SESSION_RIGHT);

		sc.Input[IN_WIDTH].Name = "Width (% of session / chart)";
		sc.Input[IN_WIDTH].SetDouble(20);
		sc.Input[IN_WIDTH].SetDoubleLimits(1, 100);

		sc.Input[IN_PADDING].Name = "Chart-right padding (pixels)";
		sc.Input[IN_PADDING].SetInt(12);
		sc.Input[IN_PADDING].SetIntLimits(0, 500);
		sc.Input[IN_PADDING].SetDescription("ChartRightLatest only. In 1/96 inch: scaled on high-DPI displays.");

		sc.Input[IN_ROW_GAP].Name = "Row gap (pixels)";
		sc.Input[IN_ROW_GAP].SetInt(1);
		sc.Input[IN_ROW_GAP].SetIntLimits(0, 5);
		sc.Input[IN_ROW_GAP].SetDescription("At most 35 % of a row.");

		sc.Input[IN_SHOW_PROFILE].Name = "Volume profile";
		sc.Input[IN_SHOW_PROFILE].SetYesNo(1);

		sc.Input[IN_ROW_VOLUMES].Name = "Row volumes (up / down)";
		sc.Input[IN_ROW_VOLUMES].SetYesNo(0);
		sc.Input[IN_ROW_VOLUMES].SetDescription("Shown on rows at least 12 by 60 (1/96 inch).");

		sc.Input[IN_SHOW_POC].Name = "POC";
		sc.Input[IN_SHOW_POC].SetYesNo(1);
		sc.Input[IN_SHOW_VAH].Name = "VAH";
		sc.Input[IN_SHOW_VAH].SetYesNo(1);
		sc.Input[IN_SHOW_VAL].Name = "VAL";
		sc.Input[IN_SHOW_VAL].SetYesNo(1);

		sc.Input[IN_EXTEND_POC].Name = "Extend POC to chart edge";
		sc.Input[IN_EXTEND_POC].SetYesNo(0);
		sc.Input[IN_EXTEND_VAH].Name = "Extend VAH to chart edge";
		sc.Input[IN_EXTEND_VAH].SetYesNo(0);
		sc.Input[IN_EXTEND_VAL].Name = "Extend VAL to chart edge";
		sc.Input[IN_EXTEND_VAL].SetYesNo(0);

		sc.Input[IN_LINE_WIDTH].Name = "Line width";
		sc.Input[IN_LINE_WIDTH].SetInt(1);
		sc.Input[IN_LINE_WIDTH].SetIntLimits(1, 5);

		sc.Input[IN_LEVEL_LABELS].Name = "Level name labels";
		sc.Input[IN_LEVEL_LABELS].SetYesNo(0);

		sc.Input[IN_INPUTS_IN_LABEL].Name = "Inputs in chart label";
		sc.Input[IN_INPUTS_IN_LABEL].SetYesNo(1);

		sc.Input[IN_VALUES_IN_LABEL].Name = "Values in chart label";
		sc.Input[IN_VALUES_IN_LABEL].SetYesNo(1);

		sc.Input[IN_UP_COLOR].Name = "Up volume";
		sc.Input[IN_UP_COLOR].SetColor(RGB(80, 85, 97));		// #505561
		sc.Input[IN_DOWN_COLOR].Name = "Down volume";
		sc.Input[IN_DOWN_COLOR].SetColor(RGB(80, 85, 97));		// #505561, the same as up (NT:86-87)
		sc.Input[IN_VA_UP_COLOR].Name = "Value area up";
		sc.Input[IN_VA_UP_COLOR].SetColor(RGB(200, 11, 91));	// #C80B5B
		sc.Input[IN_VA_DOWN_COLOR].Name = "Value area down";
		sc.Input[IN_VA_DOWN_COLOR].SetColor(RGB(235, 20, 96));	// #EB1460
		sc.Input[IN_VA_LINE_COLOR].Name = "VAH / VAL";
		sc.Input[IN_VA_LINE_COLOR].SetColor(RGB(237, 20, 97));	// #ED1461
		// NinjaTrader names this one "POC" too; two inputs named POC would be ambiguous here.
		sc.Input[IN_POC_LINE_COLOR].Name = "POC line";
		sc.Input[IN_POC_LINE_COLOR].SetColor(RGB(183, 157, 214));	// #B79DD6
		sc.Input[IN_TEXT_COLOR].Name = "Text";
		sc.Input[IN_TEXT_COLOR].SetColor(RGB(211, 211, 211));	// LightGray
		sc.Input[IN_BOX_COLOR].Name = "Histogram box";
		sc.Input[IN_BOX_COLOR].SetColor(RGB(255, 255, 255));

		// Sierra Chart colors have no alpha; NinjaTrader's default box is Transparent.
		sc.Input[IN_BOX_OPACITY].Name = "Histogram box opacity (%)";
		sc.Input[IN_BOX_OPACITY].SetInt(0);
		sc.Input[IN_BOX_OPACITY].SetIntLimits(0, 100);
		sc.Input[IN_BOX_OPACITY].SetDescription("0 = none (NinjaTrader's Transparent default), 100 = solid.");

		return;
	}

	if (sc.LastCallToFunction)
	{
		// The study is removed (or the chart closed): its ranges and its state go with it.
		if (StudyState* state = PeekState(sc))
			DeleteRanges(sc, *state);
		DeleteState(sc);
		return;
	}

	// Set on every call, after SetDefaults, so it survives a DLL reload.
	sc.p_GDIFunction = DrawSessionVolumeProfile;

	StudyState& state = GetState(sc);
	n_ACSIL::s_BarPeriod barPeriod;
	sc.GetBarPeriodParameters(barPeriod);
	const bool timeBased = barPeriod.IntradayChartBarPeriodType == IBPT_DAYS_MINS_SECS;
	state.Error = ConfigError(barPeriod.ChartDataType, barPeriod.IntradayChartBarPeriodType, sc.SecondsPerBar,
		sc.BaseDataEndDateTime.GetArraySize() >= sc.ArraySize, DecimalTickSize(sc.TickSize));
	// Logged once per error (NinjaTrader prints it once per load, NT:145): again only when it changes.
	int& logged = sc.GetPersistentInt(PI_ERROR_LOGGED);
	const int errorKey = state.Error.empty() ? 0 : (int)(Fnv1a(2166136261u, state.Error.data(), state.Error.size()) | 1u);
	if (errorKey != 0 && errorKey != logged)
		sc.AddMessageToLog(("Tatanka Session Volume Profile: " + state.Error).c_str(), 0);
	logged = errorKey;

	UpdateSubgraphs(sc);
	if (!state.Error.empty())
	{
		// Only the message is drawn. Once the cause is gone the engine is rebuilt from bar 0.
		state.ResetEngine();
		DeleteRanges(sc, state);
		sc.UpdateAlways = 0;
	}
	else
	{
		// Hidden (sc.HideStudy) still processes, so showing the study again draws at once;
		// UpdateBoxRanges then removes the ranges and the callback draws nothing.
		ProcessCall(sc, state, timeBased);
		UpdateBoxRanges(sc, state);
		// Sierra Chart calls again at the chart update interval while tick data is still to be
		// read or volume at price is not built yet (spec C.7).
		sc.UpdateAlways = state.Pending ? 1 : 0;
	}
	UpdateLabel(sc, &state);
}

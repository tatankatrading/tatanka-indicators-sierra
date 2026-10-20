// Copyright (c) 2026 Tatanka Trading LLC.
// This Source Code Form is subject to the Mozilla Public License, v. 2.0.
// If a copy of the MPL was not distributed with this file, obtain one at https://mozilla.org/MPL/2.0/.
// Tatanka Periodic Volume Profile v1.0.0 for Sierra Chart - tatankatrading.com
// Sierra Chart port of the NinjaTrader 8 "Periodic Volume Profile" (chart label "Tatanka PVP").
//
// Daily, weekly, monthly or yearly volume profiles built from 1-minute bars, with the POC, the
// value area, total, up/down or delta volume per row, and level lines extended until a later bar
// touches them. The engine below (the period clock, each minute's volume spread evenly over its
// ticks with the forming minute replaced until it completes, profiles to retain, the rows, the
// POC, the value area, the touches) is NinjaTrader's (TatankaPeriodicVolumeProfile.cs and its
// TatankaPvpCore namespace) with no Sierra Chart calls, so the tests can include this file. Where
// it differs on purpose, the comment says so (pvp_parity_spec.md section A).
//
// Data (spec C): NinjaTrader adds a 1-minute series of the chart's instrument. Here the minutes
// are this chart's own bars on a 1-minute chart (or second bars that divide a minute), otherwise
// a hidden 1-minute chart of the same symbol and settings. The engine takes the minutes through a
// small source interface (MinuteSource), so the tests feed it synthetic minutes. The Volume data
// option "Volume at price" builds the profiles from Sierra Chart's volume at price instead.
//
// Times are microseconds since Sierra Chart's base date, in the chart's time zone. Sierra bars
// are stamped at their START; NinjaTrader stamps them at their end, so the minute starting at m
// is NinjaTrader's minute m + 60 s.
//
// Each study call (ProcessCall) reads this chart's new bars, picks the source, gives the engine
// the new minutes (or bars) from a cursor, builds the developing snapshot, tests the touches,
// and writes the last bar's POC/VAH/VAL and the chart label. The drawing callback only reads what
// the call left (spec D), so scrolling and zooming repaint without study calls. A translucent
// histogram box is a Sierra Chart translucent range per profile (Left and Right placements).

#include "sierrachart.h"

#include <algorithm>
#include <climits>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <deque>
#include <functional>
#include <map>
#include <string>
#include <utility>
#include <vector>

SCDLLName("Tatanka Periodic Volume Profile")

namespace
{
	// Inputs in NinjaTrader's group/order sequence (spec B.2; Sierra Chart has no input groups).
	enum InputIndex
	{
		IN_PERIOD,
		IN_MULTIPLIER,
		IN_VOLUME_MODE,
		IN_VA_PERCENT,
		IN_ROWS_LAYOUT,
		IN_ROW_SIZE,
		IN_VA_METHOD,
		IN_PROFILES,
		IN_VOLUME_DATA,
		IN_SHOW_PROFILE,
		IN_ROW_VALUES,
		IN_WIDTH,
		IN_PLACEMENT,
		IN_PADDING,
		IN_ROW_GAP,
		IN_HISTORY_NOTICE,
		IN_SHOW_VAH,
		IN_SHOW_VAL,
		IN_SHOW_POC,
		IN_EXTEND_POC,
		IN_EXTEND_VAH,
		IN_EXTEND_VAL,
		IN_EXTENSION,
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

	// NinjaTrader's enums (NT:443-448), in their member order.
	enum PeriodOption { PER_DAILY, PER_WEEKLY, PER_MONTHLY, PER_YEARLY };
	enum VolumeModeOption { VM_TOTAL, VM_UP_DOWN, VM_DELTA };
	enum RowsLayoutOption { RL_NUMBER_OF_ROWS, RL_TICKS_PER_ROW };
	enum VaMethodOption { VAM_TRADINGVIEW, VAM_ATLEAST };
	enum PlacementOption { PL_LEFT, PL_RIGHT, PL_CHART_RIGHT_LATEST };
	enum ExtensionOption { EXT_UNTIL_TOUCHED, EXT_TO_CHART_EDGE };
	// Sierra Chart only (spec A #13).
	enum VolumeDataOption { VD_MINUTES, VD_VAP };

	// The three levels, in the order of the touch table.
	enum LevelIndex { LV_POC, LV_VAH, LV_VAL, LV_COUNT };

	const char* const PERIOD_NAMES[]	= {"Daily", "Weekly", "Monthly", "Yearly"};
	const char* const VOLUME_NAMES[]	= {"Total", "UpDown", "Delta"};
	const char* const LAYOUT_NAMES[]	= {"NumberOfRows", "TicksPerRow"};

	// Persistent variable keys
	const int PI_ERROR_LOGGED		= 1;
	const int PI_MINUTE_CHART		= 2;	// the hidden 1-minute chart's number (0: none)
	const int PI_NO_CHART_LOGGED	= 3;
	const int PP_STATE				= 1;

	const int64_t US_PER_SECOND	= 1000000;
	const int64_t US_PER_MINUTE	= 60 * US_PER_SECOND;
	const int64_t US_PER_DAY	= 86400 * US_PER_SECOND;
	const int NO_DATE			= INT_MIN;
	// A profile's LastChart before any minute was taken (NinjaTrader's DateTime.MinValue).
	const int64_t NO_TIME		= INT64_MIN;
	// |price / tick| beyond this is not a price (NinjaTrader's checked cast would throw, spec A #34).
	const double MAX_TICK_RATIO	= 4.0e15;
	// NinjaTrader's row cap (NT:633).
	const int MAX_ROWS			= 20000;
	// 1970-01-01 in Sierra Chart's day numbers (days since 1899-12-30).
	const int SIERRA_UNIX_DATE	= 25569;

	// Every text the study shows or logs (spec B.10), character for character.
	enum MessageId
	{
		MSG_NOT_INTRADAY,
		MSG_BAD_SETTINGS,
		MSG_NO_END_TIMES,
		MSG_WAITING,
		MSG_NO_MINUTE_CHART,
		MSG_WAITING_VAP,
		MSG_FIRST_LOADED,
		MSG_CAPPED,
		MSG_COUNT
	};

	const char* const MESSAGES[MSG_COUNT] =
	{
		// NinjaTrader's configuration errors (NT:103, NT:105), verbatim.
		"Use an intraday chart (for example, 30 or 60 Minute). The profile Period can still be Daily, Weekly, Monthly, or Yearly.",
		"Invalid period, row, or retention setting.",
		// The Session VP's: tick, volume and range bars need sc.BaseDataEndDateTime.
		"Reload the chart (Chart >> Reload and Recalculate). Tick, volume and range bars need their end times.",
		// NinjaTrader's waiting text (NT:244) with Sierra Chart's names for its settings.
		"Tatanka PVP: waiting for 1-minute history. Check the connection, Days to Load, and Session Times.",
		"Tatanka PVP: Sierra Chart could not open a 1-minute chart of this symbol. Use a 1-minute chart instead.",
		"Tatanka PVP: waiting for volume at price...",
		// NinjaTrader's bottom notices (NT:321, NT:324), verbatim.
		"PVP: first loaded period may be incomplete. Load history from before its start.",
		"PVP: row height increased to keep the profile within 20,000 rows."
	};

	// NinjaTrader prints its configuration error with its Name (NT:107).
	const char* const LOG_PREFIX = "Tatanka Periodic Volume Profile: ";

	// ---- Logic (no Sierra Chart calls, so it can be unit tested) ----

	uint32_t Fnv1a(uint32_t hash, const void* data, size_t size)
	{
		const unsigned char* bytes = (const unsigned char*)data;
		for (size_t i = 0; i < size; i++)
			hash = (hash ^ bytes[i]) * 16777619u;
		return hash;
	}

	// 64 bits for the history check (a chance collision must not keep a stale engine).
	const uint64_t FNV64_BASIS = 14695981039346656037ull;

	uint64_t Fnv1a64(uint64_t hash, const void* data, size_t size)
	{
		const unsigned char* bytes = (const unsigned char*)data;
		for (size_t i = 0; i < size; i++)
			hash = (hash ^ bytes[i]) * 1099511628211ull;
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

	// .NET's Math.Round(x, MidpointRounding.AwayFromZero), NinjaTrader's price to tick (NT:573):
	// 2.5 -> 3, -2.5 -> -3.
	double RoundHalfAway(double x)
	{
		return x >= 0 ? RoundHalfUp(x) : -RoundHalfUp(-x);
	}

	// .NET Framework's Math.Max(double, double): the first when larger or NaN, else the second.
	// NinjaTrader's integration clamps with it (NT:654-655) and keeps MaxAbsDelta (NT:696).
	double MaxNet(double a, double b)
	{
		if (a > b)
			return a;
		if (a != a)
			return a;
		return b;
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
	// AwayFromZero)) (NT:573). False for a price that is not a number or out of range.
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

	// T(v) of the spec: a Sierra float price snapped to the grid, then to its tick index.
	bool PriceTick(double price, double tick, int64_t& index)
	{
		return TickIndexOf(SnapToTick(price, tick), tick, index);
	}

	// ---- Calendar (Sierra date ints: days since 1899-12-30, a Saturday) ----

	// The proleptic Gregorian calendar of .NET's DateTime (H. Hinnant's days_from_civil).
	int DateOf(int year, int month, int day)
	{
		const int y		= year - (month <= 2 ? 1 : 0);
		const int era	= (y >= 0 ? y : y - 399) / 400;
		const int yoe	= y - era * 400;
		const int mp	= month + (month > 2 ? -3 : 9);
		const int doy	= (153 * mp + 2) / 5 + day - 1;
		const int doe	= yoe * 365 + yoe / 4 - yoe / 100 + doy;
		return era * 146097 + doe - 719468 + SIERRA_UNIX_DATE;
	}

	struct CivilDate
	{
		int Year	= 1900;
		int Month	= 1;
		int Day		= 1;
	};

	CivilDate CivilOf(int date)
	{
		const int z		= date - SIERRA_UNIX_DATE + 719468;
		const int era	= (z >= 0 ? z : z - 146096) / 146097;
		const int doe	= z - era * 146097;
		const int yoe	= (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
		const int doy	= doe - (365 * yoe + yoe / 4 - yoe / 100);
		const int mp	= (5 * doy + 2) / 153;
		CivilDate c;
		c.Day	= doy - (153 * mp + 2) / 5 + 1;
		c.Month	= mp < 10 ? mp + 3 : mp - 9;
		c.Year	= yoe + era * 400 + (c.Month <= 2 ? 1 : 0);
		return c;
	}

	// 0 = Sunday, as .NET's DayOfWeek.
	int WeekdayOf(int date)
	{
		return ((date % 7) + 7 + 6) % 7;
	}

	bool IsLeapYear(int year)
	{
		return (year % 4 == 0 && year % 100 != 0) || year % 400 == 0;
	}

	int DaysInMonth(int year, int month)
	{
		static const int days[12] = {31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31};
		return month == 2 && IsLeapYear(year) ? 29 : days[(month - 1) % 12];
	}

	// .NET's DateTime.AddMonths: the same day, clamped to the target month's length.
	int AddMonths(int date, int months)
	{
		const CivilDate c	= CivilOf(date);
		const int total		= c.Year * 12 + (c.Month - 1) + months;
		const int year		= (int)FloorDiv(total, 12);
		const int month		= total - year * 12 + 1;
		return DateOf(year, month, (std::min)(c.Day, DaysInMonth(year, month)));
	}

	// ---- Periods (spec B.6, NinjaTrader's PeriodClock.Get, NT:458-495) ----

	// A period's identity is its Start (NT:147); End is never used by NinjaTrader (kept for tests).
	struct PeriodWindow
	{
		int Start	= 0;
		int End		= 0;
	};

	struct PeriodClock
	{
		// Line for line on Sierra dates. Daily, weekly and monthly blocks count from January 1
		// and are clipped to the year; weeks start on Monday; yearly blocks are aligned to 2000.
		// The divisions are on non-negative values, so C++'s / is C#'s. NinjaTrader throws for a
		// multiple outside 1..100 (the input limits make that unreachable); clamped here.
		static PeriodWindow Get(int date, int period, int multiple)
		{
			multiple = (std::max)(1, (std::min)(100, multiple));
			const CivilDate c	= CivilOf(date);
			const int yearStart	= DateOf(c.Year, 1, 1);
			const int yearEnd	= DateOf(c.Year + 1, 1, 1);
			PeriodWindow w;
			switch (period)
			{
				case PER_DAILY:
				{
					const int dayIndex = (date - yearStart) / multiple * multiple;
					w.Start	= yearStart + dayIndex;
					w.End	= w.Start + multiple;
					break;
				}
				case PER_WEEKLY:
				{
					// Monday-based weeks; the first/last week can be truncated at January 1.
					const int offset	= (WeekdayOf(yearStart) + 6) % 7;
					const int monday	= yearStart - offset;
					const int block		= (date - monday) / (7 * multiple);
					w.Start	= monday + block * 7 * multiple;
					w.End	= w.Start + 7 * multiple;
					if (w.Start < yearStart)
						w.Start = yearStart;
					break;
				}
				case PER_MONTHLY:
				{
					const int firstMonth = (c.Month - 1) / multiple * multiple + 1;
					w.Start	= DateOf(c.Year, firstMonth, 1);
					w.End	= AddMonths(w.Start, multiple);
					break;
				}
				default:
				{
					const int firstYear	= 2000 + (int)std::floor((c.Year - 2000) / (double)multiple) * multiple;
					const int year		= (std::max)(1, firstYear);
					w.Start	= DateOf(year, 1, 1);
					w.End	= DateOf(year + multiple, 1, 1);
					return w;
				}
			}
			if (w.End > yearEnd)
				w.End = yearEnd;
			return w;
		}
	};

	// ---- Trading day (spec B.5, NT:135-143) ----

	// NinjaTrader's ActualTradingDayExchange.Date and ActualSessionBegin of a minute: Sierra
	// Chart's sc.GetTradingDayDate and sc.GetTradingDayStartDateTimeOfBar from the chart's
	// Session Times (Date NO_DATE: no session, the minute is dropped as NT:139 does).
	struct TradingDayInfo
	{
		int		Date	= NO_DATE;
		int64_t	Start	= 0;
	};

	using TradingDayLookup = std::function<TradingDayInfo(int64_t)>;

	// One lookup per trading day: Sierra Chart's trading day changes only at its start clock time,
	// and chart time is wall-clock time, so a trading day is [Start, Start + 24 h) across daylight
	// saving changes too.
	struct TradingDayCache
	{
		TradingDayLookup	Lookup;
		TradingDayInfo		Last;
		bool				Valid	= false;
		int64_t				Calls	= 0;

		TradingDayInfo Get(int64_t t)
		{
			if (Valid && Last.Start <= t && t < Last.Start + US_PER_DAY)
				return Last;
			Calls++;
			const TradingDayInfo info = Lookup ? Lookup(t) : TradingDayInfo();
			Last	= info;
			Valid	= info.Date != NO_DATE;
			return info;
		}

		void Reset()
		{
			Valid = false;
		}
	};

	// ---- Chart bars (spec B.3) ----

	// A column Sierra Chart adds with Include Columns With No Data: no volume, no trades, and
	// either all zero or flat at the previous close. It holds no trades: it never touches a level
	// and never holds a minute, but it keeps its slot on the x axis (the Session VP's rule).
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

	// The first instant after barStart (chart time, seconds since Sierra's base date) at which a
	// time bar ends early: each session end that no session continues, and, with New Bar at
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
	// where the next bar starts inside it (a bar cut by the data) or where the Session Times cut
	// it (cutSeconds from SessionCutAfter). Microseconds.
	int64_t TimeBarEnd(int64_t startUs, int secondsPerBar, bool hasNext, int64_t nextStartUs, int64_t cutSeconds)
	{
		int64_t end = startUs + (int64_t)secondsPerBar * US_PER_SECOND;
		if (hasNext && startUs < nextStartUs && nextStartUs < end)
			end = nextStartUs;
		if (cutSeconds != INT64_MAX && cutSeconds * US_PER_SECOND < end)
			end = cutSeconds * US_PER_SECOND;
		return end;
	}

	// The chart's bars as the touch test and the drawing see them: start S, end E (NinjaTrader's
	// close stamp), the end of the time the bar covers C, the tick indices of its low and high,
	// and whether it can touch a level (it holds trades and both prices are on the grid).
	struct PvpBars
	{
		std::vector<int64_t>	S;
		std::vector<int64_t>	E;
		std::vector<int64_t>	C;
		std::vector<int64_t>	LowTick;
		std::vector<int64_t>	HighTick;
		std::vector<uint8_t>	Touchable;

		int Count() const { return (int)S.size(); }

		void Resize(int count)
		{
			const size_t n = (size_t)(std::max)(0, count);
			S.resize(n);
			E.resize(n);
			C.resize(n);
			LowTick.resize(n);
			HighTick.resize(n);
			Touchable.resize(n);
		}

		void Set(int i, int64_t start, int64_t end, int64_t coverEnd, bool empty, double low, double high, double tick)
		{
			if (i < 0)
				return;
			if (i >= Count())
				Resize(i + 1);
			const size_t k = (size_t)i;
			S[k]	= start;
			E[k]	= end;
			C[k]	= coverEnd;
			int64_t lowTick = 0, highTick = 0;
			const bool valid = !empty && PriceTick(low, tick, lowTick) && PriceTick(high, tick, highTick) && lowTick <= highTick;
			LowTick[k]		= valid ? lowTick : 0;
			HighTick[k]		= valid ? highTick : -1;
			Touchable[k]	= valid ? 1 : 0;
		}

		// A time-based bar: it covers its whole span, [S, E).
		void SetTimeBar(int i, int64_t start, int secondsPerBar, bool hasNext, int64_t nextStart, const ChartSessions& sessions, bool empty,
			double low, double high, double tick)
		{
			const int64_t end = TimeBarEnd(start, secondsPerBar, hasNext, nextStart, SessionCutAfter(FloorDiv(start, US_PER_SECOND), sessions));
			Set(i, start, end, end, empty, low, high, tick);
		}

		// A tick, volume or range bar: it ends at its last trade (sc.BaseDataEndDateTime) and
		// covers up to that trade, [S, min(E + 1 us, next S)).
		void SetTradeBar(int i, int64_t start, int64_t lastTrade, bool hasNext, int64_t nextStart, bool empty, double low, double high,
			double tick)
		{
			int64_t cover = lastTrade + 1;
			if (hasNext)
				cover = (std::min)(cover, nextStart);
			Set(i, start, lastTrade, cover, empty, low, high, tick);
		}

		// The first bar ending after t (E never decreases), Count() if none.
		int FirstEndAfter(int64_t t) const
		{
			return (int)(std::upper_bound(E.begin(), E.end(), t) - E.begin());
		}

		// Whether the first `count` bars are the same as other's (spec B.3: a full recalculation
		// that changed them resets the touches).
		bool SameAs(const PvpBars& other, int count) const
		{
			if (count > Count() || count > other.Count())
				return false;
			for (size_t k = 0; k < (size_t)(std::max)(0, count); k++)
				if (S[k] != other.S[k] || E[k] != other.E[k] || C[k] != other.C[k] || LowTick[k] != other.LowTick[k]
					|| HighTick[k] != other.HighTick[k] || Touchable[k] != other.Touchable[k])
					return false;
			return true;
		}
	};

	// ---- Minutes (spec B.4) ----

	// One 1-minute bar as NinjaTrader's minute series gives it to the profile (NT:159): its low
	// and high in ticks, its volume and Close >= Open. M is the minute's START (Sierra Chart's
	// stamp, its order and identity); NinjaTrader's time of it is M + 60 s.
	struct PvpMinute
	{
		int64_t	M		= 0;
		int64_t	Low		= 0;
		int64_t	High	= 0;
		double	Volume	= 0;
		bool	Up		= true;
		bool	Valid	= false;	// NinjaTrader would take it (NT:570-574)
		bool	Empty	= false;	// an empty column of the source: not a minute at all

		bool operator==(const PvpMinute& o) const
		{
			return M == o.M && Low == o.Low && High == o.High && Volume == o.Volume && Up == o.Up && Valid == o.Valid && Empty == o.Empty;
		}
		bool operator!=(const PvpMinute& o) const { return !(*this == o); }
	};

	// A minute from Sierra Chart's float prices. Valid as NinjaTrader's Upsert checks it (NT:570-572):
	// a finite volume >= 0, finite prices and High >= Low; plus the tick conversion (NinjaTrader's
	// checked cast would throw instead, spec A #34). Up = T(Close) >= T(Open) (spec A #23): equal to
	// NinjaTrader's Close >= Open on grid prices, immune to float storage.
	PvpMinute MinuteOf(int64_t m, double open, double high, double low, double close, double volume, double tick)
	{
		PvpMinute r;
		r.M			= m;
		r.Volume	= volume;
		int64_t lowTick = 0, highTick = 0;
		r.Valid = std::isfinite(volume) && volume >= 0 && std::isfinite(low) && std::isfinite(high) && !(high < low)
			&& PriceTick(low, tick, lowTick) && PriceTick(high, tick, highTick);
		r.Low	= lowTick;
		r.High	= highTick;
		int64_t openTick = 0, closeTick = 0;
		if (PriceTick(open, tick, openTick) && PriceTick(close, tick, closeTick))
			r.Up = closeTick >= openTick;
		else
			r.Up = close >= open;
		return r;
	}

	// ---- Profile math (spec B.7, NinjaTrader's TatankaPvpCore.Profile, NT:497-720) ----

	// One display row (NT:497-502): ticks LowTick..HighTick, up and down volume.
	struct PvpRow
	{
		int64_t	LowTick		= 0;
		int64_t	HighTick	= 0;
		double	Up			= 0;
		double	Down		= 0;

		double Total() const { return Up + Down; }
	};

	// NinjaTrader's Snapshot (NT:504-511), plus the level ticks the touch test compares.
	struct PvpSnapshot
	{
		std::vector<PvpRow>	Rows;
		double	TotalVolume		= 0;
		double	ValueAreaVolume	= 0;
		double	MaxVolume		= 0;
		double	MaxAbsDelta		= 0;
		double	Poc				= 0;
		double	Vah				= 0;
		double	Val				= 0;
		double	LowEdge			= 0;
		double	HighEdge		= 0;
		int		PocIndex		= 0;
		int		VahIndex		= 0;
		int		ValIndex		= 0;
		int64_t	TicksPerRow		= 0;
		bool	WasCapped		= false;
		int64_t	PocTick			= 0;
		int64_t	VahTick			= 0;
		int64_t	ValTick			= 0;

		bool HasRows() const { return !Rows.empty(); }

		int64_t LevelTick(int level) const
		{
			return level == LV_POC ? PocTick : level == LV_VAH ? VahTick : ValTick;
		}
	};

	// A difference-array entry (NinjaTrader's Density, NT:524-527).
	struct PvpEvent
	{
		double Up	= 0;
		double Down	= 0;
	};

	// A constant-density span of a unit: a minute's [Low, High] ticks with its whole volume in
	// one channel, or one channel of a volume-at-price element (one tick).
	struct PvpRange
	{
		int64_t	Low		= 0;
		int64_t	High	= 0;
		double	Volume	= 0;
		bool	Up		= true;

		bool operator==(const PvpRange& o) const { return Low == o.Low && High == o.High && Volume == o.Volume && Up == o.Up; }
	};

	// The settings a profile is built with (NT:558-566).
	struct PvpProfileConfig
	{
		double	Tick	= 0.25;
		int		Layout	= RL_NUMBER_OF_ROWS;
		int		RowSize	= 200;
		double	Percent	= 68;
		bool	AtLeast	= false;
	};

	// NinjaTrader's static profile arithmetic, expression for expression (bit-for-bit parity,
	// spec A #26: its floating tie-breaks included).
	struct PvpMath
	{
		// NT:669-676: the integer ticks per row whose row count is nearest the target; a tie
		// picks the thinner rows.
		static int64_t ChooseTicksPerRow(int64_t span, int target)
		{
			const int64_t smaller		= (std::max)((int64_t)1, (int64_t)std::floor((double)span / (double)target));
			const int64_t larger		= (std::max)((int64_t)1, (int64_t)std::ceil((double)span / (double)target));
			const double smallerError	= std::fabs(std::ceil((double)span / (double)smaller) - (double)target);
			const double largerError	= std::fabs(std::ceil((double)span / (double)larger) - (double)target);
			return smallerError <= largerError ? smaller : larger;
		}

		// NT:678-685: rescales the rows so their sums are the exact minute volumes.
		static void Normalize(std::vector<PvpRow>& rows, double expectedUp, double expectedDown)
		{
			double up = 0, down = 0;
			for (const PvpRow& row : rows)
			{
				up		+= row.Up;
				down	+= row.Down;
			}
			const double upFactor	= up > 0 ? expectedUp / up : 0;
			const double downFactor	= down > 0 ? expectedDown / down : 0;
			for (PvpRow& row : rows)
			{
				row.Up		*= upFactor;
				row.Down	*= downFactor;
			}
		}

		// NT:687-720 over every row, empty ones included (spec A #27): the POC scan with the
		// nearest-the-middle tie rule, the one-row value-area walk (exhausted sides -1, the
		// 1e-12 x Total tolerance, TradingViewStyle's final break), and the level prices with
		// NinjaTrader's integer (lower-middle) POC tick.
		static void Calculate(PvpSnapshot& result, double tickSize, double percent, bool atLeast)
		{
			const std::vector<PvpRow>& rows = result.Rows;
			if (rows.empty())
				return;
			const int n = (int)rows.size();
			const double middle = (n - 1) / 2.0;
			int poc = 0;
			for (int i = 0; i < n; i++)
			{
				const double total = rows[(size_t)i].Total();
				result.TotalVolume += total;
				result.MaxAbsDelta = MaxNet(result.MaxAbsDelta, std::fabs(rows[(size_t)i].Up - rows[(size_t)i].Down));
				if (total > result.MaxVolume || (total == result.MaxVolume && std::fabs(i - middle) < std::fabs(poc - middle)))
				{
					result.MaxVolume	= total;
					poc					= i;
				}
			}
			int lo = poc, hi = poc;
			double included = rows[(size_t)poc].Total();
			const double target = result.TotalVolume * percent / 100;
			while (included < target && (lo > 0 || hi < n - 1))
			{
				const double above		= hi < n - 1 ? rows[(size_t)hi + 1].Total() : -1;
				const double below		= lo > 0 ? rows[(size_t)lo - 1].Total() : -1;
				const bool takeAbove	= above > below || (above == below && hi + 1 - poc <= poc - (lo - 1));
				const double candidate	= takeAbove ? above : below;
				if (!atLeast && included + candidate > target + result.TotalVolume * 1e-12)
					break;
				included += candidate;
				if (takeAbove)
					hi++;
				else
					lo--;
			}
			const PvpRow& pocRow = rows[(size_t)poc];
			result.PocIndex			= poc;
			result.ValIndex			= lo;
			result.VahIndex			= hi;
			result.ValueAreaVolume	= included;
			result.PocTick			= pocRow.LowTick + (pocRow.HighTick - pocRow.LowTick) / 2;
			result.ValTick			= rows[(size_t)lo].LowTick;
			result.VahTick			= rows[(size_t)hi].HighTick;
			result.Poc				= (double)result.PocTick * tickSize;
			result.Val				= (double)result.ValTick * tickSize;
			result.Vah				= (double)result.VahTick * tickSize;
			result.LowEdge			= ((double)rows[0].LowTick - 0.5) * tickSize;
			result.HighEdge			= ((double)rows[(size_t)n - 1].HighTick + 0.5) * tickSize;
		}
	};

	// One period's profile (NinjaTrader's Profile, NT:538-667): finished minutes in a difference
	// map, the newest minute pending (replaced while it forms, committed when a later one arrives),
	// the snapshot built from both, and the touch state of its levels (spec B.7).
	struct PvpProfile
	{
		int					WindowStart	= 0;
		int					WindowEnd	= 0;
		int64_t				StartChart	= 0;		// NinjaTrader's ActualSessionBegin of the first minute
		int64_t				LastChart	= NO_TIME;	// NinjaTrader's time of the last minute taken (its end)
		bool				First		= false;	// the first profile built since the engine started
		bool				Closed		= false;
		int64_t				Version		= 0;
		PvpProfileConfig	Cfg;
		// The first chart bar touching POC, VAH, VAL (-1: none yet) and the last completed bar tested.
		int					Touch[LV_COUNT]	= {-1, -1, -1};
		int					TouchScanned	= -1;

		PvpProfile(const PeriodWindow& window, int64_t startChart, bool first, const PvpProfileConfig& cfg)
			: WindowStart(window.Start), WindowEnd(window.End), StartChart(startChart), First(first), Cfg(cfg)
		{
		}

		// NT:568-592 with sourceIndex = the unit's id (a minute's start). Closed profiles and
		// older units take nothing; the same unit again unchanged changes nothing (no version);
		// a later unit commits the pending one first. Returns whether the profile changed. A
		// unit given again with only a later time is a change: a volume-at-price bar that ends
		// without new trades takes its end time, as when it is read complete (a minute's time
		// never changes).
		bool Upsert(int64_t id, const PvpRange* ranges, size_t count, int64_t time)
		{
			if (Closed)
				return false;
			if (HasPending)
			{
				if (id < PendingId)
					return false;
				if (id == PendingId && SameRanges(ranges, count) && time == LastChart)
					return false;
				if (id > PendingId)
				{
					for (const PvpRange& r : PendingRanges)
						AddRange(Committed, r);
					CommittedUp		+= PendingUp;
					CommittedDown	+= PendingDown;
				}
			}
			// Replacing the forming unit prevents double counting as its cumulative volume, range
			// and direction change; completed units stay as they were committed (NT:586-587).
			HasPending	= true;
			PendingId	= id;
			PendingRanges.assign(ranges, ranges + count);
			PendingUp	= 0;
			PendingDown	= 0;
			for (const PvpRange& r : PendingRanges)
			{
				if (r.Up)
					PendingUp += r.Volume;
				else
					PendingDown += r.Volume;
			}
			LastChart = time;
			Version++;
			return true;
		}

		bool UpsertMinute(const PvpMinute& m)
		{
			if (Closed || !m.Valid)
				return false;
			PvpRange r;
			r.Low		= m.Low;
			r.High		= m.High;
			r.Volume	= m.Volume;
			r.Up		= m.Up;
			return Upsert(m.M, &r, 1, m.M + US_PER_MINUTE);
		}

		// NT:594-600: the final snapshot (the pending unit included), then closed for good.
		void Complete()
		{
			if (Closed)
				return;
			Snapshot();
			Closed = true;
			std::map<int64_t, PvpEvent>().swap(Committed);
			std::vector<PvpRange>().swap(PendingRanges);
			HasPending = false;
		}

		// The current snapshot: a closed profile's final one, the developing one rebuilt when its
		// version changed (NinjaTrader's 250 ms throttle is a platform detail, spec A #14).
		const PvpSnapshot& Snapshot()
		{
			if (!Closed && CachedVersion != Version)
			{
				Cached			= Build();
				CachedVersion	= Version;
			}
			return Cached;
		}

		// The snapshot as last built (the drawing reads this; the study call builds it).
		const PvpSnapshot& View() const { return Cached; }

		bool SnapshotCurrent() const { return Closed || CachedVersion == Version; }

		size_t EventCount() const { return Committed.size(); }

		// NT:617-667. The event values are the committed ones with the pending unit's added in
		// its order (NinjaTrader copies the map, then AddRange's into the copy), so a key holds
		// committed + share, exactly as after the unit is committed.
		PvpSnapshot Build() const
		{
			PvpSnapshot result;
			struct PendingEvent
			{
				int64_t	Key;
				double	Up;
				double	Down;
			};
			std::vector<PendingEvent> pending;
			if (HasPending)
			{
				for (const PvpRange& r : PendingRanges)
				{
					if (!(r.Volume > 0))
						continue;
					const double density = r.Volume / ((double)r.High - (double)r.Low + 1);
					pending.push_back({r.Low, r.Up ? density : 0, r.Up ? 0 : density});
					pending.push_back({r.High + 1, r.Up ? -density : 0, r.Up ? 0 : -density});
				}
				std::stable_sort(pending.begin(), pending.end(), [](const PendingEvent& a, const PendingEvent& b) { return a.Key < b.Key; });
			}

			std::vector<int64_t> keys;
			std::vector<PvpEvent> values;
			keys.reserve(Committed.size() + pending.size());
			values.reserve(Committed.size() + pending.size());
			auto c = Committed.begin();
			size_t p = 0;
			while (c != Committed.end() || p < pending.size())
			{
				const bool fromCommitted = c != Committed.end() && (p >= pending.size() || c->first <= pending[p].Key);
				const int64_t key = fromCommitted ? c->first : pending[p].Key;
				PvpEvent value;
				if (fromCommitted)
				{
					value = c->second;
					++c;
				}
				while (p < pending.size() && pending[p].Key == key)
				{
					value.Up	+= pending[p].Up;
					value.Down	+= pending[p].Down;
					p++;
				}
				keys.push_back(key);
				values.push_back(value);
			}
			if (keys.size() < 2)
				return result;

			const int64_t low	= keys.front();
			const int64_t high	= keys.back() - 1;
			const int64_t span	= high - low + 1;
			int64_t ticks = Cfg.RowSize;
			if (Cfg.Layout == RL_NUMBER_OF_ROWS)
				ticks = PvpMath::ChooseTicksPerRow(span, Cfg.RowSize);
			const bool capped = std::ceil((double)span / (double)ticks) > MAX_ROWS;
			if (capped)
				ticks = (int64_t)std::ceil((double)span / (double)MAX_ROWS);
			const int count = (int)std::ceil((double)span / (double)ticks);
			std::vector<PvpRow>& rows = result.Rows;
			rows.resize((size_t)count);
			for (int i = 0; i < count; i++)
			{
				const int64_t rowLow = low + i * ticks;
				rows[(size_t)i].LowTick		= rowLow;
				rows[(size_t)i].HighTick	= (std::min)(high, rowLow + ticks - 1);
			}
			// Integrate constant-density spans over the rows: the cost follows the event keys and
			// the rows, not the ticks of a year's range (NT:644-645).
			double runningUp = 0, runningDown = 0;
			for (size_t i = 0; i + 1 < keys.size(); i++)
			{
				runningUp	+= values[i].Up;
				runningDown	+= values[i].Down;
				int64_t cursor = keys[i];
				const int64_t end = keys[i + 1];
				while (cursor < end)
				{
					PvpRow& row = rows[(size_t)((cursor - low) / ticks)];
					const int64_t stop = (std::min)(end, row.HighTick + 1);
					row.Up		+= MaxNet(0, runningUp) * (double)(stop - cursor);
					row.Down	+= MaxNet(0, runningDown) * (double)(stop - cursor);
					cursor = stop;
				}
			}
			const double expectedUp		= CommittedUp + (HasPending ? PendingUp : 0);
			const double expectedDown	= CommittedDown + (HasPending ? PendingDown : 0);
			PvpMath::Normalize(rows, expectedUp, expectedDown);
			PvpMath::Calculate(result, Cfg.Tick, Cfg.Percent, Cfg.AtLeast);
			result.TicksPerRow	= ticks;
			result.WasCapped	= capped;
			return result;
		}

	private:
		std::map<int64_t, PvpEvent>	Committed;			// never erased while open, as NinjaTrader's dictionary
		double						CommittedUp		= 0;
		double						CommittedDown	= 0;
		bool						HasPending		= false;
		int64_t						PendingId		= 0;
		std::vector<PvpRange>		PendingRanges;
		double						PendingUp		= 0;
		double						PendingDown		= 0;
		PvpSnapshot					Cached;
		int64_t						CachedVersion	= -1;

		bool SameRanges(const PvpRange* ranges, size_t count) const
		{
			if (count != PendingRanges.size())
				return false;
			for (size_t k = 0; k < count; k++)
				if (!(ranges[k] == PendingRanges[k]))
					return false;
			return true;
		}

		// NT:602-615: +density at Low, -density at High + 1, in the unit's channel. Nothing for
		// a volume of 0 or less.
		static void AddRange(std::map<int64_t, PvpEvent>& map, const PvpRange& r)
		{
			if (!(r.Volume > 0))
				return;
			const double density = r.Volume / ((double)r.High - (double)r.Low + 1);
			AddEvent(map, r.Low, r.Up ? density : 0, r.Up ? 0 : density);
			AddEvent(map, r.High + 1, r.Up ? -density : 0, r.Up ? 0 : -density);
		}

		static void AddEvent(std::map<int64_t, PvpEvent>& map, int64_t key, double up, double down)
		{
			PvpEvent& value = map[key];
			value.Up	+= up;
			value.Down	+= down;
		}
	};

	// What the engine is built with (spec B.2: inputs 0, 1 and 3-7, and the tick size).
	struct PvpSettings
	{
		int					Period		= PER_WEEKLY;
		int					Multiplier	= 1;
		int					Keep		= 20;
		PvpProfileConfig	Profile;
	};

	// The profiles of one chart (NinjaTrader's BIP 1 body, NT:133-166): each minute goes to the
	// profile of its trading date's period; a new period completes the previous profile and drops
	// the oldest beyond retention; minutes of an older period than the current are ignored.
	struct PvpEngine
	{
		PvpSettings				Cfg;
		std::deque<PvpProfile>	Profiles;		// oldest first; the last is the current one
		TradingDayCache			Days;
		int64_t					Revision	= 0;	// bumped by every change

		void Reset()
		{
			Profiles.clear();
			Days.Reset();
			Revision++;
		}

		// One minute (forming or complete). Returns whether anything changed.
		bool Minute(const PvpMinute& m)
		{
			if (m.Empty)
				return false;
			bool created = false;
			PvpProfile* p = ProfileFor(m.M, created);
			const bool changed = p != nullptr && p->UpsertMinute(m);
			if (created || changed)
				Revision++;
			return created || changed;
		}

		// One volume-at-price bar (spec C.7): id = the bar's index (its order: bars can share a
		// start time, so the start is no identity), dayTime = the time whose trading day decides
		// the period (the bar's start), time = its LastChart.
		bool Unit(int64_t id, int64_t dayTime, int64_t time, const std::vector<PvpRange>& ranges)
		{
			bool created = false;
			PvpProfile* p = ProfileFor(dayTime, created);
			const bool changed = p != nullptr && p->Upsert(id, ranges.data(), ranges.size(), time);
			if (created || changed)
				Revision++;
			return created || changed;
		}

		PvpProfile* Newest() { return Profiles.empty() ? nullptr : &Profiles.back(); }
		const PvpProfile* Newest() const { return Profiles.empty() ? nullptr : &Profiles.back(); }

		// The values NinjaTrader publishes (spec A #6, B.7 Values): the newest profile's current
		// levels, when it has rows.
		bool NewestLevels(double& poc, double& vah, double& val)
		{
			PvpProfile* p = Newest();
			if (p == nullptr)
				return false;
			const PvpSnapshot& s = p->Snapshot();
			if (!s.HasRows())
				return false;
			poc = s.Poc;
			vah = s.Vah;
			val = s.Val;
			return true;
		}

		// Builds every snapshot that is out of date (the developing one when its version
		// changed), so the drawing callback only reads (spec D.11).
		void UpdateSnapshots()
		{
			for (PvpProfile& p : Profiles)
				p.Snapshot();
		}

	private:
		PvpProfile* ProfileFor(int64_t dayTime, bool& created)
		{
			const TradingDayInfo day = Days.Get(dayTime);
			if (day.Date == NO_DATE)
				return nullptr;
			const PeriodWindow w = PeriodClock::Get(day.Date, Cfg.Period, Cfg.Multiplier);
			if (Profiles.empty() || w.Start != Profiles.back().WindowStart)
			{
				// Regressing data (NT:149).
				if (!Profiles.empty() && w.Start < Profiles.back().WindowStart)
					return nullptr;
				const bool first = Profiles.empty();
				if (!Profiles.empty())
					Profiles.back().Complete();
				// The profile starts at the beginning of the first loaded trading session in the
				// period; missing earlier data is a partial-history risk (NT:152-153).
				Profiles.emplace_back(w, day.Start, first, Cfg.Profile);
				while ((int)Profiles.size() > (std::max)(1, Cfg.Keep))
					Profiles.pop_front();
				created = true;
			}
			return &Profiles.back();
		}
	};

	// ---- Touches (spec B.7, NinjaTrader's ObserveTouches and Touches.Observe, NT:180-190, NT:513-522) ----

	// Per closed retained profile, the first chart bar (ascending, empty columns skipped) that
	// ends after the profile's last minute (E_j > LastChart, NinjaTrader's close stamp) and whose
	// range holds the level, inclusive. Completed bars are tested once; the forming bar on every
	// call with its current range, and a touch on it is kept (its range only grows). The touches
	// of all three levels are kept whatever the Extend switches say (they only choose which are
	// drawn). The developing profile is never tested (NT:187).
	// This is NinjaTrader in real time. Its reloaded history (without Tick Replay) takes a minute
	// at the minute's end, so on bars shorter than a minute (second, tick, volume, range bars) the
	// ones ending inside the next period's first minute are never tested there: a line can stop at
	// one of them here, as NinjaTrader shows live, where a reloaded NinjaTrader chart runs it on
	// (spec A #43, B.7; on bars of a minute or longer both are the same).
	struct PvpTouches
	{
		static void Update(PvpEngine& engine, const PvpBars& bars)
		{
			const int n = bars.Count();
			for (PvpProfile& p : engine.Profiles)
			{
				if (!p.Closed)
					continue;
				const PvpSnapshot& s = p.Snapshot();
				if (!s.HasRows())
					continue;
				const int first = bars.FirstEndAfter(p.LastChart);
				for (int j = (std::max)(first, p.TouchScanned + 1); j <= n - 2 && !AllTouched(p); j++)
					Test(p, s, bars, j);
				p.TouchScanned = (std::max)(p.TouchScanned, n - 2);
				if (n >= 1 && bars.E[(size_t)n - 1] > p.LastChart)
					Test(p, s, bars, n - 1);
			}
		}

		// The chart's bars changed (or the profiles were rebuilt): every touch is found again.
		static void Reset(PvpEngine& engine)
		{
			for (PvpProfile& p : engine.Profiles)
			{
				for (int k = 0; k < LV_COUNT; k++)
					p.Touch[k] = -1;
				p.TouchScanned = -1;
			}
		}

	private:
		static bool AllTouched(const PvpProfile& p)
		{
			return p.Touch[LV_POC] >= 0 && p.Touch[LV_VAH] >= 0 && p.Touch[LV_VAL] >= 0;
		}

		static void Test(PvpProfile& p, const PvpSnapshot& s, const PvpBars& bars, int j)
		{
			const size_t k = (size_t)j;
			if (!bars.Touchable[k])
				return;
			for (int level = 0; level < LV_COUNT; level++)
			{
				if (p.Touch[level] >= 0)
					continue;
				const int64_t tick = s.LevelTick(level);
				if (bars.LowTick[k] <= tick && tick <= bars.HighTick[k])
					p.Touch[level] = j;
			}
		}
	};

	// ---- Minute sources (spec C.3-C.6) ----

	enum SourceKind { SRC_NONE, SRC_OWN, SRC_HIDDEN, SRC_VAP };

	struct SourcePlan
	{
		// Bars that can be this chart's minutes (spec C.3): time bars of a minute or a divisor of
		// a minute. Each bar must also lie inside one whole minute (InsideOneMinute).
		static bool OwnBarLength(bool timeBased, int secondsPerBar)
		{
			return timeBased && secondsPerBar >= 1 && secondsPerBar <= 60 && 60 % secondsPerBar == 0;
		}

		// [start, start + secondsPerBar) within [floor_min(start), floor_min(start) + 60 s).
		static bool InsideOneMinute(int64_t start, int secondsPerBar)
		{
			const int64_t offset = start - FloorDiv(start, US_PER_MINUTE) * US_PER_MINUTE;
			return offset + (int64_t)secondsPerBar * US_PER_SECOND <= US_PER_MINUTE;
		}

		static int Choose(int volumeData, bool ownBarLength, bool barsInsideMinutes)
		{
			if (volumeData == VD_VAP)
				return SRC_VAP;
			return ownBarLength && barsInsideMinutes ? SRC_OWN : SRC_HIDDEN;
		}
	};

	// Minutes in ascending start order, by index. Sierra Chart: this chart's bars (OwnMinutes) or
	// the hidden 1-minute chart (ArrayMinutes over its arrays); tests: vectors.
	struct MinuteSource
	{
		virtual int64_t Count() const = 0;
		virtual PvpMinute At(int64_t k) const = 0;

	protected:
		~MinuteSource() = default;
	};

	// The first index whose minute starts at or after t (minutes ascend).
	int64_t FirstMinuteAtOrAfter(const MinuteSource& source, int64_t t)
	{
		int64_t lo = 0, hi = source.Count();
		while (lo < hi)
		{
			const int64_t mid = lo + (hi - lo) / 2;
			if (source.At(mid).M < t)
				lo = mid + 1;
			else
				hi = mid;
		}
		return lo;
	}

	// One bar of this chart, as OwnMinutes reads it.
	struct OwnBar
	{
		int64_t	S		= 0;
		double	Open	= 0;
		double	High	= 0;
		double	Low		= 0;
		double	Close	= 0;
		double	Volume	= 0;
		bool	Empty	= false;

		// From Sierra Chart's arrays at bar i: an empty column holds no minute.
		static OwnBar Make(int64_t start, double open, double high, double low, double close, double volume, double trades, bool hasPrevious,
			double previousClose)
		{
			OwnBar b;
			b.S		= start;
			b.Open		= open;
			b.High		= high;
			b.Low		= low;
			b.Close		= close;
			b.Volume	= volume;
			b.Empty		= IsEmptyColumn(volume, trades, open, high, low, close, hasPrevious, previousClose);
			return b;
		}
	};

	// This chart's bars as minutes (spec C.4): consecutive non-empty bars starting in the same
	// minute make that minute (first open, highest high, lowest low, last close, summed volume).
	// On a 1-minute chart each bar is a minute; the minute holding the last bar is the forming one.
	// Memory: 64 bytes per minute (spec C.9; with PvpBars, about 105 bytes per bar of a 1-minute
	// chart, some 65 MB for Yearly x5).
	struct OwnMinutes final : MinuteSource
	{
		struct Entry
		{
			int64_t	M			= 0;
			double	Open		= 0;
			double	High		= 0;
			double	Low			= 0;
			double	Close		= 0;
			double	Volume		= 0;
			int		FirstBar	= 0;
			int		LastBar		= 0;
			int		Outside		= 0;	// bars of it not inside one whole minute
		};

		std::vector<Entry>	Minutes;
		double				Tick			= 0.25;
		int					SecondsPerBar	= 60;
		int					Outside			= 0;	// over all entries

		void Clear()
		{
			Minutes.clear();
			Outside = 0;
		}

		// Every non-empty bar lies inside one whole minute (else the hidden chart is the source).
		bool Aligned() const { return Outside == 0; }

		// Bars from `from` (sc.UpdateStartIndex; 0 on a full recalculation) changed or are new.
		template <typename BarAt>
		void Update(int count, int from, BarAt barAt)
		{
			from = (std::max)(0, (std::min)(from, count));
			while (!Minutes.empty() && Minutes.back().LastBar >= from)
			{
				Outside -= Minutes.back().Outside;
				Minutes.pop_back();
			}
			for (int i = Minutes.empty() ? 0 : Minutes.back().LastBar + 1; i < count; i++)
			{
				const OwnBar b = barAt(i);
				if (b.Empty)
					continue;
				const int64_t m = FloorDiv(b.S, US_PER_MINUTE) * US_PER_MINUTE;
				const int outside = SourcePlan::InsideOneMinute(b.S, SecondsPerBar) ? 0 : 1;
				Outside += outside;
				if (!Minutes.empty() && Minutes.back().M == m)
				{
					Entry& e = Minutes.back();
					e.High		= (std::max)(e.High, b.High);
					e.Low		= (std::min)(e.Low, b.Low);
					e.Close		= b.Close;
					e.Volume	+= b.Volume;
					e.LastBar	= i;
					e.Outside	+= outside;
					continue;
				}
				Entry e;
				e.M			= m;
				e.Open		= b.Open;
				e.High		= b.High;
				e.Low		= b.Low;
				e.Close		= b.Close;
				e.Volume	= b.Volume;
				e.FirstBar	= i;
				e.LastBar	= i;
				e.Outside	= outside;
				Minutes.push_back(e);
			}
		}

		int64_t Count() const override { return (int64_t)Minutes.size(); }

		PvpMinute At(int64_t k) const override
		{
			const Entry& e = Minutes[(size_t)k];
			return MinuteOf(e.M, e.Open, e.High, e.Low, e.Close, e.Volume, Tick);
		}
	};

	// Minutes read in place from arrays (spec C.5 reading): the hidden 1-minute chart's
	// SCDateTimeArray and SCFloatArrays in Sierra Chart, vectors in the tests. Times: SCDateTime
	// or int64 microseconds. Columns with no data are skipped (Trades may be null).
	template <typename TimeArray, typename PriceArray>
	struct ArrayMinutes final : MinuteSource
	{
		const TimeArray*	Times	= nullptr;
		const PriceArray*	Open	= nullptr;
		const PriceArray*	High	= nullptr;
		const PriceArray*	Low		= nullptr;
		const PriceArray*	Close	= nullptr;
		const PriceArray*	Volume	= nullptr;
		const PriceArray*	Trades	= nullptr;
		int64_t				N		= 0;
		double				Tick	= 0.25;

		int64_t Count() const override { return N; }

		PvpMinute At(int64_t k) const override
		{
			const int i = (int)k;
			PvpMinute m = MinuteOf(Micros((*Times)[i]), (double)(*Open)[i], (double)(*High)[i], (double)(*Low)[i], (double)(*Close)[i],
				(double)(*Volume)[i], Tick);
			const double trades = Trades != nullptr ? (double)(*Trades)[i] : 0;
			m.Empty = IsEmptyColumn((double)(*Volume)[i], trades, (double)(*Open)[i], (double)(*High)[i], (double)(*Low)[i], (double)(*Close)[i],
				i > 0, i > 0 ? (double)(*Close)[i - 1] : 0);
			return m;
		}

		static int64_t Micros(int64_t t) { return t; }
		static int64_t Micros(const SCDateTime& t) { return t.AsMicrosecondsSinceBaseDate(); }
	};

	// Where minutes are taken (spec A #17, C.5 clip): from this chart's first bar start, before
	// the coverage end of its last bar, and during a replay up to the replay time.
	struct FeedClip
	{
		int64_t	First	= INT64_MIN;
		int64_t	End		= INT64_MAX;
		int64_t	Replay	= INT64_MAX;
	};

	// The completed units given to the engine (all before the cursor's): how many, and a hash of
	// them in order, so a full recalculation can tell whether the history they came from changed
	// (spec A #25, C.6). Pending: the cursor's unit as last given (complete once a later one is).
	struct FeedHistory
	{
		int64_t		Count	= 0;
		uint64_t	Hash	= FNV64_BASIS;
		uint64_t	Pending	= 0;

		void Complete()
		{
			Hash = Fnv1a64(Hash, &Pending, sizeof(Pending));
			Count++;
		}

		bool Same(const FeedHistory& o) const { return Count == o.Count && Hash == o.Hash; }
	};

	uint64_t MinuteHash(const PvpMinute& m)
	{
		const int64_t numbers[4] = {m.M, m.Low, m.High, (m.Up ? 1 : 0) | (m.Valid ? 2 : 0)};
		return Fnv1a64(Fnv1a64(FNV64_BASIS, numbers, sizeof(numbers)), &m.Volume, sizeof(m.Volume));
	}

	// The last minute given to the engine (spec C.6): its index and start, and the minute before
	// it as it was then (a completed minute that changes later means the history changed).
	struct FeedCursor
	{
		bool		Valid	= false;
		int64_t		K		= -1;
		int64_t		M		= 0;
		bool		HasPrev	= false;
		PvpMinute	Prev;
		FeedHistory	History;
	};

	enum FeedResult { FEED_CONTINUED, FEED_REBUILT };

	struct MinuteFeed
	{
		// One study call (spec C.6): checks the cursor against the source, rebuilds the engine
		// from the first minute when the history changed (or `rebuild`: the engine key, the
		// source or this chart's first bar changed), then gives the engine every minute from the
		// cursor's on. The cursor's minute is given again with its current values: the engine
		// replaces its pending minute, so whatever the call sizes, the lag between the charts or
		// the order of the updates, every minute counts once. `verify` (a full recalculation)
		// also compares every completed minute with what the engine took: a correction or a
		// back-adjustment in mid-history keeps the count and the newest minutes the cursor checks.
		static int Run(PvpEngine& engine, FeedCursor& cursor, const MinuteSource& source, const FeedClip& clip, bool rebuild, bool verify = false)
		{
			const int64_t n = source.Count();
			if (!rebuild && cursor.Valid && (!Continues(cursor, source) || (verify && !SameHistory(cursor, source, clip))))
				rebuild = true;
			if (rebuild)
			{
				engine.Reset();
				cursor = FeedCursor();
			}
			for (int64_t j = cursor.Valid ? cursor.K : FirstMinuteAtOrAfter(source, clip.First); j < n; j++)
			{
				const PvpMinute m = source.At(j);
				if (m.M < clip.First || m.Empty)
					continue;
				if (m.M >= clip.End || m.M > clip.Replay)
					break;
				engine.Minute(m);
				if (cursor.Valid && j != cursor.K)
					cursor.History.Complete();	// a later minute: the cursor's is complete
				cursor.History.Pending	= MinuteHash(m);
				cursor.Valid			= true;
				cursor.K				= j;
				cursor.M				= m.M;
			}
			cursor.HasPrev = cursor.Valid && cursor.K >= 1;
			if (cursor.HasPrev)
				cursor.Prev = source.At(cursor.K - 1);
			return rebuild ? FEED_REBUILT : FEED_CONTINUED;
		}

		// Whether the cursor's minute is still where it was, with the minute before it unchanged:
		// the feed goes on from it (else the source's history changed: rebuilt).
		static bool Continues(const FeedCursor& cursor, const MinuteSource& source)
		{
			return cursor.Valid && source.Count() >= cursor.K + 1 && source.At(cursor.K).M == cursor.M
				&& (!cursor.HasPrev || source.At(cursor.K - 1) == cursor.Prev);
		}

		// Whether the minutes before the cursor's are the ones the engine took. O(minutes).
		static bool SameHistory(const FeedCursor& cursor, const MinuteSource& source, const FeedClip& clip)
		{
			FeedHistory h;
			for (int64_t j = FirstMinuteAtOrAfter(source, clip.First); j < cursor.K; j++)
			{
				const PvpMinute m = source.At(j);
				if (m.M < clip.First || m.Empty)
					continue;
				if (m.M >= clip.End || m.M > clip.Replay)
					break;
				h.Pending = MinuteHash(m);
				h.Complete();
			}
			return h.Same(cursor.History);
		}
	};

	// ---- Volume at price (spec C.7) ----

	// One volume-at-price element of a bar (Sierra Chart's s_VolumeAtPriceV2).
	struct VapElement
	{
		int			PriceInTicks	= 0;
		uint32_t	Volume			= 0;
		uint32_t	BidVolume		= 0;
		uint32_t	AskVolume		= 0;
	};

	struct VapUnits
	{
		// A bar's elements as one-tick ranges at PriceInTicks (Sierra Chart's price / tick size;
		// a Volume at Price Multiplier only spaces them that many ticks apart): the ask volume
		// up, the bid volume down, volume with neither side split evenly (the Session VP's rule).
		static void Ranges(const std::vector<VapElement>& elements, std::vector<PvpRange>& out)
		{
			out.clear();
			for (const VapElement& e : elements)
			{
				if (e.Volume == 0)
					continue;
				const double volume	= (double)e.Volume;
				const double ask	= (std::min)((double)e.AskVolume, volume);
				const double bid	= (std::min)((double)e.BidVolume, volume - ask);
				const double rest	= volume - ask - bid;
				PvpRange up, down;
				up.Low		= up.High	= e.PriceInTicks;
				down.Low	= down.High	= e.PriceInTicks;
				up.Volume	= ask + rest / 2;
				up.Up		= true;
				down.Volume	= bid + rest / 2;
				down.Up		= false;
				out.push_back(up);
				out.push_back(down);
			}
		}

		// A bar's LastChart: its end; the forming bar's no later than the end of the minute of its
		// newest trade (where the minute source would end it).
		static int64_t Time(int64_t barEnd, bool forming, int64_t latestTrade)
		{
			if (!forming)
				return barEnd;
			const int64_t minuteEnd = FloorDiv(latestTrade + US_PER_MINUTE - 1, US_PER_MINUTE) * US_PER_MINUTE;
			return (std::min)(barEnd, minuteEnd);
		}
	};

	// ---- Text (spec B.9, B.10) ----

	// .NET Framework's custom formats "0" (decimals 0) and "0.#" (decimals 1), as NinjaTrader's
	// label and row text use them: the double rounded to 15 significant digits (half away from
	// zero), then half away from zero to the decimals, trailing zeros dropped. (The Session VP's.)
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

	struct PvpText
	{
		// .NET's "+0;-0;0" (NT:301): a value that rounds to zero uses the zero section, so 0.4
		// and -0.4 print "0"; -0.5 rounds away from zero to "-1".
		static std::string FormatDelta(double delta)
		{
			const std::string magnitude = FormatNet(std::fabs(delta), 0);
			if (magnitude == "0")
				return "0";
			return (delta > 0 ? "+" : "-") + magnitude;
		}

		// A row's text in each volume mode (NT:294, NT:301, NT:306).
		static std::string RowText(int mode, const PvpRow& row)
		{
			if (mode == VM_UP_DOWN)
				return FormatNet(row.Up, 0) + " / " + FormatNet(row.Down, 0);
			if (mode == VM_DELTA)
				return FormatDelta(row.Up - row.Down);
			return FormatNet(row.Total(), 0);
		}
	};

	// One row's bars in a volume mode (NT:285-307; spec D.4): the first and the second bar's
	// lengths in pixels (NinjaTrader's float widths) and their colors' roles.
	struct RowBars
	{
		float	First		= 0;
		float	Second		= 0;
		bool	InValueArea	= false;
		bool	FirstIsDown	= false;	// Delta below 0 draws in the down color
	};

	struct VolumeModes
	{
		static RowBars Of(int mode, const PvpSnapshot& s, int i, float width)
		{
			RowBars b;
			const PvpRow& row = s.Rows[(size_t)i];
			b.InValueArea = i >= s.ValIndex && i <= s.VahIndex;
			if (mode == VM_UP_DOWN)
			{
				b.First		= (float)((double)width * row.Up / s.MaxVolume);
				b.Second	= (float)((double)width * row.Down / s.MaxVolume);
			}
			else if (mode == VM_DELTA)
			{
				const double delta = row.Up - row.Down;
				b.First			= s.MaxAbsDelta > 0 ? (float)((double)width * std::fabs(delta) / s.MaxAbsDelta) : 0;
				b.FirstIsDown	= delta < 0;
			}
			else
				b.First = (float)((double)width * row.Total() / s.MaxVolume);
			return b;
		}
	};

	// NinjaTrader's chart label (DisplayName, NT:113-125; spec B.9).
	struct LabelParts
	{
		bool		ShowInputs	= true;
		bool		ShowValues	= true;
		int			Multiplier	= 1;
		int			Period		= PER_WEEKLY;
		int			Volume		= VM_TOTAL;
		double		Percent		= 68;
		int			RowSize		= 200;
		int			Layout		= RL_NUMBER_OF_ROWS;
		bool		HasValues	= false;
		std::string	Poc;
		std::string	Vah;
		std::string	Val;
	};

	std::string ChartLabel(const LabelParts& p)
	{
		std::string label = "Tatanka PVP";
		if (p.ShowInputs)
			label += " (" + std::to_string(p.Multiplier) + " " + PERIOD_NAMES[(std::max)(0, (std::min)(3, p.Period))] + ", "
				+ VOLUME_NAMES[(std::max)(0, (std::min)(2, p.Volume))] + ", VA " + FormatNet(p.Percent, 1) + "%, " + std::to_string(p.RowSize) + " "
				+ LAYOUT_NAMES[p.Layout == RL_TICKS_PER_ROW ? 1 : 0] + ")";
		if (p.ShowValues && p.HasValues)
			label += "  POC " + p.Poc + "  VAH " + p.Vah + "  VAL " + p.Val;
		return label;
	}

	// Configuration errors in NinjaTrader's order (NT:102-105; spec B.10): not intraday, the tick
	// size (the other settings are kept in range by the input limits); then tick, volume and
	// range bars without end times. Intraday bars of any length are accepted, as NinjaTrader
	// accepts multi-day minute bars (spec A #48).
	const char* ConfigError(int chartDataType, int barPeriodType, int secondsPerBar, bool hasEndTimes, double tick)
	{
		if (chartDataType != INTRADAY_DATA || barPeriodType == IBPT_MONTHS_PER_BAR || barPeriodType == IBPT_HISTORICAL_DAILY_DATA_DAYS_PER_BAR
			|| (barPeriodType == IBPT_DAYS_MINS_SECS && !(secondsPerBar > 0)))
			return MESSAGES[MSG_NOT_INTRADAY];
		if (!(tick > 0))
			return MESSAGES[MSG_BAD_SETTINGS];
		if (barPeriodType != IBPT_DAYS_MINS_SECS && !hasEndTimes)
			return MESSAGES[MSG_NO_END_TIMES];
		return "";
	}

	// ---- This chart's newest data (spec C.5, C.7) ----

	// Sierra Chart's time of the last bar's newest trade (sc.LatestDateTimeForLastBar) when it lies
	// inside that bar (from its start to the end of the time it covers); `fallback` otherwise (a
	// value Sierra Chart has not set yet, or one left from another bar).
	int64_t LatestTime(int64_t latest, int64_t lastStart, int64_t lastCover, int64_t fallback)
	{
		return latest >= lastStart && latest <= lastCover ? latest : fallback;
	}

	// This chart's newest trade for the coverage test (spec C.5): in its last bar that holds trades
	// (empty columns that Include Columns With No Data adds at the end hold none, and the hidden
	// chart has no minute for them), sc.LatestDateTimeForLastBar when it lies in that bar, else the
	// bar's start.
	int64_t NewestTrade(const PvpBars& bars, int64_t latest)
	{
		int j = bars.Count() - 1;
		while (j > 0 && !bars.Touchable[(size_t)j])
			j--;
		if (j < 0)
			return latest;
		const size_t k = (size_t)j;
		return LatestTime(latest, bars.S[k], bars.C[k], bars.S[k]);
	}

	// Whether the hidden 1-minute chart reaches this chart's newest data (spec C.5 readiness): its
	// last minute starts at most a minute before the minute of `newest` (either chart may be a call
	// ahead of the other). Not checked during a replay, where the hidden chart can be ahead.
	bool MinutesCover(int64_t lastMinute, int64_t newest, bool replay)
	{
		return replay || lastMinute >= FloorDiv(newest, US_PER_MINUTE) * US_PER_MINUTE - US_PER_MINUTE;
	}

	// ---- Volume at price feed (spec C.7) ----

	// Sierra Chart's volume at price per chart bar (SierraVap); vectors in the tests.
	struct VapSource
	{
		virtual int BarCount() const = 0;
		virtual void Elements(int bar, std::vector<VapElement>& out) const = 0;

	protected:
		~VapSource() = default;
	};

	// The last bar given to the engine: its index and start, and the bars before it (FeedHistory).
	struct VapCursor
	{
		bool		Valid	= false;
		int			K		= -1;
		int64_t		S		= 0;
		FeedHistory	History;
	};

	uint64_t UnitHash(int64_t id, int64_t dayTime, const std::vector<PvpRange>& ranges)
	{
		const int64_t numbers[2] = {id, dayTime};
		uint64_t hash = Fnv1a64(FNV64_BASIS, numbers, sizeof(numbers));
		for (const PvpRange& r : ranges)
		{
			const int64_t ticks[3] = {r.Low, r.High, r.Up ? 1 : 0};
			hash = Fnv1a64(Fnv1a64(hash, ticks, sizeof(ticks)), &r.Volume, sizeof(r.Volume));
		}
		return hash;
	}

	struct VapFeed
	{
		// One study call with the Volume at price option: this chart's bars are the units (each
		// bar's elements its ranges, its index its order, its start its trading day). As with
		// minutes, the cursor's bar is given again: the engine replaces it while it forms and
		// takes its end time once a later bar exists; a later bar commits it, also one with the
		// same start (Split Data Records splits one record over bars that all start at its time).
		// Bars without volume at price (empty columns) are skipped. Rebuilt from bar 0 when asked
		// (the engine key or this chart's completed bars changed), when the cursor's bar is gone,
		// or, with `verify` (a full recalculation), when a completed bar's volume at price is not
		// what the engine took. latestTrade: the forming bar's newest trade.
		static int Run(PvpEngine& engine, VapCursor& cursor, const PvpBars& bars, const VapSource& source, int64_t latestTrade, bool rebuild,
			bool verify = false)
		{
			const int count	= bars.Count();
			const int n		= (std::min)(count, source.BarCount());
			if (!rebuild && cursor.Valid && (count < cursor.K + 1 || bars.S[(size_t)cursor.K] != cursor.S || (verify && !SameHistory(cursor, bars, source))))
				rebuild = true;
			if (rebuild)
			{
				engine.Reset();
				cursor = VapCursor();
			}
			std::vector<VapElement> elements;
			std::vector<PvpRange> ranges;
			for (int j = cursor.Valid ? cursor.K : 0; j < n; j++)
			{
				source.Elements(j, elements);
				VapUnits::Ranges(elements, ranges);
				if (ranges.empty())
					continue;
				const size_t k = (size_t)j;
				engine.Unit(j, bars.S[k], VapUnits::Time(bars.E[k], j == count - 1, latestTrade), ranges);
				if (cursor.Valid && j != cursor.K)
					cursor.History.Complete();	// a later bar: the cursor's is complete
				cursor.History.Pending	= UnitHash(j, bars.S[k], ranges);
				cursor.Valid			= true;
				cursor.K				= j;
				cursor.S				= bars.S[k];
			}
			return rebuild ? FEED_REBUILT : FEED_CONTINUED;
		}

		// Whether the bars before the cursor's hold the volume at price the engine took. O(elements).
		static bool SameHistory(const VapCursor& cursor, const PvpBars& bars, const VapSource& source)
		{
			FeedHistory h;
			std::vector<VapElement> elements;
			std::vector<PvpRange> ranges;
			const int n = (std::min)(cursor.K, (std::min)(bars.Count(), source.BarCount()));
			for (int j = 0; j < n; j++)
			{
				source.Elements(j, elements);
				VapUnits::Ranges(elements, ranges);
				if (ranges.empty())
					continue;
				h.Pending = UnitHash(j, bars.S[(size_t)j], ranges);
				h.Complete();
			}
			return h.Same(cursor.History);
		}
	};

	// ---- Drawing geometry (spec D; no Sierra Chart calls) ----

	// The pixel boundary at which an aliased fill of the float edge v starts or stops: Direct2D
	// paints a pixel when its center is inside the shape (the Session VP's rule).
	int PixEdge(double v)
	{
		return (int)std::ceil(v - 0.5);
	}

	// Where time t falls on the chart (spec D.1), NinjaTrader's GetXByTime on its bars stamped at
	// their ends, as a fractional bar index (i + f: f of the way from bar i's center to bar i + 1's).
	// Inside bar i it interpolates between the centers of bars i - 1 and i; in a gap before bar i
	// (a session break, the weekend) it stays at bar i - 1's center, so a period that starts on
	// Sunday 17:00 begins at Friday's last bar and a finished period ends at its own last bar.
	// Past the last bar: time bars extrapolate by its length, tick, volume and range bars stay at
	// its center (they have no time axis there). Empty columns count: they are on the time axis.
	double PvpPosition(const PvpBars& bars, int64_t t, bool timeBars)
	{
		const int n = bars.Count();
		if (n == 0)
			return 0;
		const size_t i = (size_t)(std::lower_bound(bars.E.begin(), bars.E.end(), t) - bars.E.begin());
		double f;
		if (i == (size_t)n)
		{
			const size_t last		= (size_t)n - 1;
			const int64_t length	= bars.E[last] - bars.S[last];
			f = (double)last + (timeBars && length > 0 ? (double)(t - bars.E[last]) / (double)length : 0.0);
		}
		else
		{
			const int64_t length	= bars.E[i] - bars.S[i];
			const double inside		= length > 0 ? (double)(t - bars.S[i]) / (double)length : (t >= bars.S[i] ? 1.0 : 0.0);
			f = (double)i - 1 + (std::max)(0.0, (std::min)(1.0, inside));
		}
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

	// The loaded bar whose center is nearest a fractional bar position.
	int NearestBar(double position, int count)
	{
		return (int)(std::max)(0.0, (std::min)((double)(count - 1), std::floor(position + 0.5)));
	}

	// A profile's horizontal layout in pixels (NT:258-267, spec D.3). NinjaTrader's pixel
	// constants are DIPs: times scale.
	struct ProfileLayout
	{
		double	Left		= 0;	// the period's start; pinned: the histogram's left
		double	Right		= 0;	// the period's end; pinned: the panel's right less the padding
		double	Width		= 0;	// the longest row
		bool	AlignLeft	= true;	// rows grow right from Left (Left placement), else left from Right
		double	BoxLeft		= 0;	// the histogram box
		double	BoxRight	= 0;
	};

	ProfileLayout LayoutProfile(int placement, int periodLeft, int periodRight, double panelLeft, double panelRight, int padding,
		double widthPercent, double scale)
	{
		ProfileLayout l;
		l.Left				= (double)periodLeft;
		l.Right				= (double)periodRight;
		const double span	= (std::max)(2 * scale, l.Right - l.Left);
		l.Width				= span * widthPercent / 100;
		if (placement == PL_CHART_RIGHT_LATEST)
		{
			l.Right	= panelRight - padding * scale;
			l.Width	= (std::max)(1 * scale, (panelRight - panelLeft) * widthPercent / 100);
			l.Left	= l.Right - l.Width;
		}
		l.AlignLeft	= placement == PL_LEFT;
		// The box covers the whole period in Left and Right (the rows only part of it), the
		// histogram when pinned.
		l.BoxLeft	= l.Left;
		l.BoxRight	= l.Left + (std::max)(1 * scale, l.Right - l.Left);
		return l;
	}

	// One row between the pixel rows of its high and low edges (NT:273-314, spec D.4): a gap of
	// RowGap DIPs (at most 35 % of the row) split above and below, rows below 0.15 DIPs kept
	// sub-pixel (they paint nothing), the bars from the anchor: the first bar then the second
	// left to right in every placement (NT:308-310).
	struct RowRect
	{
		bool	Visible	= false;
		double	Full	= 0;	// the row's height
		double	Y		= 0;	// top of the painted part
		double	H		= 0;	// its height
		double	Left	= 0;	// left end of the first bar
		RowBars	Bars;
	};

	RowRect LayoutRow(int yHigh, int yLow, int panelTop, int panelBottom, const ProfileLayout& l, const RowBars& bars, int rowGap, double scale)
	{
		RowRect r;
		const int top		= (std::min)(yHigh, yLow);
		const int bottom	= (std::max)(yHigh, yLow);
		if (bottom < panelTop || top > panelBottom)
			return r;
		r.Visible	= true;
		r.Full		= (double)(bottom - top);
		r.H			= (std::max)(0.15 * scale, r.Full - (std::min)(rowGap * scale, r.Full * 0.35));
		r.Y			= top + (r.Full - r.H) / 2;
		r.Bars		= bars;
		r.Left		= l.AlignLeft ? l.Left : l.Right - (double)bars.First - (double)bars.Second;
		return r;
	}

	// The row text shows on rows at least 12 DIPs tall whose bars are at least 55 DIPs (NT:311).
	bool RowTextFits(double fullHeight, double barsWidth, double scale)
	{
		return fullHeight >= 12 * scale && barsWidth >= 55 * scale;
	}

	// Where a level line ends (NT:335-338, spec D.6): at the profile's right without Extend;
	// extended, at the touching bar's center (never left of the profile's right) while
	// UntilTouched has a touch, otherwise at the panel's right edge.
	double LevelEnd(double right, double panelRight, bool extend, bool untilTouched, bool touched, double touchX)
	{
		if (!extend)
			return right;
		return untilTouched && touched ? (std::max)(right, touchX) : panelRight;
	}

	// The level label's left edge (NT:344): `offset` DIPs right of the profile, kept 110 DIPs
	// from the panel's right edge and 4 inside its left. dip(x): x DIPs in whole pixels.
	template <typename Dip>
	double LevelLabelX(double panelLeft, double panelRight, double right, double offset, Dip dip)
	{
		return (std::max)(panelLeft + dip(4), (std::min)(right + dip(offset), panelRight - dip(110)));
	}

	// The bars a translucent box range runs between (spec D.5): those whose centers are nearest
	// the profile's left and right edges. False when both are one bar (the callback blends it).
	// A range spans whole bars and is set in the study call, not per frame: the developing
	// profile's edge rounds to the nearest bar center (its rows end at the exact minute), and a
	// range of a period starting after the last visible bar still shows its first half bar there
	// (NinjaTrader skips such a profile, NT:254). Blending those slivers in the callback would hide
	// the bars under them, which is what the translucent range is for.
	bool BoxBars(int64_t startChart, int64_t lastChart, const PvpBars& bars, bool timeBars, int& startBar, int& endBar)
	{
		const int n = bars.Count();
		if (n == 0)
			return false;
		startBar	= NearestBar(PvpPosition(bars, startChart, timeBars), n);
		endBar		= NearestBar(PvpPosition(bars, lastChart, timeBars), n);
		return startBar < endBar;
	}

	// One profile's translucent box as a Sierra Chart range: from the start bar's center to the
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

	// The box ranges of the retained profiles that have rows, sorted by RangeKey. Profiles sharing
	// a start bar get the next id.
	std::vector<BoxPiece> BoxPieces(const std::deque<PvpProfile>& profiles, const PvpBars& bars, bool timeBars)
	{
		std::vector<BoxPiece> out;
		for (const PvpProfile& p : profiles)
		{
			const PvpSnapshot& s = p.View();
			BoxPiece b;
			if (!s.HasRows() || !(s.MaxVolume > 0) || !BoxBars(p.StartChart, p.LastChart, bars, timeBars, b.StartBar, b.EndBar))
				continue;
			b.Top		= s.HighEdge;
			b.Bottom	= s.LowEdge;
			for (const BoxPiece& o : out)
				if (o.StartBar == b.StartBar)
					b.Id = (std::max)(b.Id, o.Id + 1);
			out.push_back(b);
		}
		std::sort(out.begin(), out.end(), [](const BoxPiece& a, const BoxPiece& b) { return RangeKey(a.StartBar, a.Id) < RangeKey(b.StartBar, b.Id); });
		return out;
	}

	using TextMeasure = std::function<int(const std::string&)>;

	// Greedy word wrap at spaces (NinjaTrader's DirectWrite layout box): a line breaks before the
	// word that would overflow it, and a word wider than the width stays whole.
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

	// ---- Sierra Chart glue ----

	// The level colors and the hidden levels' scale labels (spec A #5, D.10): a hidden level keeps
	// its values, only its label goes.
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
		p.Multiplier	= sc.Input[IN_MULTIPLIER].GetInt();
		p.Period		= (std::min)((int)sc.Input[IN_PERIOD].GetIndex(), (int)PER_YEARLY);
		p.Volume		= (std::min)((int)sc.Input[IN_VOLUME_MODE].GetIndex(), (int)VM_DELTA);
		p.Percent		= sc.Input[IN_VA_PERCENT].GetDouble();
		p.RowSize		= sc.Input[IN_ROW_SIZE].GetInt();
		p.Layout		= (std::min)((int)sc.Input[IN_ROWS_LAYOUT].GetIndex(), (int)RL_TICKS_PER_ROW);
		return p;
	}

	// A price as the chart shows it (NinjaTrader's FormatPriceMarker, NT:127-128).
	std::string Price(SCStudyInterfaceRef sc, double price)
	{
		const SCString text = sc.FormatGraphValue(price, sc.BaseGraphValueFormat);
		return text.GetChars();
	}

	int64_t Micros(const SCDateTime& t)
	{
		return t.AsMicrosecondsSinceBaseDate();
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

	// The engine inputs (spec B.2: inputs 0, 1 and 3-7, the tick size), kept in their limits.
	PvpSettings SettingsOf(SCStudyInterfaceRef sc, double tick)
	{
		PvpSettings s;
		s.Period			= (std::max)(0, (std::min)((int)sc.Input[IN_PERIOD].GetIndex(), (int)PER_YEARLY));
		s.Multiplier		= (std::max)(1, (std::min)(100, sc.Input[IN_MULTIPLIER].GetInt()));
		s.Keep				= (std::max)(1, (std::min)(100, sc.Input[IN_PROFILES].GetInt()));
		s.Profile.Tick		= tick;
		s.Profile.Layout	= (std::min)((int)sc.Input[IN_ROWS_LAYOUT].GetIndex(), (int)RL_TICKS_PER_ROW);
		s.Profile.RowSize	= (std::max)(1, (std::min)(5000, sc.Input[IN_ROW_SIZE].GetInt()));
		s.Profile.Percent	= (std::max)(1.0, (std::min)(100.0, sc.Input[IN_VA_PERCENT].GetDouble()));
		s.Profile.AtLeast	= (int)sc.Input[IN_VA_METHOD].GetIndex() == VAM_ATLEAST;
		return s;
	}

	// NinjaTrader's ActualTradingDayExchange.Date and ActualSessionBegin (spec B.5): Sierra Chart's
	// trading day from this chart's Session Times.
	TradingDayInfo SierraTradingDay(SCStudyInterfaceRef sc, int64_t t)
	{
		const SCDateTime time = SCDateTime::MICROSECONDS(t);
		TradingDayInfo d;
		d.Date	= sc.GetTradingDayDate(time);
		d.Start	= Micros(sc.GetTradingDayStartDateTimeOfBar(time));
		return d;
	}

	// Sierra Chart's volume at price per bar (sc.VolumeAtPriceForBars, spec C.7).
	struct SierraVap final : VapSource
	{
		const c_VAPContainer*	Vap	= nullptr;

		int BarCount() const override
		{
			return Vap != nullptr ? (int)Vap->GetNumberOfBars() : 0;
		}

		void Elements(int bar, std::vector<VapElement>& out) const override
		{
			out.clear();
			if (Vap == nullptr || bar < 0 || (unsigned int)bar >= Vap->GetNumberOfBars())
				return;
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
		}
	};

	// Everything the study keeps between calls (one heap object per study instance).
	struct StudyState
	{
		std::string		Error;							// configuration error for the drawing callback
		int				Message			= MSG_WAITING;	// drawn while no profile is shown (spec C.8)
		bool			Showing			= false;		// the source is ready: the profiles are shown
		bool			Waiting			= false;		// Sierra Chart is asked to call again (UpdateAlways)

		// The engine and what it was built from (spec C.3-C.7).
		bool			Built			= false;
		uint32_t		EngineKey		= 0;
		int				Kind			= SRC_NONE;
		PvpEngine		Engine;
		FeedCursor		Cursor;			// minutes (this chart's or the hidden chart's)
		VapCursor		VapAt;			// bars (Volume at price)
		OwnMinutes		Own;
		PvpBars			Bars;			// this chart's bars: touches, x positions
		bool			TimeBars		= true;
		double			Tick			= 0;
		bool			TouchesStale	= false;		// this chart's bars changed: the touches are found again

		// NinjaTrader's latestPoc/latestVah/latestVal (NT:192-206): the newest profile's levels as
		// last published; kept while the newest profile has no rows (spec B.8, D.9).
		bool			Published		= false;
		double			PublishedPoc	= 0;
		double			PublishedVah	= 0;
		double			PublishedVal	= 0;

		// The hidden 1-minute chart (spec C.5): resolved at least once, the symbol it was requested
		// for and the symbol it held then; whether the chart found did not match this chart;
		// whether the engine reads it live (it covered this chart's data when last fed).
		bool			MinuteResolved	= false;
		std::string		MinuteRequested;
		std::string		MinuteSymbol;
		bool			MinuteMismatch	= false;
		bool			HiddenReady		= false;

		// Translucent box ranges sent to Sierra Chart: (start bar, id) -> signature.
		std::map<uint64_t, uint32_t>	Sent;
		uint32_t						RangesKey	= 0;

		// Diagnostics (tests, harness).
		int		Rebuilds		= 0;
		int		Resolves		= 0;
		int		RangeAdds		= 0;
		int		RangeDeletes	= 0;
		int		ValueClears		= 0;

		// Frees the engine (a configuration error, no bars, inputs changed while waiting): built
		// again from the first minute when the source is ready.
		void ResetEngine()
		{
			Built		= false;
			EngineKey	= 0;
			Engine		= PvpEngine();
			Cursor		= FeedCursor();
			VapAt		= VapCursor();
			Own.Clear();
			Published	= false;
			HiddenReady	= false;
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

	// This chart's bars from `from` on (spec B.3): start, end (NinjaTrader's close stamp), the
	// time they cover, the ticks of their low and high, and whether they can touch.
	void ReadBars(SCStudyInterfaceRef sc, PvpBars& bars, int from, bool timeBars, double tick)
	{
		const int n = sc.ArraySize;
		bars.Resize(n);
		const ChartSessions sessions = SessionsOf(sc);
		for (int i = (std::max)(0, from); i < n; i++)
		{
			const int64_t start	= Micros(sc.BaseDateTimeIn[i]);
			const bool hasNext	= i + 1 < n;
			const int64_t next	= hasNext ? Micros(sc.BaseDateTimeIn[i + 1]) : 0;
			const bool empty	= IsEmptyColumn(sc.Volume[i], sc.NumberOfTrades[i], sc.Open[i], sc.High[i], sc.Low[i], sc.Close[i], i > 0,
				i > 0 ? sc.Close[i - 1] : 0.0f);
			if (timeBars)
				bars.SetTimeBar(i, start, sc.SecondsPerBar, hasNext, next, sessions, empty, sc.Low[i], sc.High[i], tick);
			else
				bars.SetTradeBar(i, start, Micros(sc.BaseDataEndDateTime[i]), hasNext, next, empty, sc.Low[i], sc.High[i], tick);
		}
	}

	std::string ChartSymbol(SCStudyInterfaceRef sc, int chartNumber)
	{
		const SCString symbol = sc.GetChartSymbol(chartNumber);
		return symbol.GetChars();
	}

	// Equal Session Times as far as they decide which minutes exist: the day session, the evening
	// session when it is used, and whether weekend data loads.
	bool SameSessionTimes(const n_ACSIL::s_ChartSessionTimes& a, const n_ACSIL::s_ChartSessionTimes& b)
	{
		if (a.StartTime.GetTimeInSeconds() != b.StartTime.GetTimeInSeconds() || a.EndTime.GetTimeInSeconds() != b.EndTime.GetTimeInSeconds()
			|| (a.UseEveningSessionTimes != 0) != (b.UseEveningSessionTimes != 0) || a.LoadWeekendDataSetting != b.LoadWeekendDataSetting)
			return false;
		return a.UseEveningSessionTimes == 0 || (a.EveningStartTime.GetTimeInSeconds() == b.EveningStartTime.GetTimeInSeconds()
			&& a.EveningEndTime.GetTimeInSeconds() == b.EveningEndTime.GetTimeInSeconds());
	}

	// Whether chart `chart` holds this chart's minutes (spec C.5): 1-minute intraday bars with this
	// chart's Session Times and time zone.
	bool MinuteChartMatches(SCStudyInterfaceRef sc, int chart)
	{
		n_ACSIL::s_BarPeriod period;
		sc.GetBarPeriodParametersForChart(chart, period);
		if (period.ChartDataType != INTRADAY_DATA || period.IntradayChartBarPeriodType != IBPT_DAYS_MINS_SECS
			|| period.IntradayChartBarPeriodParameter1 != 60)
			return false;
		n_ACSIL::s_ChartSessionTimes mine, theirs;
		sc.GetSessionTimesFromChart(sc.ChartNumber, mine);
		sc.GetSessionTimesFromChart(chart, theirs);
		if (!SameSessionTimes(mine, theirs))
			return false;
		const SCString zone = sc.GetChartTimeZone(chart);
		return zone == sc.GetChartTimeZone(sc.ChartNumber);
	}

	// The hidden chart's Days to Load: 0 takes this chart's (Sierra Chart's documented meaning);
	// with Load Chart Data by Date Range, the days from its start date to today.
	int MinuteDaysToLoad(SCStudyInterfaceRef sc)
	{
		if (sc.LoadChartDataByDateRange == 0 || sc.ChartDataStartDate <= 0)
			return 0;
		return (std::max)(1, sc.CurrentSystemDateTime.GetDate() - sc.ChartDataStartDate + 1);
	}

	// A hidden 1-minute chart of this chart's symbol, continuous-contract option, Session Times,
	// time zone and Days to Load, found or opened (spec C.5). Sierra Chart hands every chart and
	// study asking for the same settings the same chart, so it is never rewritten
	// (UpdatePriorChartNumberParametersToMatch = 0): a mismatch finds or opens another one.
	int OpenMinuteChart(SCStudyInterfaceRef sc, int prior)
	{
		n_ACSIL::s_ChartSessionTimes times;
		sc.GetSessionTimesFromChart(sc.ChartNumber, times);
		s_ACSOpenChartParameters p;
		p.PriorChartNumber			= prior;
		p.ChartDataType				= INTRADAY_DATA;
		p.Symbol					= sc.GetRealTimeSymbol();
		p.IntradayBarPeriodType		= IBPT_DAYS_MINS_SECS;
		p.IntradayBarPeriodLength	= 60;
		p.DaysToLoad				= MinuteDaysToLoad(sc);
		p.SessionStartTime.SetTime(sc.StartTime1);
		p.SessionEndTime.SetTime(sc.EndTime1);
		p.EveningSessionStartTime.SetTime(sc.StartTime2);
		p.EveningSessionEndTime.SetTime(sc.EndTime2);
		p.UseEveningSession			= sc.UseSecondStartEndTimes != 0 ? 1 : 0;
		p.LoadWeekendData			= times.LoadWeekendDataSetting;
		p.ContinuousFuturesContractOption = sc.ContinuousFuturesContractOption;
		p.ChartTimeZone				= sc.GetChartTimeZone(sc.ChartNumber);
		p.IncludeColumnsWithNoData	= 0;	// NinjaTrader's minute series has no empty minutes
		p.HideNewChart				= 1;
		p.UpdatePriorChartNumberParametersToMatch = 0;
		return sc.OpenChartOrGetChartReference(p);
	}

	// The hidden chart's number (0: none), resolved on a full recalculation (as Sierra Chart
	// advises), while there is none, when this chart's symbol changed, and when the chart no
	// longer holds what it held (another symbol, bar period, Session Times or time zone: then
	// without it as the prior chart). A chart found that does not match is not used: it is looked
	// for again on the next full recalculation.
	int ResolveMinuteChart(SCStudyInterfaceRef sc, StudyState& st)
	{
		int& chart = sc.GetPersistentInt(PI_MINUTE_CHART);
		const std::string symbol = sc.GetRealTimeSymbol().GetChars();
		const bool newSymbol = !st.MinuteResolved || symbol != st.MinuteRequested;
		if (st.MinuteMismatch && !sc.IsFullRecalculation && !newSymbol)
			return 0;
		int prior = chart;
		bool resolve = sc.IsFullRecalculation || chart == 0 || newSymbol;
		if (!resolve && (ChartSymbol(sc, chart) != st.MinuteSymbol || !MinuteChartMatches(sc, chart)))
		{
			resolve	= true;
			prior	= 0;
		}
		if (!resolve)
			return chart;
		st.MinuteMismatch = false;
		for (int attempt = 0; attempt < 2; attempt++)
		{
			chart = OpenMinuteChart(sc, prior);
			st.Resolves++;
			if (chart == 0 || MinuteChartMatches(sc, chart))
				break;
			if (prior == 0 || attempt == 1)
			{
				chart				= 0;
				st.MinuteMismatch	= true;
				break;
			}
			prior = 0;
		}
		st.MinuteResolved	= true;
		st.MinuteRequested	= symbol;
		st.MinuteSymbol		= chart != 0 ? ChartSymbol(sc, chart) : std::string();
		return chart;
	}

	// What the engine is built from (spec C.6): a change rebuilds it from the first minute.
	uint32_t EngineKeyOf(SCStudyInterfaceRef sc, const PvpSettings& s, int kind, int chart, int64_t first, bool timeBars)
	{
		const int64_t numbers[] = {s.Period, s.Multiplier, s.Keep, s.Profile.Layout, s.Profile.RowSize, s.Profile.AtLeast ? 1 : 0, kind, chart, first,
			timeBars ? 1 : 0, sc.SecondsPerBar, sc.StartTime1, sc.EndTime1, sc.StartTime2, sc.EndTime2, sc.UseSecondStartEndTimes,
			sc.NewBarAtSessionStart, kind == SRC_VAP ? (int64_t)sc.VolumeAtPriceMultiplier : 0};
		uint32_t key = Fnv1a(2166136261u, numbers, sizeof(numbers));
		const double doubles[] = {s.Profile.Percent, s.Profile.Tick};
		key = Fnv1a(key, doubles, sizeof(doubles));
		const SCString zone = sc.GetChartTimeZone(sc.ChartNumber);
		key = Fnv1a(key, zone.GetChars(), (size_t)zone.GetLength());
		return key == 0 ? 1 : key;
	}

	// A message for the message log, under the study's name (a drawn text's short
	// "Tatanka PVP: " is left out there).
	std::string LogText(const char* message)
	{
		const std::string text = message;
		const std::string drawnPrefix = "Tatanka PVP: ";
		return LOG_PREFIX + (text.compare(0, drawnPrefix.size(), drawnPrefix) == 0 ? text.substr(drawnPrefix.size()) : text);
	}

	// The levels shown while the profiles are shown (spec A #6, B.7 Values, D.9): NinjaTrader's
	// latestPoc, the newest profile's levels as last published (the newest profile's current
	// levels when it has rows).
	bool ShownLevels(const StudyState& st, double& poc, double& vah, double& val)
	{
		if (!st.Showing || !st.Error.empty() || !st.Published)
			return false;
		poc = st.PublishedPoc;
		vah = st.PublishedVah;
		val = st.PublishedVal;
		return true;
	}

	bool NewestHasRows(const StudyState& st)
	{
		return !st.Engine.Profiles.empty() && st.Engine.Profiles.back().View().HasRows();
	}

	// POC, VAH and VAL on the last bar only (spec B.8, NinjaTrader's "the price box is current
	// only"): bars that were the last keep what was written then; a rebuild or a full
	// recalculation clears every bar first.
	void WriteValues(SCStudyInterfaceRef sc, StudyState& st, bool clearAll)
	{
		const int n = sc.ArraySize;
		if (clearAll)
		{
			for (int i = 0; i < n; i++)
				sc.Subgraph[SG_POC][i] = sc.Subgraph[SG_VAH][i] = sc.Subgraph[SG_VAL][i] = 0.0f;
			st.ValueClears++;
		}
		if (n == 0)
			return;
		double poc = 0, vah = 0, val = 0;
		const bool has = ShownLevels(st, poc, vah, val);
		// While the newest profile has no rows NinjaTrader's Publish returns before it writes
		// (NT:200): the last bar keeps what it holds, a new bar gets nothing.
		if (has && !NewestHasRows(st))
			return;
		sc.Subgraph[SG_POC][n - 1] = has ? (float)poc : 0.0f;
		sc.Subgraph[SG_VAH][n - 1] = has ? (float)vah : 0.0f;
		sc.Subgraph[SG_VAL][n - 1] = has ? (float)val : 0.0f;
	}

	// NinjaTrader's chart label (spec B.9) in the study's Short Name (D.9), rewritten only when
	// it changes.
	void UpdateLabel(SCStudyInterfaceRef sc, const StudyState* st)
	{
		LabelParts p = LabelOf(sc);
		double poc = 0, vah = 0, val = 0;
		if (st != nullptr && ShownLevels(*st, poc, vah, val))
		{
			p.HasValues	= true;
			p.Poc		= Price(sc, poc);
			p.Vah		= Price(sc, vah);
			p.Val		= Price(sc, val);
		}
		const std::string label = ChartLabel(p);
		if (!(sc.GraphShortName == label.c_str()))
			sc.GraphShortName = label.c_str();
	}

	// Reads this chart's new bars, picks the source (spec C.3), checks that it is ready (C.4,
	// C.5, C.7), gives the engine what is new (C.6), and keeps what the drawing needs. A full
	// recalculation keeps the engine when the engine key is the same and the source still holds
	// what was read (editing a color reads nothing again); otherwise it is rebuilt from the
	// first minute.
	void ProcessCall(SCStudyInterfaceRef sc, StudyState& st, bool timeBars)
	{
		const double tick	= DecimalTickSize(sc.TickSize);
		const int n			= sc.ArraySize;
		const int oldCount	= st.Bars.Count();
		const bool fullRead	= sc.IsFullRecalculation || oldCount == 0 || n < oldCount || st.TimeBars != timeBars || st.Tick != tick
			|| sc.UpdateStartIndex < oldCount - 1;
		// Whether the completed bars changed (a reload with other data): the touches are found
		// again, and the volume-at-price engine is rebuilt.
		bool barsChanged = false;
		if (fullRead)
		{
			PvpBars fresh;
			ReadBars(sc, fresh, 0, timeBars, tick);
			barsChanged	= oldCount > 1 && !fresh.SameAs(st.Bars, oldCount - 1);
			st.Bars		= std::move(fresh);
			// Kept until the engine runs (this call may only wait for the source).
			st.TouchesStale = st.TouchesStale || barsChanged;
		}
		else
			ReadBars(sc, st.Bars, (std::max)(0, (std::min)(sc.UpdateStartIndex, oldCount - 1)), timeBars, tick);
		st.TimeBars	= timeBars;
		st.Tick		= tick;
		// A full recalculation is NinjaTrader's reload, which publishes only at the end of the
		// history: the levels published before it go (spec D.9).
		if (sc.IsFullRecalculation)
			st.Published = false;

		if (n == 0)
		{
			st.ResetEngine();
			st.Showing	= false;
			st.Waiting	= false;
			st.Message	= MSG_WAITING;
			return;
		}

		// Volume at price is kept only for that option (it costs memory); turning it on reloads
		// the chart once so Sierra Chart builds it (Sierra Chart's own studies do the same).
		const int volumeData = (std::min)((int)sc.Input[IN_VOLUME_DATA].GetIndex(), (int)VD_VAP);
		if (volumeData == VD_VAP)
		{
			if (sc.MaintainVolumeAtPriceData == 0)
			{
				sc.MaintainVolumeAtPriceData	= 1;
				sc.FlagToReloadChartData		= 1;
			}
		}
		else
			sc.MaintainVolumeAtPriceData = 0;

		// The source (spec C.3): this chart's bars when they are minutes (or whole parts of
		// minutes), else the hidden 1-minute chart; volume at price when chosen.
		const bool ownLength = volumeData != VD_VAP && SourcePlan::OwnBarLength(timeBars, sc.SecondsPerBar);
		if (ownLength)
		{
			if (st.Own.SecondsPerBar != sc.SecondsPerBar || st.Own.Tick != tick)
			{
				st.Own.Clear();
				st.Own.SecondsPerBar	= sc.SecondsPerBar;
				st.Own.Tick				= tick;
			}
			st.Own.Update(n, fullRead ? 0 : sc.UpdateStartIndex, [&sc](int i)
			{
				return OwnBar::Make(Micros(sc.BaseDateTimeIn[i]), sc.Open[i], sc.High[i], sc.Low[i], sc.Close[i], sc.Volume[i], sc.NumberOfTrades[i],
					i > 0, i > 0 ? sc.Close[i - 1] : 0.0f);
			});
		}
		else
			st.Own.Clear();
		const int kind = SourcePlan::Choose(volumeData, ownLength, st.Own.Aligned());

		// The minutes taken (spec A #17): from the minute of this chart's first bar (on second,
		// tick, volume and range bars its first trade falls inside a minute: that whole minute, as
		// NinjaTrader's minute series of the same days holds it) to the end of the time its last
		// bar covers, during a replay up to the replay's time.
		const size_t last		= (size_t)n - 1;
		const bool replay		= sc.IsReplayRunning() != 0;
		const int64_t latestRaw	= Micros(sc.LatestDateTimeForLastBar);
		FeedClip clip;
		clip.First	= FloorDiv(st.Bars.S[0], US_PER_MINUTE) * US_PER_MINUTE;
		clip.End	= st.Bars.C[last];
		if (replay)
			clip.Replay = LatestTime(latestRaw, st.Bars.S[last], st.Bars.C[last], INT64_MAX);

		const int chart = kind == SRC_HIDDEN ? ResolveMinuteChart(sc, st) : 0;
		const PvpSettings settings	= SettingsOf(sc, tick);
		const uint32_t key			= EngineKeyOf(sc, settings, kind, chart, clip.First, timeBars);
		bool rebuild = !st.Built || key != st.EngineKey || (kind == SRC_VAP && barsChanged);
		// The clip moved back past the last minute taken (a replay started again, a reload with
		// fewer bars): those minutes must go.
		if (kind != SRC_VAP && st.Cursor.Valid && (st.Cursor.M >= clip.End || st.Cursor.M > clip.Replay))
			rebuild = true;

		// Readiness (spec C.8). The hidden chart's arrays are read in place.
		int message = -1;
		SCGraphData data;
		SCDateTimeArray times;
		ArrayMinutes<SCDateTimeArray, SCFloatArray> hidden;
		SierraVap vap;
		if (kind == SRC_HIDDEN && chart == 0)
		{
			message = MSG_NO_MINUTE_CHART;
			int& logged = sc.GetPersistentInt(PI_NO_CHART_LOGGED);
			if (logged == 0)
				sc.AddMessageToLog(LogText(MESSAGES[MSG_NO_MINUTE_CHART]).c_str(), 0);
			logged = 1;
		}
		else if (sc.ChartIsDownloadingHistoricalData(sc.ChartNumber) != 0)
			message = MSG_WAITING;
		else if (kind == SRC_HIDDEN)
		{
			sc.GetPersistentInt(PI_NO_CHART_LOGGED) = 0;
			sc.GetChartBaseData(chart, data);
			sc.GetChartDateTimeArray(chart, times);
			int count = times.GetArraySize();
			const int columns[] = {SC_OPEN, SC_HIGH, SC_LOW, SC_LAST, SC_VOLUME};
			for (int column : columns)
				count = (std::min)(count, data[column].GetArraySize());
			if (count <= 0 || sc.ChartIsDownloadingHistoricalData(chart) != 0)
				message = MSG_WAITING;
			else
			{
				hidden.Times	= &times;
				hidden.Open		= &data[SC_OPEN];
				hidden.High		= &data[SC_HIGH];
				hidden.Low		= &data[SC_LOW];
				hidden.Close	= &data[SC_LAST];
				hidden.Volume	= &data[SC_VOLUME];
				hidden.Trades	= data[SC_NUM_TRADES].GetArraySize() >= count ? &data[SC_NUM_TRADES] : nullptr;
				hidden.N		= count;
				hidden.Tick		= tick;
				// Coverage: the hidden chart must reach this chart's newest trade before the engine
				// is built from it, and again after a rebuild, a download or a reload of the hidden
				// chart (the cursor's minute gone). Once it has, it may lag this chart by a call
				// (Sierra Chart updates the charts in its own order): after a quiet minute or a
				// session break it has no minute yet for this chart's newest trade, which then comes
				// a call later (the feed replaces the forming minute) instead of hiding everything.
				const bool continues = st.HiddenReady && !rebuild && MinuteFeed::Continues(st.Cursor, hidden);
				if (!continues && !MinutesCover(Micros(times[count - 1]), NewestTrade(st.Bars, latestRaw), replay))
					message = MSG_WAITING;
			}
		}
		else if (kind == SRC_VAP)
		{
			vap.Vap = sc.VolumeAtPriceForBars;
			if (vap.Vap == nullptr || vap.BarCount() < n)
				message = MSG_WAITING_VAP;
		}
		st.Kind = kind;
		if (message >= 0)
		{
			// Nothing is shown while the history is incomplete: a half-loaded profile would pass
			// for NinjaTrader's complete one. Profiles of other inputs go at once.
			if (rebuild)
				st.ResetEngine();
			st.Showing		= false;
			st.HiddenReady	= false;
			// A chart found that does not match is looked for again only on a full
			// recalculation: no polling meanwhile.
			st.Waiting	= !(message == MSG_NO_MINUTE_CHART && st.MinuteMismatch);
			st.Message	= message;
			return;
		}

		if (rebuild)
			st.Engine.Cfg = settings;
		st.Engine.Days.Lookup = [&sc](int64_t t) { return SierraTradingDay(sc, t); };
		// A full read also checks every completed minute (bar) against what the engine took: a
		// correction, a backfill or a back-adjustment in mid-history rebuilds (spec A #25, C.6).
		int result = FEED_CONTINUED;
		if (kind == SRC_OWN)
			result = MinuteFeed::Run(st.Engine, st.Cursor, st.Own, clip, rebuild, fullRead);
		else if (kind == SRC_HIDDEN)
			result = MinuteFeed::Run(st.Engine, st.Cursor, hidden, clip, rebuild, fullRead);
		else
		{
			const int64_t latestTrade = LatestTime(latestRaw, st.Bars.S[last], st.Bars.C[last], st.Bars.E[last]);
			result = VapFeed::Run(st.Engine, st.VapAt, st.Bars, vap, latestTrade, rebuild, fullRead);
		}
		if (result == FEED_REBUILT)
		{
			st.Rebuilds++;
			if (kind == SRC_VAP)
				st.Cursor = FeedCursor();
			else
				st.VapAt = VapCursor();
		}
		st.Built		= true;
		st.EngineKey	= key;
		st.HiddenReady	= kind == SRC_HIDDEN;
		st.Engine.UpdateSnapshots();
		// NinjaTrader's Publish (NT:192-206): the newest profile's levels once it has rows. While
		// it has none (a period opening with a zero-volume or rejected minute), the levels
		// published last stay. A rebuild is NinjaTrader's reload: nothing published before it.
		if (result == FEED_REBUILT)
			st.Published = false;
		double poc = 0, vah = 0, val = 0;
		if (st.Engine.NewestLevels(poc, vah, val))
		{
			st.Published	= true;
			st.PublishedPoc	= poc;
			st.PublishedVah	= vah;
			st.PublishedVal	= val;
		}
		// Touches (spec B.7): found again when the bars changed (a rebuilt engine has none
		// yet); tested only while UntilTouched.
		if (st.TouchesStale && result != FEED_REBUILT)
			PvpTouches::Reset(st.Engine);
		st.TouchesStale = false;
		if ((int)sc.Input[IN_EXTENSION].GetIndex() == EXT_UNTIL_TOUCHED)
			PvpTouches::Update(st.Engine, st.Bars);
		st.Showing	= true;
		st.Waiting	= false;
		st.Message	= st.Engine.Profiles.empty() ? MSG_WAITING : -1;
	}

	// ---- Translucent histogram boxes (spec D.5) ----

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

	// A translucent box in Left and Right placement is a Sierra Chart range per profile (the
	// Session VP's and TPO Profile's translucent boxes): bars show through it, and the study's
	// rows and lines are drawn over it. Only ranges that changed are sent; none in
	// ChartRightLatest, at opacity 0 or 100, while hidden or while nothing is shown (the callback
	// draws those).
	void UpdateBoxRanges(SCStudyInterfaceRef sc, StudyState& st)
	{
		ForgetRangesOnFullRecalculation(sc, st);
		const int opacity	= (std::max)(0, (std::min)(100, sc.Input[IN_BOX_OPACITY].GetInt()));
		const bool pinned	= (int)sc.Input[IN_PLACEMENT].GetIndex() == PL_CHART_RIGHT_LATEST;
		if (sc.HideStudy || !st.Showing || !st.Error.empty() || pinned || opacity <= 0 || opacity >= 100)
		{
			DeleteRanges(sc, st);
			return;
		}
		const std::vector<BoxPiece> desired	= BoxPieces(st.Engine.Profiles, st.Bars, st.TimeBars);
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

	// ---- Rendering helpers (the Session VP's) ----

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

	// ---- Drawing callback (spec D) ----

	// NinjaTrader's SimpleFont("Segoe UI", 11) (NT:236): 11 DIPs = 8.25 points, 8.
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
		int			Placement		= PL_LEFT;
		int			Mode			= VM_TOTAL;
		bool		ShowProfile		= true;
		bool		RowValues		= false;
		bool		HistoryNotice	= true;
		bool		Show[LV_COUNT]	= {true, true, true};		// POC, VAH, VAL
		bool		Extend[LV_COUNT] = {true, true, true};
		bool		UntilTouched	= true;
		bool		Labels			= false;
		int			Padding			= 12;
		int			RowGap			= 1;
		int			LineWidth		= 1;
		int			BoxOpacity		= 0;
		double		WidthPercent	= 60;
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
		d.Placement		= (std::min)((int)sc.Input[IN_PLACEMENT].GetIndex(), (int)PL_CHART_RIGHT_LATEST);
		d.Mode			= (std::min)((int)sc.Input[IN_VOLUME_MODE].GetIndex(), (int)VM_DELTA);
		d.ShowProfile	= sc.Input[IN_SHOW_PROFILE].GetYesNo() != 0;
		d.RowValues		= sc.Input[IN_ROW_VALUES].GetYesNo() != 0;
		d.HistoryNotice	= sc.Input[IN_HISTORY_NOTICE].GetYesNo() != 0;
		const int shows[LV_COUNT]	= {IN_SHOW_POC, IN_SHOW_VAH, IN_SHOW_VAL};
		const int extends[LV_COUNT]	= {IN_EXTEND_POC, IN_EXTEND_VAH, IN_EXTEND_VAL};
		for (int k = 0; k < LV_COUNT; k++)
		{
			d.Show[k]	= sc.Input[shows[k]].GetYesNo() != 0;
			d.Extend[k]	= sc.Input[extends[k]].GetYesNo() != 0;
		}
		d.UntilTouched	= (int)sc.Input[IN_EXTENSION].GetIndex() == EXT_UNTIL_TOUCHED;
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

	// A level line (NT:331-345, spec D.6, D.7): from lineLeft to `end`, LineWidth DIPs centered on
	// the price's pixel row; with `label` (the newest profile) its name and price above it, in
	// the line's color. Nothing when the price is off the scale.
	void DrawLevel(SCStudyInterfaceRef sc, const Canvas& c, TextPainter& text, double price, const char* name, double lineLeft, double right,
		double end, int lineWidth, uint32_t color, bool label)
	{
		const int y = PriceY(sc, price);
		if (y < c.Top || y > c.Bottom)
			return;
		if (end >= c.Left && lineLeft <= c.Right)
		{
			const int width = c.Stroke(lineWidth);
			FillRect(sc, (std::max)(c.Left, PixEdge(lineLeft)), y - width / 2, (std::min)(c.Right, PixEdge(end)), y - width / 2 + width, color);
		}
		if (label)
		{
			const double x = LevelLabelX(c.Left, c.Right, right, 4, [&c](double dips) { return c.Dip(dips); });
			text.Draw(sc, std::string(name) + " " + Price(sc, price), (int)RoundHalfUp(x), y - c.Dip(15), c.Dip(110), color);
		}
	}

	// One profile (NT:258-318): the box, the rows (first bar, second bar, row text), VAH, VAL,
	// POC. drawHistogram: the box and rows, off when the period ended before the first visible
	// bar (its extended lines still run).
	void DrawProfile(SCStudyInterfaceRef sc, const Canvas& c, const DisplaySettings& d, TextPainter& text, const StudyState& st,
		const PvpProfile& p, const PvpSnapshot& s, bool drawHistogram, bool newest)
	{
		const PvpBars& bars		= st.Bars;
		const bool pinned		= d.Placement == PL_CHART_RIGHT_LATEST;
		auto center				= [&sc](int i) { return BarX(sc, i); };
		const int periodLeft	= PositionX(PvpPosition(bars, p.StartChart, st.TimeBars), center);
		const int periodRight	= PositionX(PvpPosition(bars, p.LastChart, st.TimeBars), center);
		const ProfileLayout l	= LayoutProfile(d.Placement, periodLeft, periodRight, c.Left, c.Right, d.Padding, d.WidthPercent, c.Scale);

		if (drawHistogram)
		{
			// The box (NT:271-272): opaque, or translucent where no range draws it (ChartRightLatest,
			// or a period within one bar), blended with the chart background.
			int startBar = 0, endBar = 0;
			if (d.BoxOpacity > 0 && (d.BoxOpacity >= 100 || pinned || !BoxBars(p.StartChart, p.LastChart, bars, st.TimeBars, startBar, endBar)))
			{
				const int yTop = PriceY(sc, s.HighEdge), yBottom = PriceY(sc, s.LowEdge);
				const uint32_t color = d.BoxOpacity >= 100 ? d.Box : Blend(d.Box, d.BoxOpacity / 100.0, c.Background);
				FillRect(sc, PixEdge(l.BoxLeft), (std::min)(yTop, yBottom), PixEdge(l.BoxRight), (std::max)(yTop, yBottom), color);
			}
			if (d.ShowProfile)
			{
				const double tick = p.Cfg.Tick;
				for (size_t i = 0; i < s.Rows.size(); i++)
				{
					const PvpRow& row = s.Rows[i];
					if (!(row.Total() > 0))
						continue;
					// (H + 0.5) and ((H + 1) - 0.5) are the same double: neighbors share a boundary.
					const int yHigh		= PriceY(sc, ((double)row.HighTick + 0.5) * tick);
					const int yLow		= PriceY(sc, ((double)row.LowTick - 0.5) * tick);
					const RowBars bars2	= VolumeModes::Of(d.Mode, s, (int)i, (float)l.Width);
					const RowRect r		= LayoutRow(yHigh, yLow, c.Top, c.Bottom, l, bars2, d.RowGap, c.Scale);
					if (!r.Visible)
						continue;
					const uint32_t second	= bars2.InValueArea ? d.VaDown : d.Down;
					const uint32_t first	= bars2.FirstIsDown ? second : bars2.InValueArea ? d.VaUp : d.Up;
					const double split		= r.Left + (double)bars2.First;
					const int y0 = PixEdge(r.Y), y1 = PixEdge(r.Y + r.H);
					if (bars2.First > 0)
						FillRect(sc, PixEdge(r.Left), y0, PixEdge(split), y1, first);
					if (bars2.Second > 0)
						FillRect(sc, PixEdge(split), y0, PixEdge(split + (double)bars2.Second), y1, second);
					const double barsWidth = (double)bars2.First + (double)bars2.Second;
					if (d.RowValues && RowTextFits(r.Full, barsWidth, c.Scale))
						text.Draw(sc, PvpText::RowText(d.Mode, row), (int)RoundHalfUp(r.Left) + c.Dip(3), (int)RoundHalfUp(r.Y),
							(int)(barsWidth - 3 * c.Scale), d.Text);
				}
			}
		}

		// The lines (NT:316-318): VAH, VAL, then POC on top; the label on the newest profile.
		const bool labels = d.Labels && newest;
		auto end = [&](int level)
		{
			const int touch = p.Touch[level];
			return LevelEnd(l.Right, (double)c.Right, d.Extend[level], d.UntilTouched, touch >= 0, touch >= 0 ? (double)BarX(sc, touch) : 0.0);
		};
		if (d.Show[LV_VAH])
			DrawLevel(sc, c, text, s.Vah, "VAH", l.Left, l.Right, end(LV_VAH), d.LineWidth, d.VaLine, labels);
		if (d.Show[LV_VAL])
			DrawLevel(sc, c, text, s.Val, "VAL", l.Left, l.Right, end(LV_VAL), d.LineWidth, d.VaLine, labels);
		if (d.Show[LV_POC])
			DrawLevel(sc, c, text, s.Poc, "POC", l.Left, l.Right, end(LV_POC), d.LineWidth, d.PocLine, labels);
	}

	// Which profiles are drawn (NT:250-268, spec D.2), oldest first: those with rows that start
	// before the last visible bar ends; ChartRightLatest only the newest. Then the bottom notice
	// (NT:320-325), whether or not the newest profile is in view.
	void DrawProfiles(SCStudyInterfaceRef sc, const Canvas& c, const StudyState& st, TextPainter& text)
	{
		const DisplaySettings d	= ReadDisplay(sc);
		const PvpBars& bars		= st.Bars;
		const int n				= bars.Count();
		const int firstVisible	= (std::max)(0, (std::min)(n - 1, sc.IndexOfFirstVisibleBar));
		const int lastVisible	= (std::max)(0, (std::min)(n - 1, sc.IndexOfLastVisibleBar));
		const int64_t visibleFirst	= bars.E[(size_t)firstVisible];
		const int64_t visibleLast	= bars.E[(size_t)lastVisible];
		const std::deque<PvpProfile>& profiles = st.Engine.Profiles;
		const size_t count = profiles.size();
		const bool pinned = d.Placement == PL_CHART_RIGHT_LATEST;
		for (size_t k = 0; k < count; k++)
		{
			const PvpProfile& p		= profiles[k];
			const PvpSnapshot& s	= p.View();
			if (!s.HasRows() || !(s.MaxVolume > 0) || p.StartChart > visibleLast)
				continue;
			const bool newest = k == count - 1;
			if (pinned && !newest)
				continue;
			DrawProfile(sc, c, d, text, st, p, s, pinned || p.LastChart >= visibleFirst, newest);
		}
		const PvpProfile& newest = profiles.back();
		const char* notice = d.HistoryNotice && newest.First ? MESSAGES[MSG_FIRST_LOADED] : newest.View().WasCapped ? MESSAGES[MSG_CAPPED] : nullptr;
		if (notice != nullptr)
			text.Draw(sc, notice, c.Left + c.Dip(12), c.Bottom - c.Dip(23), (int)(std::max)(100 * c.Scale, c.Right - c.Left - 24 * c.Scale), d.Text);
	}

	// The text drawn instead of the profiles (spec C.8, D.8), or nullptr.
	const char* ViewMessage(const StudyState& st)
	{
		if (!st.Error.empty())
			return st.Error.c_str();
		if (!st.Showing || st.Engine.Profiles.empty() || st.Bars.Count() == 0)
			return MESSAGES[st.Message >= 0 && st.Message < MSG_COUNT ? st.Message : MSG_WAITING];
		return nullptr;
	}

	void DrawPeriodicVolumeProfile(HWND, HDC, SCStudyInterfaceRef sc)
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

		// A configuration error, no data or no profile: the message alone (NT:242-247), at 12, 35 DIPs.
		const char* message = ViewMessage(*state);
		if (message != nullptr)
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

SCSFExport scsf_TatankaPeriodicVolumeProfile(SCStudyInterfaceRef sc)
{
	if (sc.SetDefaults)
	{
		sc.GraphName		= "Tatanka Periodic Volume Profile";
		sc.GraphShortName	= "";
		sc.StudyDescription	= "Tatanka Periodic Volume Profile v1.0.0: daily, weekly, monthly or yearly volume profiles from 1-minute bars, "
							  "with POC, value area and extensions until touched. Defaults: 1 Week, Total, 68% value, 200 rows, 60% width, "
							  "Left. Uses the chart's own bars on a 1-minute chart, otherwise a hidden 1-minute chart of the same symbol. "
							  "Free and open source (MPL 2.0). tatankatrading.com";
		sc.GraphRegion		= 0;
		sc.AutoLoop			= 0;
		sc.ValueFormat		= VALUEFORMAT_INHERITED;
		sc.ScaleRangeType	= SCALE_SAMEASREGION;
		sc.DisplayStudyName	= 1;
		sc.DisplayStudyInputValues				= 0;	// the chart label carries NinjaTrader's chosen inputs
		sc.DrawStudyUnderneathMainPriceGraph	= 0;	// over the bars, as NinjaTrader draws
		sc.UpdateAlways		= 0;
		// Tick, volume and range bars end at their last trade (NinjaTrader's close stamp: the
		// touch test and x positions), from sc.BaseDataEndDateTime, kept only when set here.
		sc.MaintainAdditionalChartDataArrays	= 1;
		// Set at run time for the Volume at price option (spec C.7).
		sc.MaintainVolumeAtPriceData			= 0;

		// NinjaTrader's PriceBox plots (NT:81-83): a value label in the price scale, no line.
		const char* const names[3] = {"POC", "VAH", "VAL"};
		const uint32_t colors[3] = {RGB(152, 117, 205), RGB(223, 255, 0), RGB(223, 255, 0)};
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

		sc.Input[IN_PERIOD].Name = "Period";
		sc.Input[IN_PERIOD].SetCustomInputStrings("Daily;Weekly;Monthly;Yearly");
		sc.Input[IN_PERIOD].SetCustomInputIndex(PER_WEEKLY);
		sc.Input[IN_PERIOD].SetDescription("Periods follow the trading date from the chart's Session Times (a Sunday evening futures "
			"session belongs to Monday). Weeks start on Monday; daily, weekly and monthly groups restart on January 1.");

		sc.Input[IN_MULTIPLIER].Name = "Period multiplier";
		sc.Input[IN_MULTIPLIER].SetInt(1);
		sc.Input[IN_MULTIPLIER].SetIntLimits(1, 100);
		sc.Input[IN_MULTIPLIER].SetDescription("Monthly x 3 makes quarters. Yearly x 5 makes five-year profiles aligned to 2000.");

		sc.Input[IN_VOLUME_MODE].Name = "Volume";
		sc.Input[IN_VOLUME_MODE].SetCustomInputStrings("Total;UpDown;Delta");
		sc.Input[IN_VOLUME_MODE].SetCustomInputIndex(VM_TOTAL);

		sc.Input[IN_VA_PERCENT].Name = "Value area volume (%)";
		sc.Input[IN_VA_PERCENT].SetDouble(68);
		sc.Input[IN_VA_PERCENT].SetDoubleLimits(1, 100);

		sc.Input[IN_ROWS_LAYOUT].Name = "Rows layout";
		sc.Input[IN_ROWS_LAYOUT].SetCustomInputStrings("NumberOfRows;TicksPerRow");
		sc.Input[IN_ROWS_LAYOUT].SetCustomInputIndex(RL_NUMBER_OF_ROWS);

		sc.Input[IN_ROW_SIZE].Name = "Row size";
		sc.Input[IN_ROW_SIZE].SetInt(200);
		sc.Input[IN_ROW_SIZE].SetIntLimits(1, 5000);
		sc.Input[IN_ROW_SIZE].SetDescription("Target row count in NumberOfRows mode, or ticks per row in TicksPerRow mode.");

		sc.Input[IN_VA_METHOD].Name = "Value area method";
		sc.Input[IN_VA_METHOD].SetCustomInputStrings("TradingViewStyle;AtLeastTarget");
		sc.Input[IN_VA_METHOD].SetCustomInputIndex(VAM_TRADINGVIEW);
		sc.Input[IN_VA_METHOD].SetDescription("TradingViewStyle stops before the next row exceeds the target. AtLeastTarget includes that row.");

		sc.Input[IN_PROFILES].Name = "Profiles to retain";
		sc.Input[IN_PROFILES].SetInt(20);
		sc.Input[IN_PROFILES].SetIntLimits(1, 100);
		sc.Input[IN_PROFILES].SetDescription("Raising it doesn't load more history; raise Days to Load too.");

		sc.Input[IN_VOLUME_DATA].Name = "Volume data";
		sc.Input[IN_VOLUME_DATA].SetCustomInputStrings("1-minute bars (NinjaTrader);Volume at price (traded prices)");
		sc.Input[IN_VOLUME_DATA].SetCustomInputIndex(VD_MINUTES);
		sc.Input[IN_VOLUME_DATA].SetDescription("1-minute bars: each minute's volume spread evenly from its low to its high, up when it closes "
			"at or above its open (NinjaTrader). Volume at price: the volume where it traded, up/down from bid/ask (needs a chart reload "
			"when chosen).");

		sc.Input[IN_SHOW_PROFILE].Name = "Volume profile";
		sc.Input[IN_SHOW_PROFILE].SetYesNo(1);

		sc.Input[IN_ROW_VALUES].Name = "Values on rows";
		sc.Input[IN_ROW_VALUES].SetYesNo(0);
		sc.Input[IN_ROW_VALUES].SetDescription("Shown on rows at least 12 by 55 (1/96 inch).");

		sc.Input[IN_WIDTH].Name = "Width (% of period / chart)";
		sc.Input[IN_WIDTH].SetDouble(60);
		sc.Input[IN_WIDTH].SetDoubleLimits(1, 100);

		sc.Input[IN_PLACEMENT].Name = "Placement";
		sc.Input[IN_PLACEMENT].SetCustomInputStrings("Left;Right;ChartRightLatest");
		sc.Input[IN_PLACEMENT].SetCustomInputIndex(PL_LEFT);

		sc.Input[IN_PADDING].Name = "Chart-right padding (pixels)";
		sc.Input[IN_PADDING].SetInt(12);
		sc.Input[IN_PADDING].SetIntLimits(0, 500);
		sc.Input[IN_PADDING].SetDescription("ChartRightLatest only. In 1/96 inch: scaled on high-DPI displays.");

		sc.Input[IN_ROW_GAP].Name = "Row gap (pixels)";
		sc.Input[IN_ROW_GAP].SetInt(1);
		sc.Input[IN_ROW_GAP].SetIntLimits(0, 5);
		sc.Input[IN_ROW_GAP].SetDescription("At most 35 % of a row.");

		sc.Input[IN_HISTORY_NOTICE].Name = "Incomplete history notice";
		sc.Input[IN_HISTORY_NOTICE].SetYesNo(1);

		sc.Input[IN_SHOW_VAH].Name = "VAH";
		sc.Input[IN_SHOW_VAH].SetYesNo(1);
		sc.Input[IN_SHOW_VAL].Name = "VAL";
		sc.Input[IN_SHOW_VAL].SetYesNo(1);
		sc.Input[IN_SHOW_POC].Name = "POC";
		sc.Input[IN_SHOW_POC].SetYesNo(1);

		sc.Input[IN_EXTEND_POC].Name = "Extend POC right";
		sc.Input[IN_EXTEND_POC].SetYesNo(1);
		sc.Input[IN_EXTEND_VAH].Name = "Extend VAH right";
		sc.Input[IN_EXTEND_VAH].SetYesNo(1);
		sc.Input[IN_EXTEND_VAL].Name = "Extend VAL right";
		sc.Input[IN_EXTEND_VAL].SetYesNo(1);

		sc.Input[IN_EXTENSION].Name = "Extension behavior";
		sc.Input[IN_EXTENSION].SetCustomInputStrings("UntilTouched;ToChartEdge");
		sc.Input[IN_EXTENSION].SetCustomInputIndex(EXT_UNTIL_TOUCHED);
		sc.Input[IN_EXTENSION].SetDescription("UntilTouched stops each line at the first later bar of this chart whose range reaches it.");

		sc.Input[IN_LINE_WIDTH].Name = "Line width";
		sc.Input[IN_LINE_WIDTH].SetInt(1);
		sc.Input[IN_LINE_WIDTH].SetIntLimits(1, 5);

		sc.Input[IN_LEVEL_LABELS].Name = "Level name labels";
		sc.Input[IN_LEVEL_LABELS].SetYesNo(0);

		sc.Input[IN_INPUTS_IN_LABEL].Name = "Inputs in chart label";
		sc.Input[IN_INPUTS_IN_LABEL].SetYesNo(1);

		sc.Input[IN_VALUES_IN_LABEL].Name = "Values in chart label";
		sc.Input[IN_VALUES_IN_LABEL].SetYesNo(1);

		sc.Input[IN_UP_COLOR].Name = "Up / total volume";
		sc.Input[IN_UP_COLOR].SetColor(RGB(80, 85, 97));			// #505561
		sc.Input[IN_DOWN_COLOR].Name = "Down volume";
		sc.Input[IN_DOWN_COLOR].SetColor(RGB(64, 69, 81));			// #404551
		sc.Input[IN_VA_UP_COLOR].Name = "Value area up / total";
		sc.Input[IN_VA_UP_COLOR].SetColor(RGB(0, 181, 238));		// #00B5EE
		sc.Input[IN_VA_DOWN_COLOR].Name = "Value area down";
		sc.Input[IN_VA_DOWN_COLOR].SetColor(RGB(64, 32, 112));		// #402070
		sc.Input[IN_VA_LINE_COLOR].Name = "VAH / VAL";
		sc.Input[IN_VA_LINE_COLOR].SetColor(RGB(223, 255, 0));		// #DFFF00
		// NinjaTrader names this one "POC" too (NT:424); two inputs named POC would be ambiguous.
		sc.Input[IN_POC_LINE_COLOR].Name = "POC line";
		sc.Input[IN_POC_LINE_COLOR].SetColor(RGB(152, 117, 205));	// #9875CD
		sc.Input[IN_TEXT_COLOR].Name = "Text";
		sc.Input[IN_TEXT_COLOR].SetColor(RGB(211, 211, 211));		// LightGray
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
		// The study is removed (or the chart closed): its ranges and its heap state go with it.
		// The hidden 1-minute chart stays: other charts and studies of the symbol may read it
		// (Sierra Chart hands them the same chart), and it closes with the chartbook.
		if (StudyState* state = PeekState(sc))
			DeleteRanges(sc, *state);
		DeleteState(sc);
		return;
	}

	// Set on every call, after SetDefaults, so it survives a DLL reload.
	sc.p_GDIFunction = DrawPeriodicVolumeProfile;

	StudyState& state = GetState(sc);
	n_ACSIL::s_BarPeriod barPeriod;
	sc.GetBarPeriodParameters(barPeriod);
	const bool timeBars = barPeriod.IntradayChartBarPeriodType == IBPT_DAYS_MINS_SECS;
	state.Error = ConfigError(barPeriod.ChartDataType, barPeriod.IntradayChartBarPeriodType, sc.SecondsPerBar,
		sc.BaseDataEndDateTime.GetArraySize() >= sc.ArraySize, DecimalTickSize(sc.TickSize));
	// Logged once per error (NinjaTrader prints it once per load, NT:107): again only when it changes.
	int& logged = sc.GetPersistentInt(PI_ERROR_LOGGED);
	const int errorKey = state.Error.empty() ? 0 : (int)(Fnv1a(2166136261u, state.Error.data(), state.Error.size()) | 1u);
	if (errorKey != 0 && errorKey != logged)
		sc.AddMessageToLog((std::string(LOG_PREFIX) + state.Error).c_str(), 0);
	logged = errorKey;

	UpdateSubgraphs(sc);
	if (!state.Error.empty())
	{
		// Only the message is drawn (NT:242-247). Once the cause is gone the engine is rebuilt
		// from the first minute.
		const bool clear = sc.IsFullRecalculation || state.Built;
		state.ResetEngine();
		state.Bars		= PvpBars();
		state.Showing	= false;
		state.Waiting	= false;
		DeleteRanges(sc, state);
		WriteValues(sc, state, clear);
		sc.UpdateAlways = 0;
	}
	else
	{
		// Hidden (sc.HideStudy) still processes, so showing the study again draws at once;
		// UpdateBoxRanges then removes the ranges and the callback draws nothing.
		const int rebuilds = state.Rebuilds;
		ProcessCall(sc, state, timeBars);
		WriteValues(sc, state, sc.IsFullRecalculation || state.Rebuilds != rebuilds);
		UpdateBoxRanges(sc, state);
		// Sierra Chart calls again at the chart update interval while the minutes are not there
		// yet (the hidden chart loading or not found, volume at price not built: spec C.8).
		sc.UpdateAlways = state.Waiting ? 1 : 0;
	}
	UpdateLabel(sc, &state);
}

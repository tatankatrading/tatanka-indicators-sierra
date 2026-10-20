// Copyright (c) 2026 Tatanka Trading LLC.
// This Source Code Form is subject to the Mozilla Public License, v. 2.0.
// If a copy of the MPL was not distributed with this file, obtain one at https://mozilla.org/MPL/2.0/.
// Tatanka TPO Profile v1.0.0 for Sierra Chart - tatankatrading.com
// Sierra Chart port of the NinjaTrader 8 / Pine v6 "TPO Profile".
//
// TPO (Market Profile) letters for each block of a session, with the POC, the value area
// and an open-to-close color gradient. The engine below (sessions, letters, rows, profiles,
// POC, value area, daily ATR row height) is NinjaTrader's (TatankaTpoProfile.cs) with no
// Sierra Chart calls, so the tests can include this file. Where it differs on purpose, the
// comment says so (tpo_parity_spec.md section A).
//
// Sierra bars are stamped at their START, NinjaTrader's at their end, so a bar is classified
// by its end: its start plus the bar length (or where the data or the Session Times cut it),
// in the Timezone input's zone, daylight saving included.
//
// The live bar is recalculated on every tick: the engine state before the last bar is kept
// as a checkpoint, restored, and the bar processed again with its current prices, so the
// developing profile includes the bar being formed and nothing is counted twice.
//
// Drawing: Sierra Chart's drawing callback has no transparency, so translucent letter boxes
// (Box Transparency between 0 and 100) and the outline fills are study-owned translucent
// ranges (sc.AddLineUntilFutureIntersectionEx), one per vertical run of same-colored cells,
// sent only when they change. They sit under the callback, which draws the letters, the POC
// borders and lines, the value-area lines and the outline strokes, blended over the chart
// background. Opaque boxes (NinjaTrader's default 0) and Box Drawing = Solid are filled in the
// callback, and so are two translucent parts, blended with the chart background: an outline's
// untraded gaps over its own bars (exactly to the diagonal edge; none of the session's bars
// reach them), and boxes or outline parts before bar 0 or starting past the last bar (no range
// starts there). Grid lines and the lines of studies drawn under this one do not show through
// those two (they show through NinjaTrader's translucent fills; a README difference).

#include "sierrachart.h"

#include <algorithm>
#include <climits>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <functional>
#include <limits>
#include <map>
#include <string>
#include <vector>

SCDLLName("Tatanka TPO Profile")

namespace
{
	enum InputIndex
	{
		IN_FILTER,
		IN_SESSION_START,
		IN_SESSION_END,
		IN_TIME_ZONE,
		IN_BLOCK,
		IN_AUTO_ROWS,
		IN_TARGET_ROWS,
		IN_ROW_TICKS,
		IN_LETTER_DAYS,
		IN_SHOW_POLY,
		IN_POLY_DAYS,
		IN_BOX_TRANSPARENCY,
		IN_BOX_DRAWING,
		IN_START_COLOR,
		IN_END_COLOR,
		IN_TEXT_COLOR,
		IN_POC_COLOR,
		IN_POLY_COLOR,
		IN_X_OFFSET,
		IN_SHOW_LIVE,
		IN_SHOW_VA,
		IN_VA_COLOR,
		IN_EXTEND_POC
	};

	// The Timezone input, in its list order.
	enum TimeZoneOption { TZO_CHART, TZO_CHICAGO, TZO_NEW_YORK, TZO_UTC, TZO_LONDON };
	enum BoxDrawingOption { BD_TRANSPARENT, BD_SOLID };

	// Persistent variable keys
	const int PP_STATE			= 1;
	const int PI_DAILY_CHART	= 1;

	const int64_t DAY_MS		= 86400000;
	const int64_t NO_KEY		= INT64_MIN;
	const int ATR_PERIOD		= 10;	// NinjaTrader's ATR(BarsArray[1], 10)
	const int LETTER_COUNT		= 52;
	const int GRADIENT_BLOCKS	= 20;	// the End Color is reached at letter index 20 (U)

	// A session spanning more rows than this is a bad tick, not a market (ES at 1-tick rows:
	// 250,000 points). Such a bar adds no rows; NinjaTrader would try to draw them all.
	const int64_t MAX_SESSION_ROWS	= 1000000;
	const int MAX_MULTIPLIER		= 1000000000;

	const char* const MSG_NOT_INTRADAY = "Use an intraday chart. TPO sessions need intraday bars.";
	const char* const MSG_NO_END_TIMES = "Reload the chart (Chart >> Reload and Recalculate). Tick, volume and range bars need their end times.";

	// NinjaTrader's warning color (Goldenrod), for the configuration message.
	const uint32_t COLOR_GOLDENROD = RGB(218, 165, 32);

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

	// Half up: 2.5 -> 3, -2.5 -> -2, exact for |x| < 2^52 (floor(x + 0.5) would turn
	// 0.49999999999999994 into 1). For x >= 0 it is .NET's MidpointRounding.AwayFromZero
	// (NinjaTrader's PriceKey, auto multiplier and value-area target) and Pine's math.round.
	double RoundHalfUp(double x)
	{
		const double f = std::floor(x);
		return x - f >= 0.5 ? f + 1 : f;
	}

	// Half to even: .NET's default Math.Round (NinjaTrader's gradient and box alpha), written
	// out so it never depends on the floating-point environment. 76.5 -> 76, 77.5 -> 78.
	double RoundHalfEven(double x)
	{
		const double f = std::floor(x);
		const double d = x - f;
		if (d > 0.5)
			return f + 1;
		if (d < 0.5)
			return f;
		return std::fmod(f, 2.0) == 0 ? f : f + 1;
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

	// NinjaTrader's tick, 0.01 when the instrument has none (NT:261-263).
	double EffectiveTick(float tickSize)
	{
		const double tick = DecimalTickSize(tickSize);
		return tick > 0 ? tick : 0.01;
	}

	// Sierra stores prices as floats (GC 2650.1f is 2650.10009765625). Snapped to the tick
	// grid they match NinjaTrader's tick-rounded doubles: whole ticks divided by the ticks
	// per point when that is a whole number, so 75.43 is 7543 / 100, the double nearest 75.43.
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

	// Sierra Chart's "Include Columns With No Data" adds bars without trades: no volume, and
	// the previous close as all four prices (or zeros with "Do Not Draw Columns With No
	// Data"). NinjaTrader and TradingView never see such a bar, so it must not open, continue
	// or end a session. A bar with prices of its own always counts.
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
	// a time bar ends early: each session end that no session continues (the chart has no
	// data past it), and, with New Bar at Session Start, the trading day's start, where Sierra
	// Chart cuts the bar. INT64_MAX when there is none or the session times are unset.
	// NinjaTrader's bars end at its session boundaries too, and it stamps them there.
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

	// A time bar's end, NinjaTrader's close stamp (ms since Sierra's base date): its start
	// plus the bar length, or earlier where the next bar starts inside it (a bar cut by the
	// data) or where the Session Times cut it (cutSeconds from SessionCutAfter).
	int64_t TimeBarEnd(int64_t startMs, int secondsPerBar, bool hasNext, int64_t nextStartMs, int64_t cutSeconds)
	{
		int64_t end = startMs + (int64_t)secondsPerBar * 1000;
		if (hasNext && startMs < nextStartMs && nextStartMs < end)
			end = nextStartMs;
		if (cutSeconds != INT64_MAX && cutSeconds * 1000 < end)
			end = cutSeconds * 1000;
		return end;
	}

	// The custom session window (Filter by Time on), in ms since midnight of the Timezone
	// input's zone. A bar is in the window when its END is in (start, end], NinjaTrader's rule
	// on its close stamp (NT:181-185): with 0830-1500 the 1-minute bar starting 08:30 is the
	// first and the one starting 14:59 the last. A window may cross midnight; start == end is
	// a 24-hour window opening at the start (NinjaTrader never matches such a window, NT:183-184;
	// TradingView's 0000-0000 is a 24-hour session).
	struct SessionWindow
	{
		int64_t	StartMs	= 30600000;	// 08:30
		int64_t	EndMs	= 54000000;	// 15:00

		// key = the date of the window the bar ending at e belongs to (the date its window opens).
		bool Classify(int64_t e, int64_t& key) const
		{
			int64_t date	= FloorDiv(e, DAY_MS);
			int64_t clock	= e - date * DAY_MS;
			if (clock == 0)
			{
				// A bar ending at midnight belongs to the day before.
				date--;
				clock = DAY_MS;
			}
			if (StartMs < EndMs)
			{
				key = date;
				return StartMs < clock && clock <= EndMs;
			}
			if (StartMs > EndMs)
			{
				// The window crosses midnight: bars after midnight belong to the previous date's window.
				if (clock > StartMs)
				{
					key = date;
					return true;
				}
				if (clock <= EndMs)
				{
					key = date - 1;
					return true;
				}
				return false;
			}
			key = clock > StartMs ? date : date - 1;
			return true;
		}

		int64_t Open(int64_t key) const { return key * DAY_MS + StartMs; }
		int64_t End(int64_t key) const { return StartMs < EndMs ? key * DAY_MS + EndMs : (key + 1) * DAY_MS + EndMs; }

		// The bar ending exactly at the window's end completes the session (it is saved there,
		// not on the next bar; NinjaTrader waits for the next bar).
		bool Completes(int64_t e, int64_t key) const { return e == End(key); }
	};

	// The block (letter) of a bar ending at e in a session opening at open, both in ms of one
	// zone: NinjaTrader's -1 ms puts a bar ending exactly on a block boundary in the block it
	// ends (NT:246-257). Never negative.
	int LetterIndex(int64_t e, int64_t open, int blockMinutes)
	{
		const int64_t block = (int64_t)(std::max)(1, blockMinutes) * 60000;
		const int64_t index = FloorDiv(e - open - 1, block);
		return index < 0 ? 0 : index > INT_MAX ? INT_MAX : (int)index;
	}

	// NinjaTrader's letters (NT:27, NT:297-302): 52 of them, then "?".
	std::string LetterText(int index)
	{
		static const char letters[] = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";
		return index >= 0 && index < LETTER_COUNT ? std::string(1, letters[index]) : std::string("?");
	}

	// ---- Row height ----

	struct RowSizing
	{
		double	Tick		= 0.25;	// EffectiveTick
		bool	Auto		= true;
		int		TargetRows	= 80;
		int		ManualTicks	= 8;
	};

	// Ticks per row (NT:259-273): the manual height, or with Auto Row Height and a valid daily
	// ATR, ATR / target rows in ticks, rounded half up, at least 1. Evaluated left to right in
	// doubles like NinjaTrader's (atr / TargetRows / tick).
	int RowMultiplier(const RowSizing& s, double atr)
	{
		double mult = s.ManualTicks;
		if (s.Auto && atr > 0 && atr < std::numeric_limits<double>::infinity() && s.TargetRows > 0 && s.Tick > 0)
			mult = (std::max)(RoundHalfUp(atr / s.TargetRows / s.Tick), 1.0);
		mult = (std::max)(mult, 1.0);
		return (int)(std::min)(mult, (double)MAX_MULTIPLIER);
	}

	// The row height in price: a plain double product (GC 0.1 x 3 = 0.30000000000000004), as NinjaTrader's.
	double RowStep(const RowSizing& s, int mult)
	{
		return s.Tick * (double)(std::max)(1, mult);
	}

	// The row a price is in: the nearest multiple of the step, half up (NT:275-278 for positive
	// prices; a negative exact half goes up, TradingView's rule, where NinjaTrader goes away from
	// zero). False for a price that is not a number or out of range.
	bool RowKey(double price, double step, int64_t& key)
	{
		const double q = price / step;
		if (!(std::fabs(q) < 4.0e15))
			return false;
		key = (int64_t)RoundHalfUp(q);
		return true;
	}

	// NinjaTrader's daily ATR(10) (Wilder, @ATR.cs) over the bars of a daily chart.
	struct DailyAtrTable
	{
		std::vector<int>	Dates;	// trading dates of the daily bars, ascending
		std::vector<double>	Values;	// ATR at each daily bar

		bool Empty() const { return Dates.empty(); }

		// The first bar's range, then ((n - 1) x previous ATR + true range) / n with n = min(bars, 10).
		void Build(const std::vector<int>& dates, const std::vector<double>& high, const std::vector<double>& low,
			const std::vector<double>& close)
		{
			const size_t count = (std::min)((std::min)(dates.size(), high.size()), (std::min)(low.size(), close.size()));
			Dates.assign(dates.begin(), dates.begin() + (std::ptrdiff_t)count);
			Values.assign(count, 0.0);
			for (size_t i = 0; i < count; i++)
			{
				if (i == 0)
				{
					Values[0] = high[0] - low[0];
					continue;
				}
				const double previousClose	= close[i - 1];
				const double trueRange		= (std::max)(std::fabs(low[i] - previousClose), (std::max)(high[i] - low[i], std::fabs(high[i] - previousClose)));
				const int n					= (int)(std::min)(i + 1, (size_t)ATR_PERIOD);
				Values[i] = ((n - 1) * Values[i - 1] + trueRange) / n;
			}
		}

		// The ATR the sessions of a trading date use: that of the last daily bar dated before it
		// (the previous completed day, never the developing one), once that bar is the 11th or
		// later (NinjaTrader's CurrentBars[1] >= 10). NaN when there is none.
		double ForDate(int date) const
		{
			const std::ptrdiff_t index = (std::lower_bound(Dates.begin(), Dates.end(), date) - Dates.begin()) - 1;
			if (index < ATR_PERIOD)
				return std::numeric_limits<double>::quiet_NaN();
			const double value = Values[(size_t)index];
			return value > 0 && value < std::numeric_limits<double>::infinity() ? value : std::numeric_limits<double>::quiet_NaN();
		}
	};

	// ---- Profiles ----

	// The rows of the session in progress: a dense array of letter lists indexed by key - BaseKey.
	struct RowSet
	{
		int64_t							BaseKey	= 0;
		std::vector<std::vector<int>>	Rows;
		int								Present	= 0;	// rows with letters

		bool Empty() const { return Present == 0; }

		void Clear()
		{
			BaseKey = 0;
			Rows.clear();
			Present = 0;
		}

		const std::vector<int>* Find(int64_t key) const
		{
			if (key < BaseKey || key - BaseKey >= (int64_t)Rows.size())
				return nullptr;
			const std::vector<int>& row = Rows[(size_t)(key - BaseKey)];
			return row.empty() ? nullptr : &row;
		}

		// Adds the block's letter to rows lo..hi, once per row per block (NT:159-169; blocks
		// never decrease within a session). False, adding nothing, when the session would span
		// more than MAX_SESSION_ROWS rows.
		bool Add(int64_t lo, int64_t hi, int letter)
		{
			if (hi < lo)
				std::swap(lo, hi);
			const int64_t size		= (int64_t)Rows.size();
			const int64_t newLow	= size == 0 ? lo : (std::min)(lo, BaseKey);
			const int64_t newHigh	= size == 0 ? hi : (std::max)(hi, BaseKey + size - 1);
			if (newHigh - newLow + 1 > MAX_SESSION_ROWS || newHigh - newLow < 0)
				return false;
			if (size == 0)
			{
				BaseKey = newLow;
				Rows.resize((size_t)(newHigh - newLow + 1));
			}
			else
			{
				if (newLow < BaseKey)
				{
					Rows.insert(Rows.begin(), (size_t)(BaseKey - newLow), std::vector<int>());
					BaseKey = newLow;
				}
				if (newHigh - BaseKey + 1 > (int64_t)Rows.size())
					Rows.resize((size_t)(newHigh - BaseKey + 1));
			}
			for (int64_t k = lo; k <= hi; k++)
			{
				std::vector<int>& row = Rows[(size_t)(k - BaseKey)];
				if (row.empty())
					Present++;
				if (row.empty() || row.back() != letter)
					row.push_back(letter);
			}
			return true;
		}
	};

	// The POC (NT:347-362, PINE:127-143): the row with the most letters; on a tie the tied row
	// nearest the middle of the lowest..highest row, the lower one if equally close. In row
	// keys: the smallest |2k - (kMin + kMax)|, a strict "<" keeping the lower row. Exact, and
	// the same as both originals' price comparison (1e-9) for any row height above 1e-8.
	int PickPoc(const std::vector<int64_t>& keys, const std::vector<int>& counts, int maxCount)
	{
		if (keys.empty())
			return -1;
		const int64_t span = keys.front() + keys.back();
		int best = -1;
		int64_t bestDistance = INT64_MAX;
		for (size_t i = 0; i < keys.size(); i++)
		{
			if (counts[i] != maxCount)
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

	// The value area (NT:366-413, PINE:70-104): from the POC, one row at a time toward the
	// larger neighbor (down on a tie) until 70 % of the letters, target rounded half up from the
	// double product (45 letters -> 31, 85 -> 59). Neighbors are adjacent rows with letters, so
	// untraded rows are skipped. Row indices.
	void ValueArea(const std::vector<int>& counts, int poc, int& low, int& high)
	{
		low = high = poc;
		const int n = (int)counts.size();
		if (n == 0 || poc < 0 || poc >= n)
			return;
		long long total = 0;
		for (int c : counts)
			total += c;
		const long long target = (long long)RoundHalfUp((double)total * 0.70);
		long long cum = counts[(size_t)poc];
		while (cum < target && (low > 0 || high < n - 1))
		{
			const int nextLow	= low > 0 ? counts[(size_t)(low - 1)] : 0;
			const int nextHigh	= high < n - 1 ? counts[(size_t)(high + 1)] : 0;
			if (nextHigh > nextLow)
			{
				high++;
				cum += nextHigh;
			}
			else if (nextLow > 0)
			{
				low--;
				cum += nextLow;
			}
			else if (nextHigh > 0)
			{
				high++;
				cum += nextHigh;
			}
			else
				break;
		}
	}

	// A session's profile: its rows (ascending), letters, POC and value area.
	struct TpoProfile
	{
		int						Ordinal		= 0;	// index in the saved list (the live profile: the next one)
		int64_t					SessionKey	= 0;
		int						FirstBar	= -1;	// first in-session bar: the drawing anchor
		int						LastBar		= -1;	// last in-session bar
		int						AtrDate		= 0;	// the trading date whose ATR sized the rows
		int						Mult		= 1;	// ticks per row
		double					Step		= 0;	// row height in price, fixed for the session
		int64_t					IdBaseKey	= 0;	// range ids: the lowest key (live: fixed for the session)
		std::vector<int64_t>	Keys;				// rows with letters, ascending
		std::vector<int>		Counts;				// letters per row
		std::vector<int>		RowStart;			// row i's letters: Letters[RowStart[i] .. RowStart[i + 1])
		std::vector<int>		Letters;			// block indices, in time order per row
		int						MaxCount	= 0;
		int						Total		= 0;
		int						Poc			= -1;	// row index
		int						VaLow		= -1;	// row index of VAL
		int						VaHigh		= -1;	// row index of VAH
		uint32_t				Hash		= 0;	// everything its ranges depend on but IdBaseKey (ProfileHash)

		int RowCount() const { return (int)Keys.size(); }
		int Letter(int row, int j) const { return Letters[(size_t)(RowStart[(size_t)row] + j)]; }

		// Row centers (NinjaTrader's KeyToPrice, key x step).
		double Price(int row) const { return (double)Keys[(size_t)row] * Step; }
		double PocPrice() const { return Price(Poc); }
		double VahPrice() const { return Price(VaHigh); }
		double ValPrice() const { return Price(VaLow); }
	};

	// The profile's shape: ordinal, anchor, row height, rows and letters. The range cache keys
	// on it, so a session re-saved by the live bar with other prices gets new ranges.
	uint32_t ProfileHash(const TpoProfile& p)
	{
		uint32_t hash = 2166136261u;
		const int64_t head[] = {p.Ordinal, p.SessionKey, p.FirstBar, p.Mult, (int64_t)p.Keys.size(), p.Total};
		hash = Fnv1a(hash, head, sizeof(head));
		hash = Fnv1a(hash, &p.Step, sizeof(p.Step));
		if (!p.Keys.empty())
		{
			hash = Fnv1a(hash, p.Keys.data(), p.Keys.size() * sizeof(int64_t));
			hash = Fnv1a(hash, p.Counts.data(), p.Counts.size() * sizeof(int));
		}
		if (!p.Letters.empty())
			hash = Fnv1a(hash, p.Letters.data(), p.Letters.size() * sizeof(int));
		return hash;
	}

	TpoProfile BuildProfile(const RowSet& rows, int ordinal, int64_t sessionKey, int firstBar, int lastBar, int atrDate, int mult,
		double step)
	{
		TpoProfile p;
		p.Ordinal		= ordinal;
		p.SessionKey	= sessionKey;
		p.FirstBar		= firstBar;
		p.LastBar		= lastBar;
		p.AtrDate		= atrDate;
		p.Mult			= mult;
		p.Step			= step;
		p.Keys.reserve((size_t)rows.Present);
		p.Counts.reserve((size_t)rows.Present);
		p.RowStart.reserve((size_t)rows.Present + 1);
		for (size_t i = 0; i < rows.Rows.size(); i++)
		{
			const std::vector<int>& letters = rows.Rows[i];
			if (letters.empty())
				continue;
			p.Keys.push_back(rows.BaseKey + (int64_t)i);
			p.Counts.push_back((int)letters.size());
			p.RowStart.push_back((int)p.Letters.size());
			p.Letters.insert(p.Letters.end(), letters.begin(), letters.end());
			p.MaxCount = (std::max)(p.MaxCount, (int)letters.size());
		}
		p.RowStart.push_back((int)p.Letters.size());
		p.Total		= (int)p.Letters.size();
		p.IdBaseKey	= p.Keys.empty() ? 0 : p.Keys.front();
		p.Poc		= PickPoc(p.Keys, p.Counts, p.MaxCount);
		ValueArea(p.Counts, p.Poc, p.VaLow, p.VaHigh);
		p.Hash		= ProfileHash(p);
		return p;
	}

	// One bar as the engine sees it.
	struct TpoBar
	{
		int		Bar			= 0;
		bool	In			= false;	// in the session window (always, with the filter off)
		int64_t	Key			= NO_KEY;	// session identity: the window's date, or the trading date
		int		Letter		= 0;		// block index
		bool	Completes	= false;	// the bar ends exactly at the window's end
		int		AtrDate		= 0;		// trading date, for the daily ATR
		double	High		= 0;		// tick-snapped
		double	Low			= 0;
	};

	struct EngineConfig
	{
		bool			Filter			= true;
		SessionWindow	Window;
		int				Zone			= TZO_CHICAGO;
		int				BlockMinutes	= 30;
		RowSizing		Sizing;
	};

	// The engine's view of a bar. zoneEndMs: the bar's end in the Timezone input's zone;
	// chartEndMs: in the chart's zone; tradingDate/tradingOpenMs: Sierra Chart's trading day of
	// the bar and its start (chart zone), used with the filter off (NinjaTrader's trading-hours
	// template sessions, NT:125-129, NT:201-207), where a session ends only when the next starts.
	TpoBar MakeBar(int bar, const EngineConfig& c, int64_t zoneEndMs, int64_t chartEndMs, int tradingDate, int64_t tradingOpenMs,
		int atrDate, double high, double low)
	{
		TpoBar b;
		b.Bar		= bar;
		b.AtrDate	= atrDate;
		b.High		= high;
		b.Low		= low;
		if (c.Filter)
		{
			int64_t key = NO_KEY;
			b.In = c.Window.Classify(zoneEndMs, key);
			if (b.In)
			{
				b.Key		= key;
				b.Letter	= LetterIndex(zoneEndMs, c.Window.Open(key), c.BlockMinutes);
				b.Completes	= c.Window.Completes(zoneEndMs, key);
			}
		}
		else
		{
			b.In		= true;
			b.Key		= tradingDate;
			b.Letter	= LetterIndex(chartEndMs, tradingOpenMs, c.BlockMinutes);
		}
		return b;
	}

	// Everything one Update can change, saved before the (live) last bar.
	struct TpoCheckpoint
	{
		int		Bar				= -1;	// the bar this state precedes; -1 = none
		size_t	SavedCount		= 0;
		bool	HasLive			= false;
		bool	LiveInSession	= false;
		int64_t	LiveKey			= NO_KEY;
		int64_t	CompletedKey	= NO_KEY;
		int		FirstBar		= -1;
		int		LastBar			= -1;
		int		AtrDate			= 0;
		int		Mult			= 1;
		double	Step			= 0;
		int64_t	IdBaseKey		= 0;
		bool	HasIdBase		= false;
		RowSet	Live;
	};

	// NinjaTrader's OnBarUpdate (NT:101-172) on Sierra bars, oldest to newest.
	struct TpoEngine
	{
		RowSizing					Sizing;
		std::vector<TpoProfile>		Saved;			// completed sessions, oldest first; index = Ordinal (never trimmed, as NT)
		RowSet						Live;			// the session in progress
		bool						HasLive			= false;
		bool						LiveInSession	= false;	// the last bar was in the live session (Show Developing)
		int64_t						LiveKey			= NO_KEY;
		int64_t						CompletedKey	= NO_KEY;	// the session last saved by completion
		int							FirstBar		= -1;
		int							LastBar			= -1;
		int							AtrDate			= 0;
		int							Mult			= 1;
		double						Step			= 0;
		int64_t						IdBaseKey		= 0;
		bool						HasIdBase		= false;

		TpoEngine() = default;
		explicit TpoEngine(const RowSizing& sizing) : Sizing(sizing) {}

		void Update(const TpoBar& bar, const DailyAtrTable& atr)
		{
			// A bar of a session already completed cannot reopen it: it is treated as outside
			// the window. Only tick, volume or range bars can end exactly at the window's end
			// after the bar that completed it (end times at whole seconds); NinjaTrader's
			// millisecond stamps put such bars after the end, outside the window too.
			const bool in = bar.In && !(CompletedKey != NO_KEY && bar.Key == CompletedKey);

			// A bar outside the window or of another session ends the running one (NT:131-136).
			if (HasLive && (!in || bar.Key != LiveKey))
				SaveSession();

			if (in && !HasLive)
			{
				// NT:138-143. The row height is fixed for the session, from its first bar's
				// trading date (NinjaTrader re-prices a saved profile with the step of the bar
				// that saves it; TradingView draws every profile with the last bar's step).
				HasLive		= true;
				LiveKey		= bar.Key;
				FirstBar	= bar.Bar;
				AtrDate		= bar.AtrDate;
				Mult		= RowMultiplier(Sizing, atr.ForDate(bar.AtrDate));
				Step		= RowStep(Sizing, Mult);
				HasIdBase	= false;
				Live.Clear();
			}

			if (in)
			{
				int64_t lo = 0, hi = 0;
				if (RowKey(bar.Low, Step, lo) && RowKey(bar.High, Step, hi))
				{
					if (hi < lo)
						std::swap(lo, hi);
					if (Live.Add(lo, hi, bar.Letter) && !HasIdBase)
					{
						// Range ids of the live profile count from below its first bar, so they stay
						// put while the profile grows.
						IdBaseKey	= lo - 32768;
						HasIdBase	= true;
					}
				}
				LastBar = bar.Bar;
				if (bar.Completes)
				{
					// The session's last bar: save now, not on the next bar (NinjaTrader waits
					// for the next bar, so on RTH-only charts a finished day stays "live"
					// overnight and, with Show Developing off, invisible).
					SaveSession();
					CompletedKey = bar.Key;
				}
			}
			LiveInSession = HasLive && in;	// NT:145
		}

		// A bar the engine must not see (an empty column): nothing changes.
		void Skip(int) {}

		void SaveSession()
		{
			if (!Live.Empty())
				Saved.push_back(BuildProfile(Live, (int)Saved.size(), LiveKey, FirstBar, LastBar, AtrDate, Mult, Step));
			HasLive = false;
			Live.Clear();
		}

		bool HasLiveRows() const { return HasLive && !Live.Empty(); }

		// The developing profile, built on demand (O(rows)); its ordinal is the one it gets when saved.
		TpoProfile LiveProfile() const
		{
			TpoProfile p = BuildProfile(Live, (int)Saved.size(), LiveKey, FirstBar, LastBar, AtrDate, Mult, Step);
			p.IdBaseKey = HasIdBase ? IdBaseKey : p.IdBaseKey;
			return p;
		}

		// Whether every processed session (saved and live) still gets the row height it was
		// built with from this ATR table. When the daily chart arrives or changes, a session
		// whose height changed means one rebuild.
		bool StepsMatch(const DailyAtrTable& atr) const
		{
			for (const TpoProfile& p : Saved)
				if (RowMultiplier(Sizing, atr.ForDate(p.AtrDate)) != p.Mult)
					return false;
			return !HasLive || RowMultiplier(Sizing, atr.ForDate(AtrDate)) == Mult;
		}

		TpoCheckpoint Save(int bar) const
		{
			TpoCheckpoint cp;
			cp.Bar				= bar;
			cp.SavedCount		= Saved.size();
			cp.HasLive			= HasLive;
			cp.LiveInSession	= LiveInSession;
			cp.LiveKey			= LiveKey;
			cp.CompletedKey		= CompletedKey;
			cp.FirstBar			= FirstBar;
			cp.LastBar			= LastBar;
			cp.AtrDate			= AtrDate;
			cp.Mult				= Mult;
			cp.Step				= Step;
			cp.IdBaseKey		= IdBaseKey;
			cp.HasIdBase		= HasIdBase;
			cp.Live				= Live;
			return cp;
		}

		// Back to the state saved before checkpoint.Bar; a session the last bar saved is removed.
		void Restore(const TpoCheckpoint& cp)
		{
			if (Saved.size() > cp.SavedCount)
				Saved.erase(Saved.begin() + (std::ptrdiff_t)cp.SavedCount, Saved.end());
			HasLive			= cp.HasLive;
			LiveInSession	= cp.LiveInSession;
			LiveKey			= cp.LiveKey;
			CompletedKey	= cp.CompletedKey;
			FirstBar		= cp.FirstBar;
			LastBar			= cp.LastBar;
			AtrDate			= cp.AtrDate;
			Mult			= cp.Mult;
			Step			= cp.Step;
			IdBaseKey		= cp.IdBaseKey;
			HasIdBase		= cp.HasIdBase;
			Live			= cp.Live;
		}
	};

	// ---- Presentation (pure) ----

	// NinjaTrader's gradient (NT:530, NT:666-673): Start to End over 20 blocks, banker's
	// rounding per channel; letter index 20 (U) and later get the End color.
	uint32_t Gradient(uint32_t start, uint32_t end, int letterIndex)
	{
		const double f = (std::max)(0.0, (std::min)(1.0, letterIndex / (double)GRADIENT_BLOCKS));
		auto channel = [f](int a, int b) { return (int)RoundHalfEven(a + (b - a) * f); };
		return RGB(channel(GetRValue(start), GetRValue(end)), channel(GetGValue(start), GetGValue(end)),
			channel(GetBValue(start), GetBValue(end)));
	}

	// The gradient's 21 colors, letter index 0..20 (index 20 and later: the End color).
	struct GradientTable
	{
		uint32_t Colors[GRADIENT_BLOCKS + 1] = {};

		GradientTable(uint32_t start, uint32_t end)
		{
			for (int t = 0; t <= GRADIENT_BLOCKS; t++)
				Colors[t] = Gradient(start, end, t);
		}

		uint32_t operator[](int letterIndex) const { return Colors[(std::max)(0, (std::min)(GRADIENT_BLOCKS, letterIndex))]; }
	};

	// NinjaTrader's box alpha (NT:437): (100 - Box Transparency) x 2.55, banker's rounding, 0-255.
	int BoxAlpha(int transparency)
	{
		return (std::max)(0, (std::min)(255, (int)RoundHalfEven((100 - transparency) * 2.55)));
	}

	// NinjaTrader's fixed alphas (NT:496, NT:607-608): letters 230, outline fill 80 and outline
	// stroke 180 of 255. The POC border, POC line and value-area lines are opaque (NT:497-498).
	const int TEXT_ALPHA			= 230;
	const int OUTLINE_FILL_ALPHA	= 80;
	const int OUTLINE_STROKE_ALPHA	= 180;

	// The POC and value-area lines run this many columns past the widest row: 5 on letter
	// profiles (NT:548, NT:558), 3 on outlines (NT:620, NT:632).
	const int LETTER_LINE_EXTRA		= 5;
	const int OUTLINE_LINE_EXTRA	= 3;

	// The outline fill's opacity, 80/255, as a Sierra Chart TransparencyLevel: 69.
	int OutlineTransparency()
	{
		return (int)RoundHalfUp(100.0 - OUTLINE_FILL_ALPHA / 2.55);
	}

	// The outline stroke painted over its fill, as one opaque color over the chart background:
	// 1 - (1 - 180/255) x (1 - 80/255) = 0.798 (NinjaTrader strokes the filled polygon).
	double OutlineStrokeOpacity()
	{
		return 1.0 - (1.0 - OUTLINE_STROKE_ALPHA / 255.0) * (1.0 - OUTLINE_FILL_ALPHA / 255.0);
	}

	// What the display inputs ask for (the engine inputs are in EngineConfig).
	struct DisplaySettings
	{
		int			LetterDays		= 3;
		bool		ShowOutlines	= true;
		int			OutlineDays		= 15;
		int			Transparency	= 0;
		int			BoxDrawing		= BD_TRANSPARENT;
		uint32_t	StartColor		= RGB(0, 0, 255);
		uint32_t	EndColor		= RGB(255, 0, 255);
		uint32_t	TextColor		= RGB(255, 255, 255);
		uint32_t	PocColor		= RGB(255, 255, 0);
		uint32_t	PolyColor		= RGB(128, 128, 128);
		uint32_t	VaColor			= RGB(0, 128, 128);
		int			XOffset			= 0;
		bool		ShowLive		= false;
		bool		ShowValueArea	= false;
		bool		ExtendPoc		= false;

		// Letter boxes are translucent ranges in Transparent mode with a Box Transparency
		// strictly between 0 and 100; at 0 they are opaque and filled by the callback (exact,
		// and NinjaTrader's opaque boxes hide the bars too), at 100 they are not drawn.
		bool CellRanges() const { return BoxDrawing == BD_TRANSPARENT && Transparency > 0 && Transparency < 100; }
		bool OutlineRanges() const { return BoxDrawing == BD_TRANSPARENT; }
	};

	// Which saved profiles are drawn (NT:452-467): the newest LetterDays with letters, up to
	// OutlineDays before them as outlines, and the developing profile on top.
	struct ProfileSelection
	{
		int		OutlineFirst	= 0;	// outlines: Saved[OutlineFirst .. LetterFirst)
		int		LetterFirst		= 0;	// letter profiles: Saved[LetterFirst .. Total)
		int		Total			= 0;
		bool	Live			= false;
	};

	ProfileSelection SelectProfiles(int total, int letterDays, bool showOutlines, int outlineDays, bool live)
	{
		ProfileSelection s;
		s.Total			= (std::max)(0, total);
		s.LetterFirst	= (std::max)(s.Total - (std::max)(1, letterDays), 0);
		s.OutlineFirst	= showOutlines && s.LetterFirst > 0 ? (std::max)(s.LetterFirst - (std::max)(1, outlineDays), 0) : s.LetterFirst;
		s.Live			= live;
		return s;
	}

	// Extend POC (NT:476-483): the profile's POC line runs to the next saved session's last
	// in-session bar; the newest saved and the developing profile's to one bar past the latest
	// bar. A bar index, not shifted by X Offset (as NinjaTrader's).
	int PocExtensionBar(const std::vector<TpoProfile>& saved, int index, int arraySize)
	{
		return index + 1 < (int)saved.size() ? saved[(size_t)index + 1].LastBar : arraySize;
	}

	// The POC line's last bar: extra columns past the widest row, or the extension if longer.
	int PocEndBar(int anchor, int maxCount, int extra, bool extend, int extensionBar)
	{
		const int end = anchor + maxCount + extra;
		return extend ? (std::max)(end, extensionBar) : end;
	}

	// Row k's price edges, each computed once from (k +/- 0.5) x step so neighbors share them.
	double RowTop(int64_t key, double step) { return ((double)key + 0.5) * step; }
	double RowBottom(int64_t key, double step) { return ((double)key - 0.5) * step; }

	// ---- Translucent ranges (spec C.3) ----

	enum RangeKind { RK_LETTER = 0, RK_OUTLINE = 1 };

	// One study-owned translucent range: bars StartBar..EndBar (bar centers, check T1), prices
	// Bottom..Top. Keyed in Sierra Chart by (StartBarIndex, LineIDForBar).
	struct RangePiece
	{
		int			StartBar		= 0;
		int			EndBar			= 0;
		int			Id				= 0;
		double		Top				= 0;
		double		Bottom			= 0;
		uint32_t	Color			= 0;
		int			Transparency	= 0;	// Sierra Chart TransparencyLevel: 0 opaque .. 100 invisible
	};

	// LineIDForBar = 1 + rel + 65536 x (2 x (ordinal % 8192) + kind): rel is the piece's bottom
	// key above the profile's IdBaseKey, so ids are unique per start bar within a profile, and
	// profiles have their own ordinal. At most 1 + 65535 + 65536 x 16383 = 2^30.
	int RangeId(int ordinal, int kind, int64_t rel)
	{
		const int r = (int)(std::max)((int64_t)0, (std::min)((int64_t)65535, rel));
		return 1 + r + 65536 * (2 * ((std::max)(0, ordinal) % 8192) + kind);
	}

	uint64_t RangeKey(int startBar, int id)
	{
		return ((uint64_t)(uint32_t)startBar << 32) | (uint64_t)(uint32_t)id;
	}

	// What a sent range shows; it is sent again only when this changes.
	uint32_t RangeSignature(const RangePiece& r)
	{
		uint32_t hash = 2166136261u;
		const float prices[2] = {(float)r.Top, (float)r.Bottom};
		hash = Fnv1a(hash, &r.EndBar, sizeof(r.EndBar));
		hash = Fnv1a(hash, prices, sizeof(prices));
		hash = Fnv1a(hash, &r.Color, sizeof(r.Color));
		hash = Fnv1a(hash, &r.Transparency, sizeof(r.Transparency));
		return hash == 0 ? 1 : hash;
	}

	// Letter boxes: one range per vertical run, a maximal set of adjacent rows (no untraded row
	// between them) whose j-th letters have the same gradient color, in column j (bars A + j to
	// A + j + 1). Column 0 holds each row's first letter, so the runs are tall: a profile needs
	// some 40-150 ranges instead of 300-600 boxes. Pieces of one column have different bottom
	// keys, so their ids differ.
	std::vector<RangePiece> CellRuns(const TpoProfile& p, int anchor, uint32_t startColor, uint32_t endColor, int transparency)
	{
		std::vector<RangePiece> runs;
		if (p.MaxCount <= 0)
			return runs;
		const GradientTable colors(startColor, endColor);
		struct Open
		{
			bool		Active	= false;
			int64_t		Bottom	= 0;
			int64_t		Top		= 0;
			uint32_t	Color	= 0;
		};
		std::vector<Open> open((size_t)p.MaxCount);
		auto close = [&](int j)
		{
			Open& o = open[(size_t)j];
			if (!o.Active)
				return;
			RangePiece r;
			r.StartBar		= anchor + j;
			r.EndBar		= anchor + j + 1;
			r.Id			= RangeId(p.Ordinal, RK_LETTER, o.Bottom - p.IdBaseKey);
			r.Top			= RowTop(o.Top, p.Step);
			r.Bottom		= RowBottom(o.Bottom, p.Step);
			r.Color			= o.Color;
			r.Transparency	= transparency;
			runs.push_back(r);
			o.Active = false;
		};
		for (int i = 0; i < p.RowCount(); i++)
		{
			const int64_t key = p.Keys[(size_t)i];
			for (int j = 0; j < p.Counts[(size_t)i]; j++)
			{
				const uint32_t color = colors[p.Letter(i, j)];
				Open& o = open[(size_t)j];
				if (o.Active && o.Top == key - 1 && o.Color == color)
				{
					o.Top = key;
					continue;
				}
				close(j);
				o.Active	= true;
				o.Bottom	= key;
				o.Top		= key;
				o.Color		= color;
			}
		}
		for (int j = 0; j < p.MaxCount; j++)
			close(j);
		return runs;
	}

	// The outline's fill over its rows (NT:572-590): one range per run of adjacent rows with the
	// same count, bars A to A + count. The untraded gaps between rows, where the outline's right
	// edge runs diagonally, are in OutlinePieces.
	std::vector<RangePiece> OutlineRuns(const TpoProfile& p, int anchor, uint32_t color, int transparency)
	{
		std::vector<RangePiece> runs;
		const int n = p.RowCount();
		for (int i = 0; i < n;)
		{
			int last = i;
			while (last + 1 < n && p.Keys[(size_t)last + 1] == p.Keys[(size_t)last] + 1 && p.Counts[(size_t)last + 1] == p.Counts[(size_t)i])
				last++;
			RangePiece r;
			r.StartBar		= anchor;
			r.EndBar		= anchor + p.Counts[(size_t)i];
			r.Id			= RangeId(p.Ordinal, RK_OUTLINE, p.Keys[(size_t)i] - p.IdBaseKey);
			r.Top			= RowTop(p.Keys[(size_t)last], p.Step);
			r.Bottom		= RowBottom(p.Keys[(size_t)i], p.Step);
			r.Color			= color;
			r.Transparency	= transparency;
			runs.push_back(r);
			i = last + 1;
		}
		return runs;
	}

	// Whether the bars under the columns anchor .. anchor + columns (a column's right half is the
	// next bar's left half, so that bar counts too) are the session's own bars, or no bars at all
	// (before bar 0). No bar of the session reaches into an untraded row (a bar's rows are every
	// row from its low to its high), so a gap over its own bars covers none of the chart's bars,
	// and the drawing callback fills it exactly to the diagonal edge with an opaque blend over
	// the chart background. That blend hides the grid lines and the lines of studies drawn under
	// this one there, which NinjaTrader's translucent fill shows (a README difference: as ranges
	// the gap would show them, but its fill would follow the diagonal in half-column steps on
	// every gap, past the edge line).
	// At X Offset 0 this always holds: the two rows next to a gap are traded by different bars,
	// so neither has as many letters as the session has bars. X Offset can move a gap over other
	// sessions' bars, which must then show through its fill (OutlinePieces).
	bool OnlyOwnBarsUnder(const TpoProfile& p, int anchor, int columns)
	{
		const int last = anchor + columns;
		return last < 0 || ((std::max)(anchor, 0) >= p.FirstBar && last <= p.LastBar);
	}

	// The outline across the untraded gap between rows i and i + 1 as ranges (spec C.3 item 2):
	// the columns both rows reach, over the whole gap; then for each column between the two
	// counts, the part of the gap where the diagonal edge is right of the column's middle (a
	// staircase within half a column of the edge, which the callback strokes exactly). All of a
	// gap's pieces have its first untraded key as their id key, never a traded row's (so never
	// a row run's id), and they start on different bars. None when rows i, i + 1 are adjacent.
	std::vector<RangePiece> GapPieces(const TpoProfile& p, int i, int anchor, uint32_t color, int transparency)
	{
		std::vector<RangePiece> pieces;
		if (i < 0 || i + 1 >= p.RowCount() || p.Keys[(size_t)i + 1] == p.Keys[(size_t)i] + 1)
			return pieces;
		const int below		= p.Counts[(size_t)i];
		const int above		= p.Counts[(size_t)i + 1];
		const int narrow	= (std::min)(below, above);
		const int wide		= (std::max)(below, above);
		const double bottom	= RowTop(p.Keys[(size_t)i], p.Step);
		const double top	= RowBottom(p.Keys[(size_t)i + 1], p.Step);
		const int id		= RangeId(p.Ordinal, RK_OUTLINE, p.Keys[(size_t)i] + 1 - p.IdBaseKey);
		auto add = [&](int column, int columns, double low, double high)
		{
			RangePiece r;
			r.StartBar		= anchor + column;
			r.EndBar		= anchor + column + columns;
			r.Id			= id;
			r.Top			= high;
			r.Bottom		= low;
			r.Color			= color;
			r.Transparency	= transparency;
			pieces.push_back(r);
		};
		if (narrow > 0)
			add(0, narrow, bottom, top);
		for (int c = narrow; c < wide; c++)
		{
			// u: how far up the gap (0 = its bottom, 1 = its top) the edge crosses the column's middle.
			if (above > below)
				add(c, 1, bottom + (c + 0.5 - below) / (above - below) * (top - bottom), top);
			else
				add(c, 1, bottom, bottom + (below - c - 0.5) / (below - above) * (top - bottom));
		}
		return pieces;
	}

	// Every translucent piece of an outline: its row runs, and the gaps whose columns reach
	// bars of other sessions (X Offset). The other gaps cover none of the chart's bars, and the
	// callback fills them to the true diagonal (DrawOutlineFill), hiding grid lines and other
	// studies' lines there (OnlyOwnBarsUnder).
	std::vector<RangePiece> OutlinePieces(const TpoProfile& p, int anchor, uint32_t color, int transparency)
	{
		std::vector<RangePiece> pieces = OutlineRuns(p, anchor, color, transparency);
		for (int i = 0; i + 1 < p.RowCount(); i++)
		{
			if (p.Keys[(size_t)i + 1] == p.Keys[(size_t)i] + 1
				|| OnlyOwnBarsUnder(p, anchor, (std::max)(p.Counts[(size_t)i], p.Counts[(size_t)i + 1])))
				continue;
			const std::vector<RangePiece> gap = GapPieces(p, i, anchor, color, transparency);
			pieces.insert(pieces.end(), gap.begin(), gap.end());
		}
		return pieces;
	}

	// The outline's right edge across an untraded gap, at pixel row y: the diagonal from the
	// lower row's top right (lowRight, lowTop) to the upper row's bottom right (highRight,
	// highBottom), taken at the row's middle and rounded; the gap's fill on row y ends there.
	int GapEdgeX(int lowRight, int lowTop, int highRight, int highBottom, int y)
	{
		if (lowTop <= highBottom)
			return lowRight;
		const double t = (lowTop - (y + 0.5)) / (double)(lowTop - highBottom);
		return (int)std::floor(lowRight + t * (highRight - lowRight) + 0.5);
	}

	// T1: whether Sierra Chart draws a range that ends past the last loaded bar, in the chart's
	// right-side fill space (the developing profile's last column on a 30-minute chart). If a
	// tester finds it does not, set this to false: those parts go to the callback.
	const bool RANGES_IN_FILL_SPACE = true;

	// A piece's bars split between a range and the callback: no range starts before bar 0 or
	// at/after the last loaded bar + 1 (a range starts on a loaded bar). There are no bars
	// there, so the callback blends those parts over the chart background; grid lines and the
	// lines of studies drawn under this one do not show through them (a README difference).
	struct SpanSplit
	{
		bool	HasRange	= false;
		int		RangeStart	= 0;
		int		RangeEnd	= 0;
		int		Parts		= 0;		// callback parts
		int		Start[2]	= {0, 0};
		int		End[2]		= {0, 0};
	};

	SpanSplit SplitSpan(int start, int end, int arraySize)
	{
		SpanSplit s;
		auto callback = [&s](int a, int b)
		{
			if (b > a && s.Parts < 2)
			{
				s.Start[s.Parts]	= a;
				s.End[s.Parts]		= b;
				s.Parts++;
			}
		};
		if (end <= start)
			return s;
		callback(start, (std::min)(end, 0));
		const int first = (std::max)(start, 0);
		if (first >= end)
			return s;
		const int limit = RANGES_IN_FILL_SPACE ? end : (std::min)(end, arraySize - 1);
		if (first < arraySize && first < limit)
		{
			s.HasRange		= true;
			s.RangeStart	= first;
			s.RangeEnd		= limit;
			callback(limit, end);
		}
		else
			callback(first, end);
		return s;
	}

	// A profile's pieces before the split at the chart's ends: outline fills always (in
	// Transparent mode), letter boxes only when they are translucent ranges.
	std::vector<RangePiece> ProfilePieces(const TpoProfile& p, bool outline, const DisplaySettings& d)
	{
		const int anchor = p.FirstBar + d.XOffset;
		if (outline)
			return OutlinePieces(p, anchor, d.PolyColor, OutlineTransparency());
		if (d.CellRanges())
			return CellRuns(p, anchor, d.StartColor, d.EndColor, d.Transparency);
		return std::vector<RangePiece>();
	}

	// Pieces per profile, rebuilt only when the profile or a display input it depends on changes
	// (saved profiles never change; the developing one does, at most once per tick).
	struct PieceCacheEntry
	{
		uint32_t				Key		= 0;
		bool					Used	= false;
		std::vector<RangePiece>	Pieces;
	};
	using PieceCache = std::map<int, PieceCacheEntry>;

	uint32_t PieceKey(const TpoProfile& p, bool outline, const DisplaySettings& d)
	{
		// LastBar: which of an outline's gaps are ranges (OnlyOwnBarsUnder).
		const int64_t values[] = {outline ? 1 : 0, p.IdBaseKey, p.LastBar, d.XOffset, outline ? (int64_t)d.PolyColor : (int64_t)d.StartColor,
			outline ? 0 : (int64_t)d.EndColor, outline ? 0 : d.Transparency, d.CellRanges() ? 1 : 0};
		const uint32_t key = Fnv1a(p.Hash, values, sizeof(values));
		return key == 0 ? 1 : key;
	}

	// Every range the drawn profiles need, split at the chart's ends, sorted by (start, id).
	// Duplicate keys (possible only past 65,536 rows, where ids are clamped) keep the first.
	std::vector<RangePiece> DesiredRanges(const std::vector<TpoProfile>& saved, const TpoProfile* live, const DisplaySettings& d,
		int arraySize, PieceCache* cache)
	{
		std::vector<RangePiece> out;
		if (!d.OutlineRanges())
			return out;
		const ProfileSelection s = SelectProfiles((int)saved.size(), d.LetterDays, d.ShowOutlines, d.OutlineDays, live != nullptr);
		if (cache)
			for (auto& entry : *cache)
				entry.second.Used = false;
		auto add = [&](const TpoProfile& p, bool outline)
		{
			std::vector<RangePiece> local;
			const std::vector<RangePiece>* pieces = &local;
			if (cache)
			{
				PieceCacheEntry& entry = (*cache)[p.Ordinal * 2 + (outline ? 1 : 0)];
				const uint32_t key = PieceKey(p, outline, d);
				if (entry.Key != key)
				{
					entry.Pieces	= ProfilePieces(p, outline, d);
					entry.Key		= key;
				}
				entry.Used	= true;
				pieces		= &entry.Pieces;
			}
			else
				local = ProfilePieces(p, outline, d);
			for (const RangePiece& r : *pieces)
			{
				const SpanSplit split = SplitSpan(r.StartBar, r.EndBar, arraySize);
				if (!split.HasRange)
					continue;
				RangePiece q	= r;
				q.StartBar		= split.RangeStart;
				q.EndBar		= split.RangeEnd;
				out.push_back(q);
			}
		};
		for (int i = s.OutlineFirst; i < s.LetterFirst; i++)
			add(saved[(size_t)i], true);
		for (int i = s.LetterFirst; i < s.Total; i++)
			add(saved[(size_t)i], false);
		if (live)
			add(*live, false);
		if (cache)
			for (auto it = cache->begin(); it != cache->end();)
				it = it->second.Used ? std::next(it) : cache->erase(it);

		std::stable_sort(out.begin(), out.end(), [](const RangePiece& a, const RangePiece& b)
			{ return RangeKey(a.StartBar, a.Id) < RangeKey(b.StartBar, b.Id); });
		out.erase(std::unique(out.begin(), out.end(), [](const RangePiece& a, const RangePiece& b)
			{ return a.StartBar == b.StartBar && a.Id == b.Id; }), out.end());
		return out;
	}


	// Daily, weekly and monthly bars have no sessions to profile (Historical charts, and
	// intraday charts with day-long or longer bars). Tick, volume, range and other bars that
	// are not time-based are placed by their last trade (NinjaTrader's close stamp), Sierra
	// Chart's bar end times (hasEndTimes: sc.BaseDataEndDateTime is filled); without them the
	// study asks for a reload instead of placing those bars by their start times.
	const char* ConfigError(int chartDataType, int barPeriodType, int secondsPerBar, bool hasEndTimes)
	{
		if (chartDataType != INTRADAY_DATA || barPeriodType == IBPT_MONTHS_PER_BAR || barPeriodType == IBPT_HISTORICAL_DAILY_DATA_DAYS_PER_BAR
			|| (barPeriodType == IBPT_DAYS_MINS_SECS && !(secondsPerBar > 0 && secondsPerBar < SECONDS_PER_DAY)))
			return MSG_NOT_INTRADAY;
		if (barPeriodType != IBPT_DAYS_MINS_SECS && !hasEndTimes)
			return MSG_NO_END_TIMES;
		return "";
	}

	// ---- Sierra Chart glue ----

	struct StudyState
	{
		TpoEngine		Engine;
		TpoCheckpoint	Checkpoint;
		DailyAtrTable	Atr;
		uint32_t		AtrSignature	= 0;
		uint32_t		InputsKey		= 0;
		bool			Built			= false;
		int				Rebuilds		= 0;	// full engine rebuilds (diagnostics, tests)
		std::string		Error;					// configuration error for the drawing callback

		// The hidden daily chart (ReadDailyChart): resolved at least once, the symbol it was
		// requested for, and the symbol it held then.
		bool			DailyResolved	= false;
		std::string		DailyRequested;
		std::string		DailySymbol;

		// The developing profile as drawn (built once per study call for the callback and the ranges).
		bool			LiveShown		= false;
		TpoProfile		LiveProfile;

		// Translucent ranges sent to Sierra Chart: (start bar, id) -> signature. A full
		// recalculation deletes them (Sierra Chart removes a study's ranges then).
		std::map<uint64_t, uint32_t>	Sent;
		PieceCache						Pieces;
		uint32_t						RangesKey	= 0;	// what the sent ranges show; 0 = check them all
		int								RangeAdds	= 0;	// calls made (diagnostics, tests)
		int								RangeDeletes = 0;

		void ResetEngine()
		{
			Engine		= TpoEngine();
			Checkpoint	= TpoCheckpoint();
			InputsKey	= 0;
			Built		= false;
			LiveShown	= false;
			LiveProfile	= TpoProfile();
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

	TimeZonesEnum ZoneOf(int option)
	{
		switch (option)
		{
			case TZO_NEW_YORK:	return TIMEZONE_NEW_YORK;
			case TZO_UTC:		return TIMEZONE_UTC;
			case TZO_LONDON:	return TIMEZONE_LONDON;
			default:			return TIMEZONE_CHICAGO;
		}
	}

	EngineConfig ReadEngineConfig(SCStudyInterfaceRef sc)
	{
		EngineConfig c;
		c.Filter				= sc.Input[IN_FILTER].GetYesNo() != 0;
		c.Window.StartMs		= (int64_t)sc.Input[IN_SESSION_START].GetTime() * 1000;
		c.Window.EndMs			= (int64_t)sc.Input[IN_SESSION_END].GetTime() * 1000;
		c.Zone					= (std::min)((int)sc.Input[IN_TIME_ZONE].GetIndex(), (int)TZO_LONDON);
		c.BlockMinutes			= (std::max)(5, (std::min)(240, sc.Input[IN_BLOCK].GetInt()));
		c.Sizing.Tick			= EffectiveTick(sc.TickSize);
		c.Sizing.Auto			= sc.Input[IN_AUTO_ROWS].GetYesNo() != 0;
		c.Sizing.TargetRows		= (std::max)(15, (std::min)(100, sc.Input[IN_TARGET_ROWS].GetInt()));
		c.Sizing.ManualTicks	= (std::max)(1, (std::min)(100, sc.Input[IN_ROW_TICKS].GetInt()));
		return c;
	}

	std::string ChartSymbol(SCStudyInterfaceRef sc, int chartNumber)
	{
		const SCString symbol = sc.GetChartSymbol(chartNumber);
		return symbol.GetChars();
	}

	// The daily ATR from a hidden daily chart of the same symbol (If/Then's parameters, so
	// both studies share one chart), opened only while Auto Row Height is on. NinjaTrader's
	// daily series loads only over the chart's own range (a chart loading a few days gets
	// manual rows); TradingView uses the full daily history, as this does. Until the daily
	// chart has data the manual rows apply. True when the table changed.
	//
	// Sierra Chart hands every chart of the chartbook the same matching hidden chart (two ES
	// charts share one), so the study never changes it: a chart switched to another symbol gets
	// a daily chart of that symbol, found or opened (UpdatePriorChartNumberParametersToMatch = 0;
	// one hidden chart per symbol, the old one stays for the charts still reading it). Like
	// NinjaTrader's daily series, the ATR must be this chart's own symbol's, so the daily chart's
	// symbol is checked on every call as well: if it is no longer the one it held when it was
	// resolved (another study rewrote it, or it was closed), the chart is resolved again, and
	// until that one has data the manual rows apply.
	bool ReadDailyChart(SCStudyInterfaceRef sc, StudyState& state, bool autoRows, double tick)
	{
		DailyAtrTable table;
		uint32_t signature = 2166136261u;
		if (autoRows)
		{
			int& chartNumber = sc.GetPersistentInt(PI_DAILY_CHART);
			const std::string symbol = sc.GetRealTimeSymbol().GetChars();
			bool resolve = sc.IsFullRecalculation || chartNumber == 0 || !state.DailyResolved || symbol != state.DailyRequested;
			if (!resolve && ChartSymbol(sc, chartNumber) != state.DailySymbol)
				resolve = true;
			if (resolve)
			{
				s_ACSOpenChartParameters params;
				params.PriorChartNumber						= chartNumber;
				params.ChartDataType						= DAILY_DATA;
				params.Symbol								= symbol.c_str();
				params.HistoricalChartBarPeriod				= HISTORICAL_CHART_PERIOD_DAYS;
				params.HistoricalChartBarPeriodLengthInDays	= 1;
				params.DaysToLoad							= 3000;
				params.ContinuousFuturesContractOption		= sc.ContinuousFuturesContractOption;
				params.HideNewChart							= 1;
				params.UpdatePriorChartNumberParametersToMatch = 0;	// never rewrite a chart other charts read
				chartNumber = sc.OpenChartOrGetChartReference(params);
				state.DailyResolved		= true;
				state.DailyRequested	= symbol;
				state.DailySymbol		= chartNumber != 0 ? ChartSymbol(sc, chartNumber) : std::string();
			}
			if (chartNumber != 0)
			{
				SCGraphData daily;
				sc.GetChartBaseData(chartNumber, daily);
				SCDateTimeArray times;
				sc.GetChartDateTimeArray(chartNumber, times);
				const int count = (std::min)(daily[SC_LAST].GetArraySize(), times.GetArraySize());
				// Which chart and symbol: another chart's bars never pass for this one's.
				signature = Fnv1a(signature, &chartNumber, sizeof(chartNumber));
				signature = Fnv1a(signature, state.DailySymbol.data(), state.DailySymbol.size());
				signature = Fnv1a(signature, &count, sizeof(count));
				signature = Fnv1a(signature, &tick, sizeof(tick));
				// What can change while the chart is open: the last completed bar, and the date of
				// the developing one. The developing bar's prices change on every tick, but no
				// session uses its ATR (only bars dated before a session's trading date), so they
				// are left out; when the next day's bar arrives the count changes.
				for (int i = (std::max)(0, count - 2); i < count; i++)
				{
					const int date = times[i].GetDate();
					signature = Fnv1a(signature, &date, sizeof(date));
					if (i == count - 2)
					{
						const float bar[3] = {daily[SC_HIGH][i], daily[SC_LOW][i], daily[SC_LAST][i]};
						signature = Fnv1a(signature, bar, sizeof(bar));
					}
				}
				if (signature == state.AtrSignature)
					return false;
				std::vector<int> dates((size_t)count);
				std::vector<double> high((size_t)count), low((size_t)count), close((size_t)count);
				for (int i = 0; i < count; i++)
				{
					dates[(size_t)i]	= times[i].GetDate();
					high[(size_t)i]		= SnapToTick(daily[SC_HIGH][i], tick);
					low[(size_t)i]		= SnapToTick(daily[SC_LOW][i], tick);
					close[(size_t)i]	= SnapToTick(daily[SC_LAST][i], tick);
				}
				table.Build(dates, high, low, close);
			}
		}
		if (signature == state.AtrSignature)
			return false;
		state.Atr			= table;
		state.AtrSignature	= signature;
		return true;
	}

	// One chart bar for the engine (spec B.3): its end in the session's zone, its trading day,
	// tick-snapped high and low.
	TpoBar BarInput(SCStudyInterfaceRef sc, int index, const EngineConfig& c, const ChartSessions& sessions, bool timeBased, bool endTimes)
	{
		const SCDateTime start = sc.BaseDateTimeIn[index];
		const int64_t startMs = start.GetMillisecondsSinceBaseDate();
		int64_t endMs = startMs;
		if (timeBased)
		{
			const bool hasNext = index + 1 < sc.ArraySize;
			endMs = TimeBarEnd(startMs, sc.SecondsPerBar, hasNext, hasNext ? sc.BaseDateTimeIn[index + 1].GetMillisecondsSinceBaseDate() : 0,
				SessionCutAfter(FloorDiv(startMs, 1000), sessions));
		}
		else if (endTimes)
			endMs = sc.BaseDataEndDateTime[index].GetMillisecondsSinceBaseDate();  // the bar's last trade (NT's close stamp)

		int64_t zoneEndMs = endMs;
		int tradingDate = 0;
		int64_t tradingOpenMs = 0;
		if (c.Filter)
		{
			if (c.Zone != TZO_CHART)
				zoneEndMs = sc.ConvertDateTimeFromChartTimeZone(SCDateTime::MILLISECONDS(endMs), ZoneOf(c.Zone)).GetMillisecondsSinceBaseDate();
		}
		else
		{
			tradingDate		= sc.GetTradingDayDate(start);
			tradingOpenMs	= sc.GetTradingDayStartDateTimeOfBar(start).GetMillisecondsSinceBaseDate();
		}
		const int atrDate = c.Filter ? sc.GetTradingDayDate(start) : tradingDate;
		return MakeBar(index, c, zoneEndMs, endMs, tradingDate, tradingOpenMs, atrDate, SnapToTick(sc.High[index], c.Sizing.Tick),
			SnapToTick(sc.Low[index], c.Sizing.Tick));
	}

	// Runs the engine over the new bars (spec D.4). A full recalculation, a changed engine
	// input, a daily ATR change that alters a processed session's row height, or anything
	// unexpected rebuilds from bar 0; a tick restores the state before the last processed bar
	// and processes it again with its current prices.
	void ProcessBars(SCStudyInterfaceRef sc, StudyState& state, bool timeBased)
	{
		const EngineConfig c			= ReadEngineConfig(sc);
		const ChartSessions sessions	= SessionsOf(sc);
		const bool endTimes				= !timeBased && sc.BaseDataEndDateTime.GetArraySize() >= sc.ArraySize;

		uint32_t key = 2166136261u;
		const int64_t numbers[] = {c.Filter, c.Window.StartMs, c.Window.EndMs, c.Zone, c.BlockMinutes, c.Sizing.Auto, c.Sizing.TargetRows,
			c.Sizing.ManualTicks, timeBased, endTimes, sc.SecondsPerBar, sessions.DayStart, sessions.DayEnd, sessions.EveningStart,
			sessions.EveningEnd, sessions.UseEvening, sessions.NewBarAtSessionStart};
		key = Fnv1a(key, numbers, sizeof(numbers));
		key = Fnv1a(key, &c.Sizing.Tick, sizeof(c.Sizing.Tick));
		if (c.Zone == TZO_CHART)
		{
			const SCString zone = sc.GetChartTimeZone(sc.ChartNumber);
			key = Fnv1a(key, zone.GetChars(), (size_t)zone.GetLength());
		}

		const bool atrChanged = ReadDailyChart(sc, state, c.Sizing.Auto, c.Sizing.Tick);

		bool rebuild = sc.IsFullRecalculation || sc.UpdateStartIndex <= 0 || !state.Built || key != state.InputsKey
			|| (sc.UpdateStartIndex < sc.ArraySize && sc.UpdateStartIndex != state.Checkpoint.Bar)
			|| sc.ArraySize - 1 < state.Checkpoint.Bar;
		if (!rebuild && atrChanged && !state.Engine.StepsMatch(state.Atr))
			rebuild = true;

		int from;
		if (rebuild)
		{
			state.Engine		= TpoEngine(c.Sizing);
			state.Checkpoint	= TpoCheckpoint();
			state.InputsKey		= key;
			state.Built			= true;
			state.Rebuilds++;
			from				= 0;
		}
		else if (sc.UpdateStartIndex >= sc.ArraySize)
			from = sc.ArraySize;
		else
		{
			state.Engine.Restore(state.Checkpoint);
			from = state.Checkpoint.Bar;
		}

		for (int i = from; i < sc.ArraySize; i++)
		{
			if (i == sc.ArraySize - 1)
				state.Checkpoint = state.Engine.Save(i);
			if (IsEmptyColumn(sc.Volume[i], sc.NumberOfTrades[i], sc.Open[i], sc.High[i], sc.Low[i], sc.Close[i], i > 0,
				i > 0 ? sc.Close[i - 1] : 0.0f))
			{
				state.Engine.Skip(i);
				continue;
			}
			state.Engine.Update(BarInput(sc, i, c, sessions, timeBased, endTimes), state.Atr);
		}
	}

	DisplaySettings ReadDisplay(SCStudyInterfaceRef sc)
	{
		DisplaySettings d;
		d.LetterDays	= (std::max)(1, (std::min)(5, sc.Input[IN_LETTER_DAYS].GetInt()));
		d.ShowOutlines	= sc.Input[IN_SHOW_POLY].GetYesNo() != 0;
		d.OutlineDays	= (std::max)(1, (std::min)(50, sc.Input[IN_POLY_DAYS].GetInt()));
		d.Transparency	= (std::max)(0, (std::min)(100, sc.Input[IN_BOX_TRANSPARENCY].GetInt()));
		d.BoxDrawing	= (std::min)((int)sc.Input[IN_BOX_DRAWING].GetIndex(), (int)BD_SOLID);
		d.StartColor	= sc.Input[IN_START_COLOR].GetColor();
		d.EndColor		= sc.Input[IN_END_COLOR].GetColor();
		d.TextColor		= sc.Input[IN_TEXT_COLOR].GetColor();
		d.PocColor		= sc.Input[IN_POC_COLOR].GetColor();
		d.PolyColor		= sc.Input[IN_POLY_COLOR].GetColor();
		d.VaColor		= sc.Input[IN_VA_COLOR].GetColor();
		d.XOffset		= (std::max)(-10000, (std::min)(10000, sc.Input[IN_X_OFFSET].GetInt()));
		d.ShowLive		= sc.Input[IN_SHOW_LIVE].GetYesNo() != 0;
		d.ShowValueArea	= sc.Input[IN_SHOW_VA].GetYesNo() != 0;
		d.ExtendPoc		= sc.Input[IN_EXTEND_POC].GetYesNo() != 0;
		return d;
	}

	// On a full recalculation Sierra Chart has already deleted the study's ranges.
	void ForgetRangesOnFullRecalculation(SCStudyInterfaceRef sc, StudyState& state)
	{
		if (!sc.IsFullRecalculation)
			return;
		state.Sent.clear();
		state.RangesKey = 0;
	}

	void DeleteRanges(SCStudyInterfaceRef sc, StudyState& state)
	{
		ForgetRangesOnFullRecalculation(sc, state);
		for (const auto& entry : state.Sent)
		{
			sc.DeleteLineUntilFutureIntersection((int)(uint32_t)(entry.first >> 32), (int)(uint32_t)(entry.first & 0xFFFFFFFFu));
			state.RangeDeletes++;
		}
		state.Sent.clear();
		state.Pieces.clear();
		state.RangesKey = 0;
	}

	// The translucent letter boxes and outline fills (spec C.3) as study-owned ranges: the
	// drawing callback has no transparency, and the bars must show through. Only ranges that
	// changed are sent (re-adding the same start bar and id updates one in place), the ones no
	// longer wanted are deleted, and a call that changes nothing makes no calls at all.
	void UpdateRanges(SCStudyInterfaceRef sc, StudyState& state, const DisplaySettings& d)
	{
		ForgetRangesOnFullRecalculation(sc, state);
		if (sc.HideStudy || !state.Built || !state.Error.empty() || !d.OutlineRanges())
		{
			DeleteRanges(sc, state);
			return;
		}

		const std::vector<TpoProfile>& saved = state.Engine.Saved;
		const ProfileSelection s = SelectProfiles((int)saved.size(), d.LetterDays, d.ShowOutlines, d.OutlineDays, state.LiveShown);
		const int64_t settings[] = {d.LetterDays, d.ShowOutlines, d.OutlineDays, d.Transparency, d.BoxDrawing, d.StartColor, d.EndColor,
			d.PolyColor, d.XOffset, state.LiveShown, sc.ArraySize, (int64_t)saved.size()};
		uint32_t key = Fnv1a(2166136261u, settings, sizeof(settings));
		auto mix = [&key](const TpoProfile& p)
		{
			key = Fnv1a(key, &p.Hash, sizeof(p.Hash));
			key = Fnv1a(key, &p.IdBaseKey, sizeof(p.IdBaseKey));
			key = Fnv1a(key, &p.LastBar, sizeof(p.LastBar));
		};
		for (int i = s.OutlineFirst; i < s.Total; i++)
			mix(saved[(size_t)i]);
		if (s.Live)
			mix(state.LiveProfile);
		key = key == 0 ? 1 : key;
		if (key == state.RangesKey)
			return;

		const std::vector<RangePiece> desired = DesiredRanges(saved, s.Live ? &state.LiveProfile : nullptr, d, sc.ArraySize, &state.Pieces);
		auto wanted = [&desired](uint64_t rangeKey)
		{
			const auto found = std::lower_bound(desired.begin(), desired.end(), rangeKey,
				[](const RangePiece& r, uint64_t k) { return RangeKey(r.StartBar, r.Id) < k; });
			return found != desired.end() && RangeKey(found->StartBar, found->Id) == rangeKey;
		};
		for (auto it = state.Sent.begin(); it != state.Sent.end();)
		{
			if (wanted(it->first))
			{
				++it;
				continue;
			}
			sc.DeleteLineUntilFutureIntersection((int)(uint32_t)(it->first >> 32), (int)(uint32_t)(it->first & 0xFFFFFFFFu));
			state.RangeDeletes++;
			it = state.Sent.erase(it);
		}
		for (const RangePiece& r : desired)
		{
			const uint64_t rangeKey		= RangeKey(r.StartBar, r.Id);
			const uint32_t signature	= RangeSignature(r);
			uint32_t& sent = state.Sent[rangeKey];
			if (sent == signature)
				continue;
			n_ACSIL::s_LineUntilFutureIntersection line;
			line.StartBarIndex					= r.StartBar;
			line.EndBarIndex					= r.EndBar;	// > 0: the range stops there and never extends
			line.LineIDForBar					= r.Id;
			line.LineValue						= (float)r.Top;
			line.UseLineValue2					= 1;
			line.LineValue2ForRange				= (float)r.Bottom;
			line.LineColor						= r.Color;
			line.LineWidth						= 0;
			line.LineStyle						= 0;
			line.DrawValueLabel					= 0;
			line.DrawNameLabel					= 0;
			line.AlwaysExtendToEndOfChart		= 0;
			line.TransparencyLevel				= r.Transparency;
			line.PerformCloseCrossoverComparison = 0;
			sc.AddLineUntilFutureIntersectionEx(line);
			state.RangeAdds++;
			sent = signature;
		}
		state.RangesKey = key;
	}

	// ---- Rendering helpers (from TatankaGapAnalysis.cpp) ----

	// NinjaTrader draws these colors at partial opacity over the chart. The drawing
	// callback has no transparency, so blend them over what's underneath instead.
	uint32_t Blend(uint32_t color, double opacity, uint32_t background)
	{
		opacity = (std::max)(0.0, (std::min)(1.0, opacity));
		auto mix = [opacity](int c, int b) { return (int)(c * opacity + b * (1.0 - opacity) + 0.5); };
		return RGB(mix(GetRValue(color), GetRValue(background)),
			mix(GetGValue(color), GetGValue(background)),
			mix(GetBValue(color), GetBValue(background)));
	}

	enum LineStyleOption { LS_SOLID, LS_DASHED };

	// On/off run lengths in multiples of the line width, NinjaTrader's Direct2D Dash: 2 on, 2 off.
	// Drawn as filled rectangles, so styled lines keep their width (GDI pens draw wide dashes solid).
	const std::vector<int>& DashPattern(int style)
	{
		static const std::vector<int> solid;
		static const std::vector<int> dash = {2, 2};
		return style == LS_DASHED ? dash : solid;
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

	// The chart region in pixels, the visible bars, the DIP scale and the chart background.
	struct Canvas
	{
		int			Left		= 0;
		int			Top			= 0;
		int			Right		= 0;
		int			Bottom		= 0;
		int			FirstBar	= 0;
		int			LastBar		= 0;
		int			ArraySize	= 0;
		double		Scale		= 1;
		uint32_t	Background	= 0;

		int Dip(double dips) const { return (int)std::floor(dips * Scale + 0.5); }
		int Stroke(double dips) const { return (std::max)(1, Dip(dips)); }
	};

	// A line from x0 to x1 covering rows top..bottom - 1, dashed in multiples of width, the
	// pattern starting at x0. Only the part inside the region is drawn (dashes keep their
	// phase), so a long line from far off-screen costs nothing.
	void DrawHorizontalLine(SCStudyInterfaceRef sc, const Canvas& c, int x0, int x1, int top, int bottom, int width, int style, uint32_t color)
	{
		width = (std::max)(1, width);
		if (x1 <= x0 || bottom <= c.Top || top >= c.Bottom || x1 <= c.Left || x0 >= c.Right)
			return;
		const std::vector<int>& pattern = DashPattern(style);
		if (pattern.empty())
		{
			FillRect(sc, (std::max)(x0, c.Left - 1), top, (std::min)(x1, c.Right + 1), bottom, color);
			return;
		}
		int period = 0;
		for (int run : pattern)
			period += run * width;
		int x = x0;
		if (x < c.Left - period)
			x += (int)(((int64_t)c.Left - x) / period - 1) * period;
		const int end = (std::min)(x1, c.Right + period);
		for (size_t run = 0; x < end; run = (run + 1) % pattern.size())
		{
			const int length = pattern[run] * width;
			if (run % 2 == 0)
				FillRect(sc, x, top, (std::min)(x + length, x1), bottom, color);
			x += length;
		}
	}

	// NinjaTrader lays everything out in DIPs (1/96 inch), so its paddings and line widths
	// grow on a scaled display. This is that scale: the window's DPI, or, when the window
	// reports 96 on a scaled display, how much wider the selected font drew a long line than
	// GetTextSizeWithFont measured it (whole-pixel widths of many characters round far less
	// than one text height). The DPI is trusted whenever it is above 96, so the scale never
	// depends on the font size. Call after SetTextFont(font).
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

	// ---- Drawing callback ----

	// NinjaTrader's letters: Arial 10 DIPs (NT:444) = 7.5 points, rounded half up to 8.
	n_ACSIL::s_GraphicsFont LetterFont()
	{
		n_ACSIL::s_GraphicsFont font;
		font.m_FaceName	= "Arial";
		font.m_Height	= 8;
		font.m_Weight	= FW_NORMAL;
		return font;
	}

	// The configuration message font (Gap Analysis's).
	n_ACSIL::s_GraphicsFont MessageFont()
	{
		n_ACSIL::s_GraphicsFont font;
		font.m_FaceName	= "Segoe UI";
		font.m_Height	= 10;
		font.m_Weight	= FW_NORMAL;
		return font;
	}

	// Letter sizes in the letter font, measured once per frame and letter; the text color is
	// set only when it changes.
	struct LetterPainter
	{
		n_ACSIL::s_GraphicsFont	Font;
		SCString				Text[LETTER_COUNT + 1];
		n_ACSIL::s_GraphicsSize	Size[LETTER_COUNT + 1];
		bool					Measured[LETTER_COUNT + 1] = {};
		uint32_t				TextColor		= 0;
		bool					HasTextColor	= false;

		void Draw(SCStudyInterfaceRef sc, int letterIndex, int x1, int yTop, int x2, int yBottom, uint32_t color)
		{
			const int slot = letterIndex >= 0 && letterIndex < LETTER_COUNT ? letterIndex : LETTER_COUNT;
			if (!Measured[slot])
			{
				const std::string text = LetterText(letterIndex);
				Text[slot]		= text.c_str();
				Size[slot]		= MeasureLine(sc, Font, text);
				Measured[slot]	= true;
			}
			if (!HasTextColor || TextColor != color)
			{
				sc.Graphics.SetTextColor(GraphicsColor(color));
				TextColor		= color;
				HasTextColor	= true;
			}
			// Centered in the box, not clipped to it (NinjaTrader's layout box, NT:542-543).
			sc.Graphics.DrawTextAt(Text[slot], x1 + (x2 - x1 - Size[slot].Width) / 2, yTop + (yBottom - yTop - Size[slot].Height) / 2);
		}
	};

	// Whether a profile's bars anchor..endBar meet the visible bars (one bar of margin). The last
	// visible bar is never past the last loaded bar, so when the view reaches it, anything to its
	// right can be in view (the right-side fill space): the clipping region trims it.
	bool MeetsView(const Canvas& c, int anchor, int endBar)
	{
		const bool fillSpace = c.LastBar >= c.ArraySize - 1;
		return endBar >= c.FirstBar - 1 && (fillSpace || anchor <= c.LastBar + 1);
	}

	// NinjaTrader's 1.2-DIP POC border (NT:536) is centered on the box edges: each side covers
	// [edge - width / 2, edge - width / 2 + width), so two POC boxes side by side share one
	// separator (a 1-pixel border is the box's left and top pixel rows and the neighbors' first
	// ones on the right and bottom, as Direct2D snaps a 1-pixel line on a pixel edge).
	void DrawBoxBorder(SCStudyInterfaceRef sc, int x1, int yTop, int x2, int yBottom, int width, uint32_t color)
	{
		const int shift = width / 2;
		const int left = x1 - shift, top = yTop - shift, right = x2 - shift + width, bottom = yBottom - shift + width;
		FillRect(sc, left, top, right, top + width, color);
		FillRect(sc, left, bottom - width, right, bottom, color);
		FillRect(sc, left, top + width, left + width, bottom - width, color);
		FillRect(sc, right - width, top + width, right, bottom - width, color);
	}

	// A horizontal profile line at a price: width rows centered on its pixel row.
	void DrawPriceLine(SCStudyInterfaceRef sc, const Canvas& c, int x0, int x1, double price, int width, int style, uint32_t color)
	{
		const int y = PriceY(sc, price);
		DrawHorizontalLine(sc, c, x0, x1, y - width / 2, y - width / 2 + width, width, style, color);
	}

	// A letter profile (saved or developing, NT:485-563): per row bottom to top, per box left to
	// right: the box fill (unless a translucent range draws it) and the POC border on the POC
	// row; then the letters; then the 2-DIP POC line and the dashed value-area lines.
	// NinjaTrader draws each box's letter right after its fill, so the next box's fill cuts off
	// any letter wider or taller than its box (most letters in 6-7 DIP columns); here every
	// letter is drawn whole, over the boxes.
	void DrawLetterProfile(SCStudyInterfaceRef sc, const Canvas& c, const DisplaySettings& d, const TpoProfile& p, int extensionBar,
		LetterPainter& letters)
	{
		if (p.RowCount() == 0 || p.MaxCount <= 0)
			return;
		const int anchor	= p.FirstBar + d.XOffset;
		const int lineEnd	= anchor + p.MaxCount + LETTER_LINE_EXTRA;
		const int pocEnd	= PocEndBar(anchor, p.MaxCount, LETTER_LINE_EXTRA, d.ExtendPoc, extensionBar);
		if (!MeetsView(c, anchor, (std::max)(lineEnd, pocEnd)))
			return;

		std::vector<int> columns((size_t)p.MaxCount + 1);
		for (int j = 0; j <= p.MaxCount; j++)
			columns[(size_t)j] = BarX(sc, anchor + j);
		const GradientTable gradient(d.StartColor, d.EndColor);
		const double alpha		= BoxAlpha(d.Transparency) / 255.0;
		const bool visibleBox	= d.Transparency < 100;
		const bool cellRanges	= d.CellRanges();
		const int border		= c.Stroke(1.2);
		const double minWidth	= 6 * c.Scale;	// NinjaTrader shows letters in boxes of 6 x 7 DIPs or more (NT:539)
		const double minHeight	= 7 * c.Scale;
		const int margin		= c.Dip(24);	// letters overflow small boxes

		struct LetterJob
		{
			int			Letter	= 0;
			int			X1		= 0;
			int			Top		= 0;
			int			X2		= 0;
			int			Bottom	= 0;
			uint32_t	Color	= 0;
		};
		std::vector<LetterJob> jobs;
		for (int i = 0; i < p.RowCount(); i++)
		{
			const int64_t key	= p.Keys[(size_t)i];
			const int yTop		= PriceY(sc, RowTop(key, p.Step));
			const int yBottom	= PriceY(sc, RowBottom(key, p.Step));
			if (yBottom <= yTop || yBottom < c.Top - margin || yTop > c.Bottom + margin)
				continue;
			const bool pocRow		= i == p.Poc;
			const bool showLetters	= yBottom - yTop >= minHeight;
			for (int j = 0; j < p.Counts[(size_t)i]; j++)
			{
				const int x1 = columns[(size_t)j], x2 = columns[(size_t)j + 1];
				if (x2 <= x1 || x2 < c.Left - margin || x1 > c.Right + margin)
					continue;
				const int letter	= p.Letter(i, j);
				const uint32_t box	= visibleBox ? Blend(gradient[letter], alpha, c.Background) : c.Background;
				// Opaque boxes, Solid, and translucent boxes no range can draw (before bar 0 or
				// from the last bar + 1 on, SplitSpan: grid lines do not show through those).
				if (visibleBox && !(cellRanges && SplitSpan(anchor + j, anchor + j + 1, c.ArraySize).HasRange))
					FillRect(sc, x1, yTop, x2, yBottom, box);
				if (pocRow)
					DrawBoxBorder(sc, x1, yTop, x2, yBottom, border, d.PocColor);
				if (showLetters && x2 - x1 >= minWidth)
					jobs.push_back({letter, x1, yTop, x2, yBottom, Blend(d.TextColor, TEXT_ALPHA / 255.0, box)});
			}
		}
		for (const LetterJob& job : jobs)
			letters.Draw(sc, job.Letter, job.X1, job.Top, job.X2, job.Bottom, job.Color);

		const int left = columns[0];
		if (p.Poc >= 0)
			DrawPriceLine(sc, c, left, BarX(sc, pocEnd), p.PocPrice(), c.Stroke(2), LS_SOLID, d.PocColor);
		if (d.ShowValueArea && p.VaHigh >= 0 && p.VaLow >= 0)
		{
			const int right = BarX(sc, lineEnd);
			DrawPriceLine(sc, c, left, right, p.VahPrice(), c.Stroke(1), LS_DASHED, d.VaColor);
			DrawPriceLine(sc, c, left, right, p.ValPrice(), c.Stroke(1), LS_DASHED, d.VaColor);
		}
	}

	// An older day's outline in pixels (NT:572-590): the left edge, each row's right edge, top
	// and bottom, and the bars where the POC and value-area lines end. Visible: it meets the
	// visible bars.
	struct OutlineFrame
	{
		struct Row
		{
			int Right	= 0;
			int Top		= 0;
			int Bottom	= 0;
		};
		const TpoProfile*	Profile	= nullptr;
		bool				Visible	= false;
		int					Anchor	= 0;
		int					LineEnd	= 0;
		int					PocEnd	= 0;
		int					Left	= 0;
		std::vector<Row>	Rows;
	};

	OutlineFrame MakeOutlineFrame(SCStudyInterfaceRef sc, const Canvas& c, const DisplaySettings& d, const TpoProfile& p, int extensionBar)
	{
		OutlineFrame f;
		f.Profile = &p;
		const int n = p.RowCount();
		if (n == 0 || p.MaxCount <= 0)
			return f;
		f.Anchor	= p.FirstBar + d.XOffset;
		f.LineEnd	= f.Anchor + p.MaxCount + OUTLINE_LINE_EXTRA;
		f.PocEnd	= PocEndBar(f.Anchor, p.MaxCount, OUTLINE_LINE_EXTRA, d.ExtendPoc, extensionBar);
		if (!MeetsView(c, f.Anchor, (std::max)(f.LineEnd, f.PocEnd)))
			return f;
		f.Visible	= true;
		f.Left		= BarX(sc, f.Anchor);
		f.Rows.resize((size_t)n);
		for (int i = 0; i < n; i++)
		{
			f.Rows[(size_t)i].Right		= BarX(sc, f.Anchor + p.Counts[(size_t)i]);
			f.Rows[(size_t)i].Top		= PriceY(sc, RowTop(p.Keys[(size_t)i], p.Step));
			f.Rows[(size_t)i].Bottom	= PriceY(sc, RowBottom(p.Keys[(size_t)i], p.Step));
		}
		return f;
	}

	// An outline's fill (NT:607, 80/255 of the Polyline Fill Color). In Solid mode all of it is
	// here, blended with the chart background. In Transparent mode the translucent ranges
	// (OutlinePieces) cover what lies on the loaded bars, so the bars show through, and this
	// fills only what no chart bar is under: pieces before bar 0 or past the last bar, and the
	// untraded gaps over the session's own bars (OnlyOwnBarsUnder), exactly to the diagonal.
	// It is the same color the ranges give over the bare background, but opaque: grid lines and
	// the lines of studies drawn under this one do not show through these parts (README).
	void DrawOutlineFill(SCStudyInterfaceRef sc, const Canvas& c, const DisplaySettings& d, const OutlineFrame& f)
	{
		if (!f.Visible)
			return;
		const TpoProfile& p		= *f.Profile;
		const int n				= p.RowCount();
		const bool solid		= d.BoxDrawing == BD_SOLID;
		const uint32_t fill		= Blend(d.PolyColor, OUTLINE_FILL_ALPHA / 255.0, c.Background);
		const int transparency	= OutlineTransparency();
		// Whether pieces reaching this column can lie off the loaded bars (SplitSpan's callback parts).
		auto offChart = [&](int columns) { return f.Anchor < 0 || f.Anchor + columns >= c.ArraySize - 1; };
		auto fillPiece = [&](const RangePiece& r)
		{
			const int top = PriceY(sc, r.Top), bottom = PriceY(sc, r.Bottom);
			if (solid)
			{
				FillRect(sc, BarX(sc, r.StartBar), top, BarX(sc, r.EndBar), bottom, fill);
				return;
			}
			const SpanSplit split = SplitSpan(r.StartBar, r.EndBar, c.ArraySize);
			for (int k = 0; k < split.Parts; k++)
				FillRect(sc, BarX(sc, split.Start[k]), top, BarX(sc, split.End[k]), bottom, fill);
		};

		if (solid || offChart(p.MaxCount))
			for (const RangePiece& r : OutlineRuns(p, f.Anchor, d.PolyColor, transparency))
				fillPiece(r);

		for (int i = 0; i + 1 < n; i++)
		{
			if (p.Keys[(size_t)i + 1] == p.Keys[(size_t)i] + 1)
				continue;
			const int wide = (std::max)(p.Counts[(size_t)i], p.Counts[(size_t)i + 1]);
			if (solid || OnlyOwnBarsUnder(p, f.Anchor, wide))
			{
				// One pixel row at a time from the left edge to the diagonal: none of the chart's
				// bars are under it, so the blend matches the ranges' look, except that it hides
				// grid lines and other studies' lines crossing the gap (OnlyOwnBarsUnder).
				const OutlineFrame::Row& below = f.Rows[(size_t)i];
				const OutlineFrame::Row& above = f.Rows[(size_t)i + 1];
				const int first = (std::max)(above.Bottom, c.Top), last = (std::min)(below.Top, c.Bottom);
				for (int y = first; y < last; y++)
					FillRect(sc, f.Left, y, GapEdgeX(below.Right, below.Top, above.Right, above.Bottom, y), y + 1, fill);
			}
			else if (offChart(wide))
				for (const RangePiece& r : GapPieces(p, i, f.Anchor, d.PolyColor, transparency))
					fillPiece(r);
		}
	}

	// An outline's stroke, drawn inside the polygon's edge as one opaque color (NinjaTrader's
	// 180-alpha stroke over its 80-alpha fill), the dashed POC and the value-area lines
	// (NT:608-635). A one-row day is its rectangle (NinjaTrader and TradingView skip it).
	void DrawOutlineEdges(SCStudyInterfaceRef sc, const Canvas& c, const DisplaySettings& d, const OutlineFrame& f)
	{
		if (!f.Visible)
			return;
		const TpoProfile& p		= *f.Profile;
		const int n				= p.RowCount();
		const uint32_t stroke	= Blend(d.PolyColor, OutlineStrokeOpacity(), c.Background);
		const std::vector<OutlineFrame::Row>& rows = f.Rows;
		const int left			= f.Left;

		// The stroke, w pixels inside the edge: the left edge, the lowest row's bottom, the
		// highest row's top, each row's right edge, the steps between adjacent rows (with the
		// corner square), and diagonals across untraded gaps.
		const int w = c.Stroke(1);
		const OutlineFrame::Row& lowest = rows.front();
		const OutlineFrame::Row& highest = rows.back();
		FillRect(sc, left, highest.Top, left + w, lowest.Bottom, stroke);
		FillRect(sc, left, lowest.Bottom - w, lowest.Right, lowest.Bottom, stroke);
		FillRect(sc, left, highest.Top, highest.Right, highest.Top + w, stroke);
		for (const OutlineFrame::Row& row : rows)
			FillRect(sc, row.Right - w, row.Top, row.Right, row.Bottom, stroke);
		bool penSet = false;
		for (int i = 0; i + 1 < n; i++)
		{
			const OutlineFrame::Row& below = rows[(size_t)i];
			const OutlineFrame::Row& above = rows[(size_t)i + 1];
			if (p.Keys[(size_t)i + 1] == p.Keys[(size_t)i] + 1)
			{
				if (above.Right > below.Right)
					FillRect(sc, below.Right - w, below.Top - w, above.Right, below.Top, stroke);
				else if (above.Right < below.Right)
					FillRect(sc, above.Right - w, below.Top, below.Right, below.Top + w, stroke);
				continue;
			}
			if (above.Right == below.Right)
			{
				FillRect(sc, below.Right - w, above.Bottom, below.Right, below.Top, stroke);
				continue;
			}
			if (!penSet)
			{
				n_ACSIL::s_GraphicsPen pen;
				pen.m_PenStyle	= n_ACSIL::s_GraphicsPen::e_PenStyle::PEN_STYLE_SOLID;
				pen.m_PenColor	= GraphicsColor(stroke);
				pen.m_Width		= w;
				sc.Graphics.SetPen(pen);
				penSet = true;
			}
			const int inset = 1 + (w - 1) / 2;
			sc.Graphics.MoveTo(below.Right - inset, below.Top);
			sc.Graphics.LineTo(above.Right - inset, above.Bottom - 1);
		}
		if (penSet)
			sc.Graphics.ResetPen();

		// The 1-DIP dashed POC and value-area lines (NT:627-635).
		if (p.Poc >= 0)
			DrawPriceLine(sc, c, left, BarX(sc, f.PocEnd), p.PocPrice(), w, LS_DASHED, d.PocColor);
		if (d.ShowValueArea && p.VaHigh >= 0 && p.VaLow >= 0)
		{
			const int right = BarX(sc, f.LineEnd);
			DrawPriceLine(sc, c, left, right, p.VahPrice(), w, LS_DASHED, d.VaColor);
			DrawPriceLine(sc, c, left, right, p.ValPrice(), w, LS_DASHED, d.VaColor);
		}
	}

	// A configuration error replaces everything: the study name and the message in Goldenrod.
	void DrawMessage(SCStudyInterfaceRef sc, const Canvas& c, const n_ACSIL::s_GraphicsFont& font, const std::string& message)
	{
		const TextMeasure measure = [&sc, &font](const std::string& text) { return MeasureLine(sc, font, text).Width; };
		const int maxWidth = (std::max)(1, c.Right - c.Left - c.Dip(24));
		std::vector<std::string> lines = WrapWords("Tatanka TPO Profile", maxWidth, measure);
		for (const std::string& line : WrapWords(message, maxWidth, measure))
			lines.push_back(line);
		const int lineHeight = LineHeight(sc, font);
		sc.Graphics.SetTextColor(GraphicsColor(COLOR_GOLDENROD));
		for (size_t i = 0; i < lines.size(); i++)
			if (!lines[i].empty())
				sc.Graphics.DrawTextAt(SCString(lines[i].c_str()), c.Left + c.Dip(12), c.Top + c.Dip(20) + (int)i * lineHeight);
	}

	// NinjaTrader's order (NT:452-467): outlines oldest first, letter profiles oldest first,
	// then the developing profile. The outlines' fills come first, then their strokes and
	// lines: NinjaTrader's translucent fill of a newer outline leaves an older day's extended
	// POC line visible through it, which an opaque fill drawn over the line would erase (the
	// fill's ranges are under every line anyway).
	void DrawProfiles(SCStudyInterfaceRef sc, const Canvas& c, const StudyState& state, LetterPainter& letters)
	{
		const DisplaySettings d	= ReadDisplay(sc);
		const TpoEngine& e		= state.Engine;
		const ProfileSelection s = SelectProfiles((int)e.Saved.size(), d.LetterDays, d.ShowOutlines, d.OutlineDays, state.LiveShown);
		std::vector<OutlineFrame> outlines;
		for (int i = s.OutlineFirst; i < s.LetterFirst; i++)
			outlines.push_back(MakeOutlineFrame(sc, c, d, e.Saved[(size_t)i], PocExtensionBar(e.Saved, i, c.ArraySize)));
		for (const OutlineFrame& f : outlines)
			DrawOutlineFill(sc, c, d, f);
		for (const OutlineFrame& f : outlines)
			DrawOutlineEdges(sc, c, d, f);
		for (int i = s.LetterFirst; i < s.Total; i++)
			DrawLetterProfile(sc, c, d, e.Saved[(size_t)i], PocExtensionBar(e.Saved, i, c.ArraySize), letters);
		if (s.Live)
			DrawLetterProfile(sc, c, d, state.LiveProfile, PocExtensionBar(e.Saved, s.Total, c.ArraySize), letters);
	}

	void DrawTpoProfile(HWND, HDC, SCStudyInterfaceRef sc)
	{
		const StudyState* state = PeekState(sc);
		if (sc.HideStudy || state == nullptr)
			return;

		Canvas c;
		c.Left		= sc.StudyRegionLeftCoordinate;
		c.Top		= sc.StudyRegionTopCoordinate;
		c.Right		= sc.StudyRegionRightCoordinate;
		c.Bottom	= sc.StudyRegionBottomCoordinate;
		c.FirstBar	= sc.IndexOfFirstVisibleBar;
		c.LastBar	= sc.IndexOfLastVisibleBar;
		c.ArraySize	= sc.ArraySize;
		if (c.Right <= c.Left || c.Bottom <= c.Top)
			return;

		LetterPainter letters;
		letters.Font = LetterFont();
		sc.Graphics.SetTextFont(letters.Font);  // before any measuring: see MeasureLine
		c.Scale = DipScale(sc, letters.Font);
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

		if (!state->Error.empty())
		{
			const n_ACSIL::s_GraphicsFont font = MessageFont();
			sc.Graphics.SetTextFont(font);
			DrawMessage(sc, c, font, state->Error);
		}
		else if (state->Built)
			DrawProfiles(sc, c, *state, letters);

		sc.Graphics.ResetTextAlign();
		sc.Graphics.ResetBackgroundMode();
		sc.Graphics.ResetTextColor();
		sc.Graphics.ResetClippingRegion();
		sc.Graphics.ResetTextFont();
	}
}

SCSFExport scsf_TatankaTpoProfile(SCStudyInterfaceRef sc)
{
	if (sc.SetDefaults)
	{
		sc.GraphName		= "Tatanka TPO Profile";
		sc.StudyDescription	= "Tatanka TPO Profile v1.0.0: TPO (Market Profile) letters for each block of the session with the POC, "
							  "value area and an open-to-close gradient. Letter detail for recent sessions, outlines for older ones. "
							  "Free and open source (MPL 2.0). tatankatrading.com";
		sc.GraphRegion		= 0;
		sc.AutoLoop			= 0;
		sc.ValueFormat		= VALUEFORMAT_INHERITED;
		sc.ScaleRangeType	= SCALE_SAMEASREGION;
		sc.UpdateAlways		= 0;
		sc.DisplayStudyInputValues				= 0;
		sc.DrawStudyUnderneathMainPriceGraph	= 0;  // over the bars, as both originals draw
		// Tick, volume and range bars end at their last trade (NinjaTrader's close stamp), from
		// sc.BaseDataEndDateTime, which Sierra Chart keeps only when this is set here.
		sc.MaintainAdditionalChartDataArrays	= 1;

		sc.Input[IN_FILTER].Name = "Filter by Time? (RTH Only)";
		sc.Input[IN_FILTER].SetYesNo(1);
		sc.Input[IN_FILTER].SetDescription("Off: one profile per trading day (Chart Settings session times).");

		sc.Input[IN_SESSION_START].Name = "Session Start Time";
		sc.Input[IN_SESSION_START].SetTime(30600);
		sc.Input[IN_SESSION_START].SetDescription("In the Timezone below. NinjaTrader's Session Time 0830-1500 = 08:30 to 15:00.");

		sc.Input[IN_SESSION_END].Name = "Session End Time";
		sc.Input[IN_SESSION_END].SetTime(54000);
		sc.Input[IN_SESSION_END].SetDescription("Equal to the start = a 24-hour session from the start time.");

		sc.Input[IN_TIME_ZONE].Name = "Timezone";
		sc.Input[IN_TIME_ZONE].SetCustomInputStrings("Chart Time Zone;America/Chicago;America/New_York;UTC;Europe/London");
		sc.Input[IN_TIME_ZONE].SetCustomInputIndex(TZO_CHICAGO);
		sc.Input[IN_TIME_ZONE].SetDescription("The session times' time zone (daylight saving included). Chart Time Zone = NinjaTrader's behavior.");

		sc.Input[IN_BLOCK].Name = "Block Size (Minutes)";
		sc.Input[IN_BLOCK].SetInt(30);
		sc.Input[IN_BLOCK].SetIntLimits(5, 240);
		sc.Input[IN_BLOCK].SetDescription("One letter per block.");

		sc.Input[IN_AUTO_ROWS].Name = "Auto Row Height";
		sc.Input[IN_AUTO_ROWS].SetYesNo(1);
		sc.Input[IN_AUTO_ROWS].SetDescription("Sizes rows from the daily ATR(10) of a hidden daily chart of the same symbol.");

		sc.Input[IN_TARGET_ROWS].Name = "Target Rows Per Day (Auto)";
		sc.Input[IN_TARGET_ROWS].SetInt(80);
		sc.Input[IN_TARGET_ROWS].SetIntLimits(15, 100);
		sc.Input[IN_TARGET_ROWS].SetDescription("Rows per daily ATR (a full trading day); an RTH session usually has fewer.");

		sc.Input[IN_ROW_TICKS].Name = "Row Height (Ticks, Manual)";
		sc.Input[IN_ROW_TICKS].SetInt(8);
		sc.Input[IN_ROW_TICKS].SetIntLimits(1, 100);
		sc.Input[IN_ROW_TICKS].SetDescription("Used when Auto Row Height is off, or until the daily chart has 11 days.");

		sc.Input[IN_LETTER_DAYS].Name = "Days with Letter Detail";
		sc.Input[IN_LETTER_DAYS].SetInt(3);
		sc.Input[IN_LETTER_DAYS].SetIntLimits(1, 5);

		sc.Input[IN_SHOW_POLY].Name = "Show Polyline Outlines (Older Days)";
		sc.Input[IN_SHOW_POLY].SetYesNo(1);

		sc.Input[IN_POLY_DAYS].Name = "Max Polyline Days";
		sc.Input[IN_POLY_DAYS].SetInt(15);
		sc.Input[IN_POLY_DAYS].SetIntLimits(1, 50);

		sc.Input[IN_BOX_TRANSPARENCY].Name = "Box Transparency (0-100)";
		sc.Input[IN_BOX_TRANSPARENCY].SetInt(0);
		sc.Input[IN_BOX_TRANSPARENCY].SetIntLimits(0, 100);
		sc.Input[IN_BOX_TRANSPARENCY].SetDescription("0 = opaque (NinjaTrader's default), 75 = TradingView's default.");

		sc.Input[IN_BOX_DRAWING].Name = "Box Drawing";
		sc.Input[IN_BOX_DRAWING].SetCustomInputStrings("Transparent (bars show through);Solid (fastest)");
		sc.Input[IN_BOX_DRAWING].SetCustomInputIndex(BD_TRANSPARENT);
		sc.Input[IN_BOX_DRAWING].SetDescription("Solid blends boxes and outline fills with the chart background: faster, but bars under a "
			"profile are hidden unless Draw Study Underneath Main Price Graph is on.");

		sc.Input[IN_START_COLOR].Name = "Start Color (Open)";
		sc.Input[IN_START_COLOR].SetColor(RGB(0, 0, 255));		// NinjaTrader's Blue

		sc.Input[IN_END_COLOR].Name = "End Color (Close)";
		sc.Input[IN_END_COLOR].SetColor(RGB(255, 0, 255));		// Fuchsia

		sc.Input[IN_TEXT_COLOR].Name = "Text Color";
		sc.Input[IN_TEXT_COLOR].SetColor(RGB(255, 255, 255));	// White

		sc.Input[IN_POC_COLOR].Name = "POC Color";
		sc.Input[IN_POC_COLOR].SetColor(RGB(255, 255, 0));		// Yellow

		sc.Input[IN_POLY_COLOR].Name = "Polyline Fill Color";
		sc.Input[IN_POLY_COLOR].SetColor(RGB(128, 128, 128));	// Gray

		sc.Input[IN_X_OFFSET].Name = "X Offset (Bars)";
		sc.Input[IN_X_OFFSET].SetInt(0);
		sc.Input[IN_X_OFFSET].SetIntLimits(-10000, 10000);
		sc.Input[IN_X_OFFSET].SetDescription("Positive = shift right, negative = shift left.");

		sc.Input[IN_SHOW_LIVE].Name = "Show Developing (Current Day)";
		sc.Input[IN_SHOW_LIVE].SetYesNo(0);

		sc.Input[IN_SHOW_VA].Name = "Show Value Area (VAH/VAL)";
		sc.Input[IN_SHOW_VA].SetYesNo(0);

		sc.Input[IN_VA_COLOR].Name = "Value Area Color";
		sc.Input[IN_VA_COLOR].SetColor(RGB(0, 128, 128));		// Teal

		sc.Input[IN_EXTEND_POC].Name = "Extend POC Through Next RTH Session";
		sc.Input[IN_EXTEND_POC].SetYesNo(0);

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
	sc.p_GDIFunction = DrawTpoProfile;

	StudyState& state = GetState(sc);

	n_ACSIL::s_BarPeriod barPeriod;
	sc.GetBarPeriodParameters(barPeriod);
	const bool timeBased = barPeriod.IntradayChartBarPeriodType == IBPT_DAYS_MINS_SECS;
	state.Error = ConfigError(barPeriod.ChartDataType, barPeriod.IntradayChartBarPeriodType, sc.SecondsPerBar,
		sc.BaseDataEndDateTime.GetArraySize() >= sc.ArraySize);
	if (!state.Error.empty())
	{
		// Only the message is drawn. Once the cause is gone (the end times are loaded), the
		// engine is rebuilt from bar 0.
		state.ResetEngine();
		DeleteRanges(sc, state);
		return;
	}

	// Hidden (sc.HideStudy) still processes, so showing the study again draws at once;
	// UpdateRanges then removes the ranges and the callback draws nothing.
	ProcessBars(sc, state, timeBased);

	// The developing profile, built once per call (O(rows)) for the ranges and the callback.
	const DisplaySettings display = ReadDisplay(sc);
	state.LiveShown		= display.ShowLive && state.Engine.LiveInSession && state.Engine.HasLiveRows();
	state.LiveProfile	= state.LiveShown ? state.Engine.LiveProfile() : TpoProfile();
	UpdateRanges(sc, state, display);
}

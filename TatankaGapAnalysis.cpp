// Copyright (c) 2026 Tatanka Trading LLC.
// This Source Code Form is subject to the Mozilla Public License, v. 2.0.
// If a copy of the MPL was not distributed with this file, obtain one at https://mozilla.org/MPL/2.0/.
// Tatanka Gap Analysis v1.0.0 for Sierra Chart - tatankatrading.com
// Sierra Chart port of the NinjaTrader 8 / Pine v6 "Gap Analysis".
//
// The gap between one RTH session's last chart-bar close (the fill target) and the next
// RTH open, tracked over every loaded bar until price fills it. The engine below is a
// line-by-line port of the NinjaTrader engine (TatankaGapAnalysis.cs, ENGINE_BEGIN..END)
// with no Sierra Chart calls, so the tests can include this file. Sierra bars are stamped
// at their START, NinjaTrader's at their end, so a bar is classified by its start plus
// the bar length, converted to Chicago time.
//
// The live bar is recalculated on every tick: the engine state before the last bar is
// kept as a checkpoint, restored, and the bar processed again with its current prices.
//
// The zone shading is transparent Rectangle Highlight drawings (the drawing callback can't
// draw transparency, and the bars must show through), sent to Sierra Chart only when a zone
// changes, and drawn underneath the bars. Zone outlines, fill-target lines, labels and the
// table are drawn in a drawing callback over them, blended over the chart background, so the
// shading never covers a label or the table. Alerts fire on live data only, once per event.

#include "sierrachart.h"

#include <algorithm>
#include <climits>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <functional>
#include <map>
#include <string>
#include <vector>

SCDLLName("Tatanka Gap Analysis")

namespace
{
	enum InputIndex
	{
		IN_ENABLED,
		IN_RTH_START,
		IN_RTH_END,
		IN_MIN_GAP,
		IN_MAX_VISIBLE,
		IN_EXTEND_RIGHT,
		IN_SHOW_ZONES,
		IN_SHRINK,
		IN_SHOW_TOUCHED,
		IN_HIDE_FILLED,
		IN_SHOW_LINES,
		IN_LINE_STYLE,
		IN_LINE_WIDTH,
		IN_SHOW_LABELS,
		IN_LABEL_FONT,
		IN_GAP_OPACITY,
		IN_FILLED_OPACITY,
		IN_UP_COLOR,
		IN_DOWN_COLOR,
		IN_FILLED_COLOR,
		IN_SHOW_TABLE,
		IN_TABLE_POSITION,
		IN_TABLE_FONT,
		IN_ALERT_NEW,
		IN_ALERT_FILL,
		IN_ALERT_SOUND,
		IN_ALERT_SOUND_FILE
	};

	enum LineStyleOption { LS_SOLID, LS_DASHED, LS_DOTTED };
	enum TablePositionOption { TP_TOP_RIGHT, TP_TOP_LEFT, TP_BOTTOM_RIGHT, TP_BOTTOM_LEFT, TP_MIDDLE_RIGHT, TP_MIDDLE_LEFT };

	// Persistent variable keys
	const int PP_STATE = 1;

	const int NO_SESSION = -1;

	// NinjaTrader's fixed brushes (WhiteSmoke text, Goldenrod warnings).
	const uint32_t COLOR_WHITE_SMOKE	= RGB(245, 245, 245);
	const uint32_t COLOR_GOLDENROD		= RGB(218, 165, 32);

	const char* const MSG_INVALID_SESSION	= "Enter different, valid RTH start/end times.";
	const char* const MSG_UNSUPPORTED_BARS	= "Use a Minute or Second chart. Session boundaries require time-based bars.";

	// ---- Logic (no Sierra Chart calls, so it can be unit tested) ----

	using PriceFormatter = std::function<std::string(double)>;

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

	// The RTH session a bar belongs to: the Chicago calendar date of the session, or
	// NO_SESSION for an overnight (ETH) bar. endSeconds is the bar's nominal end (start +
	// bar length) in Chicago time, in seconds since Sierra's base date; rthStart/rthEnd are
	// seconds since midnight. NinjaTrader classifies the bar's last instant (end - 1 tick):
	// with whole-second ends that is start < end-of-bar <= end, so the 1-minute bar that
	// starts at 08:30 is the first RTH bar and the one starting at 14:59 the last.
	int SessionKey(int64_t endSeconds, int rthStart, int rthEnd)
	{
		int64_t date	= FloorDiv(endSeconds, SECONDS_PER_DAY);
		int clock		= (int)(endSeconds - date * SECONDS_PER_DAY);
		if (clock == 0)
		{
			// A bar ending at midnight belongs to the day before.
			date--;
			clock = SECONDS_PER_DAY;
		}

		if (rthStart < rthEnd)
			return rthStart < clock && clock <= rthEnd ? (int)date : NO_SESSION;
		if (rthStart > rthEnd)
		{
			// The window crosses midnight: bars after midnight belong to the previous date's session.
			if (clock > rthStart)
				return (int)date;
			if (clock <= rthEnd)
				return (int)(date - 1);
		}
		return NO_SESSION;
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
	// data past it), and, with New Bar at Session Start, the trading day's start (the Session
	// Start Time, or the Evening Start Time with the evening session), where Sierra Chart cuts
	// the bar. INT64_MAX when there is none or the session times are unset. NinjaTrader's bars
	// end at its session boundaries too, and it stamps them there.
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

	// Sierra Chart's "Include Columns With No Data" adds bars without trades: no volume, and
	// the previous close as all four prices (or zeros with "Do Not Draw Columns With No
	// Data"). NinjaTrader and TradingView never see such a bar, so it must not open a session,
	// set the RTH close or fill a gap. A bar with prices of its own always counts, so a symbol
	// without volume data loses at most a flat bar at the previous close.
	bool IsEmptyColumn(double volume, double trades, double open, double high, double low, double close, bool hasPrevious,
		double previousClose)
	{
		if (volume != 0 || trades != 0)
			return false;
		if (open == 0 && high == 0 && low == 0 && close == 0)
			return true;
		return hasPrevious && open == previousClose && high == previousClose && low == previousClose && close == previousClose;
	}

	// Sierra's tick size is a float in older versions (0.01f is 0.0099999998) and a double in newer
	// ones. This is the decimal tick it stands for.
	double DecimalTickSize(double tickSize)
	{
		if (!(tickSize > 0))
			return 0;
		char text[32];
		snprintf(text, sizeof(text), "%.6g", (double)tickSize);
		return strtod(text, nullptr);
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

	// NinjaTrader compares the size with the minimum exactly, which can drop a gap that is
	// exactly the minimum by rounding error. A gap of zero is never stored.
	bool MeetsMinimum(double size, double minimum)
	{
		return size > 0 && size >= minimum - 1e-9 * (std::max)(1.0, minimum);
	}

	struct GapRecord
	{
		int		Ordinal		= 0;
		int		StartBar	= 0;
		int		NextGapBar	= -1;	// opening bar of the next stored gap
		int		FillBar		= -1;
		int		Direction	= 0;	// +1 up, -1 down
		double	OpenPrice	= 0;
		double	SettlePrice	= 0;	// the prior session's last RTH close: the fill target
		double	FillEdge	= 0;	// deepest wick into the zone, clamped at the settle
		int		EmptyBeforeStart	= 0;	// empty columns skipped before the opening bar
		int		EmptyBeforeFill		= 0;	// and before the fill bar

		double Size() const { return std::fabs(OpenPrice - SettlePrice); }
		bool Filled() const { return FillBar >= 0; }

		// Bar counts as NinjaTrader and TradingView count them: Sierra Chart's empty columns
		// (Include Columns With No Data) are bars on neither, so those in between don't count.
		// Geometry keeps the Sierra Chart indices.
		int BarsToFill() const { return Filled() ? FillBar - StartBar - (EmptyBeforeFill - EmptyBeforeStart) : 0; }
		int BarsElapsed(int currentBar, int emptyColumns) const { return currentBar - StartBar - (emptyColumns - EmptyBeforeStart); }

		double FillPercent() const
		{
			return Filled() ? 100.0 : (std::min)(100.0, std::fabs(OpenPrice - FillEdge) / Size() * 100.0);
		}

		// Last bar of the zone: the fill bar or the current bar, or, without the right
		// extension, the bar before the next stored gap.
		int DrawingEndBar(int currentBar, bool extend) const
		{
			int end = Filled() ? FillBar : currentBar;
			if (!extend && NextGapBar >= 0)
				end = (std::min)(end, NextGapBar - 1);
			return (std::max)(StartBar, end);
		}
	};

	struct GapUpdate
	{
		int					NewGap = -1;	// ordinal of the gap this bar opened, or -1
		std::vector<int>	Filled;			// ordinals filled on this bar, newest first
	};

	struct GapFrame
	{
		int					StoredCount	= 0;
		int					CurrentBar	= -1;
		int					EmptyColumns	= 0;	// empty columns skipped through CurrentBar
		int					Consecutive	= 0;
		int					Latest		= -1;	// ordinal of the newest stored gap, or -1
		std::vector<int>	Visible;			// selected ordinals, oldest first (newest painted last)
	};

	// Everything one Update can change, saved before the (live) last bar.
	struct GapCheckpoint
	{
		int					Bar				= -1;	// the bar this state precedes; -1 = none
		size_t				HistoryCount	= 0;
		int					PriorNextGapBar	= -1;
		int					TrackedSession	= NO_SESSION;
		double				TrackedClose	= 0;
		int					CurrentBar		= -1;
		int					EmptyColumns	= 0;
		int					Consecutive		= 0;
		std::vector<int>	Active;
		std::vector<double>	ActiveFillEdge;
	};

	struct GapEngine
	{
		std::vector<GapRecord>	History;	// every stored gap, oldest first; index = Ordinal
		std::vector<int>		Active;		// ordinals of the unfilled gaps, oldest first
		double					MinimumGap		= 0;
		int						TrackedSession	= NO_SESSION;
		double					TrackedClose	= 0;
		int						CurrentBar		= -1;
		int						EmptyColumns	= 0;	// empty columns skipped so far (Skip)
		int						Consecutive		= 0;

		explicit GapEngine(double minimumGap = 0) : MinimumGap(minimumGap) {}

		GapUpdate Update(int bar, int sessionKey, double open, double high, double low, double close)
		{
			GapUpdate update;
			CurrentBar = bar;
			if (sessionKey != NO_SESSION)
			{
				if (sessionKey != TrackedSession)
				{
					// The first loaded session only supplies the RTH close. Every later session
					// can open a gap, even on an RTH-only chart with no overnight bars.
					if (TrackedSession != NO_SESSION)
					{
						const double signedSize = open - TrackedClose;
						if (MeetsMinimum(std::fabs(signedSize), MinimumGap))
						{
							GapRecord gap;
							gap.Ordinal		= (int)History.size();
							gap.StartBar	= bar;
							gap.Direction	= signedSize > 0 ? 1 : -1;
							gap.OpenPrice	= open;
							gap.SettlePrice	= TrackedClose;
							gap.FillEdge	= open;
							gap.EmptyBeforeStart = EmptyColumns;

							// The streak compares with the last stored gap; sessions without a
							// qualifying gap neither break nor extend it.
							const bool hasPrior = !History.empty();
							if (hasPrior)
								History.back().NextGapBar = bar;
							Consecutive = hasPrior && History.back().Direction == gap.Direction ? Consecutive + 1 : 1;

							History.push_back(gap);
							Active.push_back(gap.Ordinal);
							update.NewGap = gap.Ordinal;
						}
					}
					TrackedSession = sessionKey;
				}
				TrackedClose = close;
			}

			// Every chart bar, overnight bars and the opening bar included, works on the
			// unfilled gaps. Filled gaps are never rescanned.
			for (size_t k = Active.size(); k-- > 0;)
			{
				GapRecord& gap = History[(size_t)Active[k]];
				bool filled;
				if (gap.Direction > 0)
				{
					gap.FillEdge	= (std::max)(gap.SettlePrice, (std::min)(gap.FillEdge, low));
					filled			= low <= gap.SettlePrice;
				}
				else
				{
					gap.FillEdge	= (std::min)(gap.SettlePrice, (std::max)(gap.FillEdge, high));
					filled			= high >= gap.SettlePrice;
				}
				if (filled)
				{
					gap.FillEdge		= gap.SettlePrice;
					gap.FillBar			= bar;
					gap.EmptyBeforeFill	= EmptyColumns;
					update.Filled.push_back(gap.Ordinal);
					Active.erase(Active.begin() + (std::ptrdiff_t)k);
				}
			}
			return update;
		}

		// A bar the engine must not see (an empty column): it only becomes the current bar,
		// and is left out of the bar counts.
		void Skip(int bar)
		{
			CurrentBar = bar;
			EmptyColumns++;
		}

		// The gaps to draw: the newest maximumVisible (0 = all) of those that reach the
		// visible bars, oldest first. Tracking never depends on this. A zone that doesn't
		// extend reaches the view through its right side, edgeBars after its last bar: 0 is
		// NinjaTrader's rule (its zone ends at that bar's right edge); the study passes
		// ZONE_END_BARS, as its zones end at the next bar's center, which shows half a bar of
		// the zone when that next bar is the first visible one.
		GapFrame Snapshot(int firstVisibleBar, int lastVisibleBar, bool extend, bool hideFilled, int maximumVisible, int edgeBars = 0) const
		{
			GapFrame frame;
			frame.StoredCount	= (int)History.size();
			frame.CurrentBar	= CurrentBar;
			frame.EmptyColumns	= EmptyColumns;
			frame.Consecutive	= Consecutive;
			frame.Latest		= History.empty() ? -1 : (int)History.size() - 1;

			const size_t candidates = hideFilled ? Active.size() : History.size();
			for (size_t k = candidates; k-- > 0;)
			{
				const GapRecord& gap = History[hideFilled ? (size_t)Active[k] : k];
				if (gap.StartBar > lastVisibleBar)
					continue;
				const bool reachesView = (extend && !gap.Filled()) || gap.DrawingEndBar(CurrentBar, extend) + edgeBars >= firstVisibleBar;
				if (!reachesView)
					continue;
				if (maximumVisible > 0 && (int)frame.Visible.size() >= maximumVisible)
					break;
				frame.Visible.push_back(gap.Ordinal);
			}
			std::reverse(frame.Visible.begin(), frame.Visible.end());
			return frame;
		}

		GapCheckpoint Save(int bar) const
		{
			GapCheckpoint checkpoint;
			checkpoint.Bar				= bar;
			checkpoint.HistoryCount		= History.size();
			checkpoint.PriorNextGapBar	= History.empty() ? -1 : History.back().NextGapBar;
			checkpoint.TrackedSession	= TrackedSession;
			checkpoint.TrackedClose		= TrackedClose;
			checkpoint.CurrentBar		= CurrentBar;
			checkpoint.EmptyColumns		= EmptyColumns;
			checkpoint.Consecutive		= Consecutive;
			checkpoint.Active			= Active;
			checkpoint.ActiveFillEdge.reserve(Active.size());
			for (int ordinal : Active)
				checkpoint.ActiveFillEdge.push_back(History[(size_t)ordinal].FillEdge);
			return checkpoint;
		}

		// Back to the state saved before checkpoint.Bar. Only the active gaps, a gap opened
		// on that bar and the previous gap's NextGapBar can have changed since.
		void Restore(const GapCheckpoint& checkpoint)
		{
			if (History.size() > checkpoint.HistoryCount)
				History.erase(History.begin() + (std::ptrdiff_t)checkpoint.HistoryCount, History.end());
			if (!History.empty())
				History.back().NextGapBar = checkpoint.PriorNextGapBar;
			Active = checkpoint.Active;
			for (size_t k = 0; k < Active.size(); k++)
			{
				GapRecord& gap		= History[(size_t)Active[k]];
				gap.FillEdge		= checkpoint.ActiveFillEdge[k];
				gap.FillBar			= -1;
				gap.EmptyBeforeFill	= 0;
			}
			TrackedSession	= checkpoint.TrackedSession;
			TrackedClose	= checkpoint.TrackedClose;
			CurrentBar		= checkpoint.CurrentBar;
			EmptyColumns	= checkpoint.EmptyColumns;
			Consecutive		= checkpoint.Consecutive;
		}

		// Changes whenever anything the zones, labels or table show changes (a gap opens,
		// a fill edge moves, a gap fills, a new bar). A live tick that changes nothing keeps it.
		uint32_t Signature() const
		{
			uint32_t hash = 2166136261u;
			const uint32_t stored = (uint32_t)History.size();
			hash = Fnv1a(hash, &stored, sizeof(stored));
			hash = Fnv1a(hash, &CurrentBar, sizeof(CurrentBar));
			hash = Fnv1a(hash, &Consecutive, sizeof(Consecutive));
			for (int ordinal : Active)
			{
				hash = Fnv1a(hash, &ordinal, sizeof(ordinal));
				hash = Fnv1a(hash, &History[(size_t)ordinal].FillEdge, sizeof(double));
			}
			return hash;
		}
	};

	// .NET Framework's "0.##" (NinjaTrader 8 runs on .NET Framework 4.8): the double's 15
	// significant digits, rounded half away from zero to two decimals, trailing zeros dropped.
	std::string FormatPercent(double value)
	{
		if (!(value == value))
			return "NaN";

		char text[48];
		if (std::fabs(value) >= 1e15)
		{
			snprintf(text, sizeof(text), "%.0f", value);
			return text;
		}
		snprintf(text, sizeof(text), "%.14e", std::fabs(value));	// d.dddddddddddddde+XX
		char digits[15];
		digits[0] = text[0];
		memcpy(digits + 1, text + 2, 14);
		const char* exponentText = strchr(text, 'e');
		const int exponent	= exponentText ? atoi(exponentText + 1) : 0;
		const int keep		= exponent + 3;	// significant digits through the second decimal
		if (keep < 0 || digits[0] == '0')
			return "0";

		unsigned long long hundredths = 0;
		for (int k = 0; k < keep; k++)
			hundredths = hundredths * 10 + (unsigned long long)(k < 15 ? digits[k] - '0' : 0);
		if (keep < 15 && digits[keep] >= '5')
			hundredths++;
		if (hundredths == 0)
			return "0";

		const char* sign = value < 0 ? "-" : "";
		const unsigned long long units = hundredths / 100;
		const unsigned int fraction = (unsigned int)(hundredths % 100);
		if (fraction == 0)
			snprintf(text, sizeof(text), "%s%llu", sign, units);
		else if (fraction % 10 == 0)
			snprintf(text, sizeof(text), "%s%llu.%u", sign, units, fraction / 10);
		else
			snprintf(text, sizeof(text), "%s%llu.%02u", sign, units, fraction);
		return text;
	}

	const char* DirectionText(const GapRecord& gap)
	{
		return gap.Direction > 0 ? "UP" : "DOWN";
	}

	std::string NewGapAlertText(const GapRecord& gap, const PriceFormatter& price)
	{
		return std::string("GAP ") + DirectionText(gap) + " " + price(gap.Size()) + " pts | Open: " + price(gap.OpenPrice)
			+ " | RTH close: " + price(gap.SettlePrice);
	}

	std::string FillAlertText(const GapRecord& gap, const PriceFormatter& price)
	{
		return std::string("GAP ") + DirectionText(gap) + " FILLED | " + price(gap.Size()) + " pts in " + std::to_string(gap.BarsToFill()) + " bars";
	}

	// Each new-gap and fill event alerts at most once, however often the live bar is
	// recalculated. Events are marked whether or not they alert, so a recalculation,
	// a backfill or turning an alert on later never replays one.
	struct AlertBook
	{
		int							HandledNewGaps = 0;
		std::vector<unsigned char>	HandledFill;

		// Marks this update's events; returns the alert messages to send (only when live).
		std::vector<std::string> Handle(const GapEngine& engine, const GapUpdate& update, bool live, bool alertNew, bool alertFill,
			const PriceFormatter& price)
		{
			std::vector<std::string> messages;
			if (update.NewGap >= HandledNewGaps)
			{
				if (live && alertNew)
					messages.push_back(NewGapAlertText(engine.History[(size_t)update.NewGap], price));
				HandledNewGaps = update.NewGap + 1;
			}
			for (int ordinal : update.Filled)
			{
				if (HandledFill.size() <= (size_t)ordinal)
					HandledFill.resize((size_t)ordinal + 1, 0);
				if (HandledFill[(size_t)ordinal])
					continue;
				if (live && alertFill)
					messages.push_back(FillAlertText(engine.History[(size_t)ordinal], price));
				HandledFill[(size_t)ordinal] = 1;
			}
			return messages;
		}
	};

	bool SupportedBars(int chartDataType, int intradayBarPeriodType, int secondsPerBar)
	{
		return chartDataType == INTRADAY_DATA && intradayBarPeriodType == IBPT_DAYS_MINS_SECS
			&& secondsPerBar > 0 && secondsPerBar < SECONDS_PER_DAY;
	}

	// NinjaTrader's order: the session first, then the bar type. Empty = no error.
	const char* ConfigError(int rthStart, int rthEnd, bool supportedBars)
	{
		if (rthStart == rthEnd)
			return MSG_INVALID_SESSION;
		if (!supportedBars)
			return MSG_UNSUPPORTED_BARS;
		return "";
	}

	bool IsBlank(const std::string& text)
	{
		for (char c : text)
			if (c != ' ' && c != '\t' && c != '\r' && c != '\n')
				return false;
		return true;
	}

	// A file name is looked up in Sierra Chart's AlertSounds folder; a rooted path is used as is.
	std::string AlertSoundPath(const std::string& file, const std::string& sierraFolder)
	{
		const bool rooted = !file.empty() && (file[0] == '\\' || file[0] == '/' || (file.size() >= 2 && file[1] == ':'));
		return rooted ? file : sierraFolder + "\\AlertSounds\\" + file;
	}

	// ---- Presentation (pure; the drawing callback uses these) ----

	enum ZonePartKind { ZP_FULL, ZP_TOUCHED, ZP_REMAINING };

	struct ZoneStyle
	{
		bool		Extend			= true;
		bool		Shrink			= true;
		bool		ShowTouched		= true;
		uint32_t	UpColor			= RGB(50, 205, 50);
		uint32_t	DownColor		= RGB(205, 92, 92);
		uint32_t	FilledColor		= RGB(112, 128, 144);
		int			GapOpacity		= 20;
		int			FilledOpacity	= 10;
	};

	struct ZonePart
	{
		int			Kind			= ZP_FULL;
		double		Top				= 0;
		double		Bottom			= 0;
		int			BeginBar		= 0;
		int			EndBar			= 0;	// the last bar it covers; an extended part is anchored at its start
		bool		ExtendRight		= false;
		uint32_t	Color			= 0;
		int			Opacity			= 0;	// the opacity input, before fading
		int			Transparency	= 0;	// Sierra TransparencyLevel, faded
		bool		Outline			= false;
	};

	// Older gaps fade: 100, 85, 70, 55, then 40 percent (age counts hidden filled gaps too).
	int FadePercent(int age)
	{
		return 100 - 15 * (std::min)((std::max)(age, 0), 4);
	}

	// Opacity percent x fade -> Sierra's TransparencyLevel (0 opaque ... 100 invisible), rounded half up.
	int ZoneTransparency(int opacity, int fadePercent)
	{
		return 100 - (opacity * fadePercent + 50) / 100;
	}

	// NinjaTrader's zone outline: min(0.7, opacity x fade + 0.25); the 0.25 is not faded.
	double OutlineAlpha(int opacity, int fadePercent)
	{
		return (std::min)(0.70, opacity / 100.0 * (fadePercent / 100.0) + 0.25);
	}

	// Horizontal zone edges. A zone covers its whole last bar, as on both originals
	// (NinjaTrader to the bar's right edge, TradingView to its close time), so a gap filled on
	// its opening bar is still a bar wide. Sierra Chart draws a Rectangle Highlight from its
	// begin bar's center to its end bar's center (check S1), so a zone's drawing ends at the
	// center of the bar after its last bar (ZoneEndIndex), and the outline, target line, label
	// and the test for reaching the view use the same edges. (If a Sierra Chart version drew
	// rectangles to bar-slot edges, ZONE_END_BARS would be 0 and ZONE_EDGE_OFFSET NinjaTrader's
	// half bar, (std::max)(1, sc.ChartBarSpacing / 2).)
	const int ZONE_END_BARS		= 1;
	const int ZONE_EDGE_OFFSET	= 0;

	// The zone drawings are drawn underneath the price graph, so this study's drawing callback
	// (outlines, target lines, labels and the table) always paints over them, as NinjaTrader
	// paints all of those over its fills. A chart drawing that is not drawn underneath is drawn
	// above the main price graph and every study (Sierra Chart's s_UseTool documentation): the
	// shading would then tint the labels and the table wherever a zone crosses them, and hide
	// them at a high opacity. The cost: the bars are drawn over the shading instead of under it,
	// which at the default 10-20 % opacity is barely visible. (Check S2.)
	const bool ZONES_UNDER_BARS = true;

	// Whether the callback paints over the zone fills: it then paints NinjaTrader's stroke over
	// its fill as one opaque color (OverZone). With the drawings above the bars the fills would
	// land on the callback's outline and target line instead, and a color blended over the
	// chart background composites to the same.
	const bool CALLBACK_PAINTS_OVER_ZONES = ZONES_UNDER_BARS;

	// A gap's shading: the whole zone (filled, or shrinking off), or the touched part
	// (filled color, never extended) and the remaining part (direction color).
	std::vector<ZonePart> ZoneParts(const GapRecord& gap, int storedCount, int currentBar, const ZoneStyle& style)
	{
		const int fade			= FadePercent(storedCount - 1 - gap.Ordinal);
		const bool extends		= style.Extend && !gap.Filled();
		const int endBar		= gap.DrawingEndBar(currentBar, style.Extend);
		const int anchorEnd		= extends ? gap.StartBar : endBar;
		const bool up			= gap.Direction > 0;
		const double top		= (std::max)(gap.OpenPrice, gap.SettlePrice);
		const double bottom		= (std::min)(gap.OpenPrice, gap.SettlePrice);
		const uint32_t direction = up ? style.UpColor : style.DownColor;

		std::vector<ZonePart> parts;
		auto add = [&](int kind, double partTop, double partBottom, int end, bool extendRight, uint32_t color, int opacity, bool outline)
		{
			if (partTop <= partBottom)
				return;
			ZonePart part;
			part.Kind			= kind;
			part.Top			= partTop;
			part.Bottom			= partBottom;
			part.BeginBar		= gap.StartBar;
			part.EndBar			= end;
			part.ExtendRight	= extendRight;
			part.Color			= color;
			part.Opacity		= opacity;
			part.Transparency	= ZoneTransparency(opacity, fade);
			part.Outline		= outline;
			parts.push_back(part);
		};

		if (gap.Filled() || !style.Shrink)
			add(ZP_FULL, top, bottom, anchorEnd, extends, gap.Filled() ? style.FilledColor : direction,
				gap.Filled() ? style.FilledOpacity : style.GapOpacity, true);
		else
		{
			if (style.ShowTouched && gap.FillPercent() > 0)
				add(ZP_TOUCHED, up ? gap.OpenPrice : gap.FillEdge, up ? gap.FillEdge : gap.OpenPrice,
					extends ? currentBar : endBar, false, style.FilledColor, style.FilledOpacity, false);
			add(ZP_REMAINING, up ? gap.FillEdge : gap.SettlePrice, up ? gap.SettlePrice : gap.FillEdge,
				anchorEnd, extends, direction, style.GapOpacity, true);
		}
		return parts;
	}

	// The part's Rectangle Highlight EndIndex: the center of the bar after its last bar. An
	// extended part's last bar is its opening bar, so it ends at the bar after that, a fixed
	// index (no update per new bar), and ExtendRight carries it to the right edge. Never its
	// begin bar: Sierra Chart requires a drawing to span at least two bars (s_UseTool
	// documentation). Past the last loaded bar the index is in the chart's right-side fill
	// space, which Sierra Chart supports.
	int ZoneEndIndex(const ZonePart& part)
	{
		return (std::max)(part.BeginBar + 1, part.EndBar + ZONE_END_BARS);
	}

	// GAP UP  12.50 pts / 37.5% FILLED
	std::vector<std::string> LabelLines(const GapRecord& gap, const PriceFormatter& price)
	{
		return {
			std::string(gap.Direction > 0 ? "GAP UP" : "GAP DOWN") + "  " + price(gap.Size()) + " pts",
			gap.Filled() ? std::string("FILLED") : FormatPercent(gap.FillPercent()) + "% FILLED"
		};
	}

	struct TableRow
	{
		std::string	Key;
		std::string	Value;
		uint32_t	ValueColor = COLOR_WHITE_SMOKE;
	};

	// The table describes the newest stored gap, drawn or not.
	std::vector<TableRow> TableRows(const GapEngine& engine, const GapFrame& frame, const PriceFormatter& price,
		uint32_t upColor, uint32_t downColor)
	{
		std::vector<TableRow> rows;
		auto add = [&rows](const char* key, const std::string& value, uint32_t color)
		{
			TableRow row;
			row.Key			= key;
			row.Value		= value;
			row.ValueColor	= color;
			rows.push_back(row);
		};

		add("TATANKA", "GAP ANALYSIS", COLOR_WHITE_SMOKE);
		add("HISTORY", std::to_string(frame.StoredCount) + " stored / " + std::to_string(frame.Visible.size()) + " in view", COLOR_WHITE_SMOKE);
		if (frame.Latest < 0)
		{
			add("STATUS", "Waiting for a qualifying RTH gap", COLOR_WHITE_SMOKE);
			return rows;
		}

		const GapRecord& latest	= engine.History[(size_t)frame.Latest];
		const bool up			= latest.Direction > 0;
		const double percent	= latest.FillPercent();
		add("GAP", up ? "UP" : "DOWN", up ? upColor : downColor);
		add("SIZE", price(latest.Size()) + " pts", COLOR_WHITE_SMOKE);
		// A filled gap shows the Up color in both directions, as on both originals.
		add("STATUS", latest.Filled() ? std::string("FILLED") : FormatPercent(percent) + "% FILLED",
			latest.Filled() ? upColor : percent > 50 ? COLOR_GOLDENROD : COLOR_WHITE_SMOKE);
		add("RTH CLOSE", price(latest.SettlePrice), COLOR_WHITE_SMOKE);
		add("BARS", latest.Filled() ? std::to_string(latest.BarsToFill()) + " to fill"
			: std::to_string(latest.BarsElapsed(frame.CurrentBar, frame.EmptyColumns)) + " elapsed", COLOR_WHITE_SMOKE);
		add("CONSECUTIVE", std::to_string(frame.Consecutive) + (up ? " bull" : " bear"), COLOR_WHITE_SMOKE);
		add("EXHAUSTION", frame.Consecutive >= 3 ? "ELEVATED" : "---", frame.Consecutive >= 3 ? COLOR_GOLDENROD : COLOR_WHITE_SMOKE);
		return rows;
	}

	using TextMeasure = std::function<int(const std::string&)>;

	// Greedy word wrap at spaces, like a DirectWrite layout of that width: a line breaks
	// before the word that would overflow it, and a word wider than the width stays whole.
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

	// NinjaTrader's table placement: 8 DIPs in from the left, right and bottom edges, 20 below
	// the top, or centered vertically; never higher than 2 DIPs below the panel top.
	void TableOrigin(int position, int panelLeft, int panelTop, int panelRight, int panelBottom, int width, int height,
		int inset8, int inset20, int inset2, int& x, int& y)
	{
		const bool onLeft	= position == TP_TOP_LEFT || position == TP_BOTTOM_LEFT || position == TP_MIDDLE_LEFT;
		const bool onBottom	= position == TP_BOTTOM_LEFT || position == TP_BOTTOM_RIGHT;
		const bool inMiddle	= position == TP_MIDDLE_LEFT || position == TP_MIDDLE_RIGHT;
		x = onLeft ? panelLeft + inset8 : panelRight - width - inset8;
		y = onBottom ? panelBottom - height - inset8
			: inMiddle ? panelTop + (panelBottom - panelTop - height) / 2
			: panelTop + inset20;
		y = (std::max)(panelTop + inset2, y);
	}

	// What a zone drawing shows; the drawing is sent to Sierra Chart again only when it changes.
	uint32_t PartSignature(const ZonePart& part)
	{
		uint32_t hash = 2166136261u;
		const int extend = part.ExtendRight ? 1 : 0;
		hash = Fnv1a(hash, &part.BeginBar, sizeof(part.BeginBar));
		hash = Fnv1a(hash, &part.EndBar, sizeof(part.EndBar));
		hash = Fnv1a(hash, &extend, sizeof(extend));
		hash = Fnv1a(hash, &part.Top, sizeof(part.Top));
		hash = Fnv1a(hash, &part.Bottom, sizeof(part.Bottom));
		hash = Fnv1a(hash, &part.Color, sizeof(part.Color));
		hash = Fnv1a(hash, &part.Transparency, sizeof(part.Transparency));
		return hash == 0 ? 1 : hash;  // 0 means "not drawn"
	}

	// ---- Rendering helpers (from TatankaIfThenBiasTable.cpp) ----

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

	// A callback color at alpha that lies on a zone fill of the same color at fillOpacity
	// (NinjaTrader paints the outline and the target line over the fill), as an opaque pixel:
	// over the chart background when the fill is painted on it afterwards, else the composite.
	uint32_t OverZone(uint32_t color, double alpha, double fillOpacity, uint32_t background, bool callbackPaintsLast)
	{
		if (callbackPaintsLast)
			alpha = 1.0 - (1.0 - alpha) * (1.0 - fillOpacity);
		return Blend(color, alpha, background);
	}

	// On/off run lengths in multiples of the line width, matching NinjaTrader's Direct2D
	// styles: Dash = 2 on, 2 off; Dot = dots one line width across, one width apart.
	// Drawn as filled rectangles, so styled lines keep their width (GDI pens draw wide
	// dashed lines solid).
	const std::vector<int>& DashPattern(int style)
	{
		static const std::vector<int> solid;
		static const std::vector<int> dash	= {2, 2};
		static const std::vector<int> dot	= {1, 1};
		return style == LS_DASHED ? dash : style == LS_DOTTED ? dot : solid;
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

	// A line from x0 to x1 covering rows top..bottom - 1, dashed in multiples of width (the
	// line width), the pattern starting at x0. Drawing only some rows of a line with the
	// same x0 and width keeps its dashes in place.
	void DrawHorizontalLine(SCStudyInterfaceRef sc, int x0, int x1, int top, int bottom, int width, int style, uint32_t color)
	{
		width = (std::max)(1, width);
		const std::vector<int>& pattern = DashPattern(style);

		if (pattern.empty())
		{
			FillRect(sc, x0, top, x1, bottom, color);
			return;
		}

		size_t run = 0;
		for (int x = x0; x < x1; run = (run + 1) % pattern.size())
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
	// (high-DPI) display, so the larger of the two is used and a label plate or table
	// cell is never smaller than its text.
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

	// ---- Sierra Chart glue ----

	// One zone drawing: the Sierra Chart line number and what it was last drawn with.
	struct ZoneSlot
	{
		int			LineNumber	= 0;
		uint32_t	Signature	= 0;
		bool		Wanted		= false;
	};

	struct StudyState
	{
		GapEngine		Engine;
		GapCheckpoint	Checkpoint;
		AlertBook		Alerts;
		uint32_t		InputsKey	= 0;
		bool			Built		= false;
		std::string		Error;	// configuration error for the drawing callback

		// Zone drawings by Ordinal * 3 + ZonePartKind. A full recalculation deletes them
		// (Sierra Chart removes a study's own drawings then) and adds them again.
		std::map<int, ZoneSlot>	Zones;
		uint32_t				ZonesKey	= 0;	// what the drawings show; 0 = check them all

		void ResetEngine()
		{
			Engine		= GapEngine();
			Checkpoint	= GapCheckpoint();
			Alerts		= AlertBook();
			InputsKey	= 0;
			Built		= false;
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

	// Sierra stamps bars at their start in the chart's time zone. The session is decided by
	// the bar's end in Chicago time (daylight saving included), whatever the chart's zone.
	// A bar cut short at a session boundary (a Session Times end, New Bar at Session Start)
	// ends there, not a full bar length later: NinjaTrader stamps it at that end, so a 14:30
	// bar cut at a 15:00 session end is the session's last RTH bar, and an 08:00 bar cut at
	// an 08:30 trading-day start is not the opening bar. The next bar's start shows the cut
	// on a loaded bar; the session times show it on the live bar before the next one exists.
	int BarSessionKey(SCStudyInterfaceRef sc, int index, int rthStart, int rthEnd)
	{
		const SCDateTime barStart = sc.BaseDateTimeIn[index];
		SCDateTime barEnd = barStart + SCDateTime::SECONDS(sc.SecondsPerBar);
		if (index + 1 < sc.ArraySize && barStart < sc.BaseDateTimeIn[index + 1] && sc.BaseDateTimeIn[index + 1] < barEnd)
			barEnd = sc.BaseDateTimeIn[index + 1];
		const int64_t cut = SessionCutAfter(barStart.GetSecondsSinceBaseDate(), SessionsOf(sc));
		if (cut < barEnd.GetSecondsSinceBaseDate())
			barEnd = SCDateTime((int)(cut / SECONDS_PER_DAY), (int)(cut % SECONDS_PER_DAY));
		return SessionKey(sc.ConvertDateTimeFromChartTimeZone(barEnd, TIMEZONE_CHICAGO).GetSecondsSinceBaseDate(), rthStart, rthEnd);
	}

	std::string SierraChartFolder()
	{
		wchar_t path[MAX_PATH * 4];
		const DWORD length = GetModuleFileNameW(nullptr, path, (DWORD)(sizeof(path) / sizeof(path[0])));
		if (length == 0 || length >= sizeof(path) / sizeof(path[0]))
			return std::string();
		std::wstring folder(path, length);
		const size_t slash = folder.find_last_of(L"\\/");
		folder = slash == std::wstring::npos ? std::wstring() : folder.substr(0, slash);
		const int bytes = WideCharToMultiByte(CP_UTF8, 0, folder.c_str(), (int)folder.size(), nullptr, 0, nullptr, nullptr);
		std::string result(bytes > 0 ? (size_t)bytes : 0, '\0');
		if (bytes > 0)
			WideCharToMultiByte(CP_UTF8, 0, folder.c_str(), (int)folder.size(), &result[0], bytes, nullptr, nullptr);
		return result;
	}

	// A sound file plays instead of the Alert sound list. Without one: None = no alert,
	// No Sound = an Alerts Log entry only (NinjaTrader's blank sound), else that sound.
	void SendAlert(SCStudyInterfaceRef sc, const std::string& message)
	{
		// GetPathAndFileName returns "" for a blank string input, where GetString returns "Unset".
		const std::string file = sc.Input[IN_ALERT_SOUND_FILE].GetPathAndFileName();
		if (!IsBlank(file))
		{
			sc.PlaySound(AlertSoundPath(file, SierraChartFolder()).c_str(), 1, message.c_str(), 0);
			return;
		}
		const unsigned int sound = sc.Input[IN_ALERT_SOUND].GetAlertSoundNumber();
		if (sound > 0)
			sc.AlertWithMessage((int)sound - 1, message.c_str(), 0);
	}

	// Runs the engine over the new bars. A full recalculation (or anything unexpected)
	// rebuilds from bar 0 without alerts; a tick restores the state before the last
	// processed bar and processes it again with its current prices.
	void ProcessBars(SCStudyInterfaceRef sc, StudyState& state, int rthStart, int rthEnd)
	{
		const double minimum	= sc.Input[IN_MIN_GAP].GetDouble();
		const double tick		= DecimalTickSize(sc.TickSize);
		uint32_t inputsKey = 2166136261u;
		inputsKey = Fnv1a(inputsKey, &rthStart, sizeof(rthStart));
		inputsKey = Fnv1a(inputsKey, &rthEnd, sizeof(rthEnd));
		inputsKey = Fnv1a(inputsKey, &minimum, sizeof(minimum));
		inputsKey = Fnv1a(inputsKey, &tick, sizeof(tick));

		const bool rebuild = sc.IsFullRecalculation || sc.UpdateStartIndex <= 0 || !state.Built || inputsKey != state.InputsKey
			|| (sc.UpdateStartIndex < sc.ArraySize && sc.UpdateStartIndex != state.Checkpoint.Bar)
			|| sc.ArraySize - 1 < state.Checkpoint.Bar;

		int from;
		if (rebuild)
		{
			state.ResetEngine();
			state.Engine	= GapEngine(minimum);
			state.InputsKey	= inputsKey;
			state.Built		= true;
			from			= 0;
		}
		else if (sc.UpdateStartIndex >= sc.ArraySize)
			from = sc.ArraySize;
		else
		{
			state.Engine.Restore(state.Checkpoint);
			from = state.Checkpoint.Bar;
		}

		const bool live			= !rebuild && !sc.IsFullRecalculation && !sc.ChartIsDownloadingHistoricalData(sc.ChartNumber);
		const bool alertNew		= sc.Input[IN_ALERT_NEW].GetYesNo() != 0;
		const bool alertFill	= sc.Input[IN_ALERT_FILL].GetYesNo() != 0;
		const PriceFormatter price = [&sc](double value) { return std::string(sc.FormatGraphValue(value, sc.BaseGraphValueFormat).GetChars()); };

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
			const GapUpdate update = state.Engine.Update(i, BarSessionKey(sc, i, rthStart, rthEnd),
				SnapToTick(sc.Open[i], tick), SnapToTick(sc.High[i], tick), SnapToTick(sc.Low[i], tick), SnapToTick(sc.Close[i], tick));
			if (update.NewGap >= 0 || !update.Filled.empty())
				for (const std::string& message : state.Alerts.Handle(state.Engine, update, live, alertNew, alertFill, price))
					SendAlert(sc, message);
		}
	}

	ZoneStyle ReadZoneStyle(SCStudyInterfaceRef sc)
	{
		ZoneStyle style;
		style.Extend		= sc.Input[IN_EXTEND_RIGHT].GetYesNo() != 0;
		style.Shrink		= sc.Input[IN_SHRINK].GetYesNo() != 0;
		style.ShowTouched	= sc.Input[IN_SHOW_TOUCHED].GetYesNo() != 0;
		style.UpColor		= sc.Input[IN_UP_COLOR].GetColor();
		style.DownColor		= sc.Input[IN_DOWN_COLOR].GetColor();
		style.FilledColor	= sc.Input[IN_FILLED_COLOR].GetColor();
		style.GapOpacity	= (std::max)(0, (std::min)(100, sc.Input[IN_GAP_OPACITY].GetInt()));
		style.FilledOpacity	= (std::max)(0, (std::min)(100, sc.Input[IN_FILLED_OPACITY].GetInt()));
		return style;
	}

	// On a full recalculation Sierra Chart has already deleted the study's own drawings (all
	// but user-drawn ones) and may give their line numbers to new drawings, so the old
	// numbers are forgotten: never checked, adjusted or deleted again.
	void ForgetZonesOnFullRecalculation(SCStudyInterfaceRef sc, StudyState& state)
	{
		if (!sc.IsFullRecalculation)
			return;
		for (auto& entry : state.Zones)
		{
			entry.second.LineNumber	= 0;
			entry.second.Signature	= 0;
		}
		state.ZonesKey = 0;
	}

	void DeleteZones(SCStudyInterfaceRef sc, StudyState& state)
	{
		ForgetZonesOnFullRecalculation(sc, state);
		for (const auto& entry : state.Zones)
			if (entry.second.LineNumber != 0)
				sc.DeleteACSChartDrawing(sc.ChartNumber, TOOL_DELETE_CHARTDRAWING, entry.second.LineNumber);
		state.Zones.clear();
		state.ZonesKey = 0;
	}

	// The gap shading: transparent Rectangle Highlight drawings, since the drawing callback
	// can't draw transparency and the bars must show through (NinjaTrader paints the zones at
	// 20 % and 10 % opacity), drawn underneath the bars (ZONES_UNDER_BARS). A drawing is sent to
	// Sierra Chart only when its gap changed, and nothing at all is done while nothing visible
	// changes.
	void UpdateZones(SCStudyInterfaceRef sc, StudyState& state)
	{
		ForgetZonesOnFullRecalculation(sc, state);
		if (sc.HideStudy || !state.Built || !sc.Input[IN_SHOW_ZONES].GetYesNo())
		{
			DeleteZones(sc, state);
			return;
		}

		const ZoneStyle style	= ReadZoneStyle(sc);
		const bool hideFilled	= sc.Input[IN_HIDE_FILLED].GetYesNo() != 0;
		const int maximum		= (std::max)(0, sc.Input[IN_MAX_VISIBLE].GetInt());
		const GapEngine& engine	= state.Engine;

		// With a maximum, which gaps show depends on the visible bars too.
		const int settings[] = {style.Extend, style.Shrink, style.ShowTouched, hideFilled, (int)style.UpColor, (int)style.DownColor,
			(int)style.FilledColor, style.GapOpacity, style.FilledOpacity, maximum, maximum > 0 ? sc.IndexOfFirstVisibleBar : 0,
			maximum > 0 ? sc.IndexOfLastVisibleBar : 0, sc.ChartNumber, sc.GraphRegion};
		uint32_t key = Fnv1a(engine.Signature(), settings, sizeof(settings));
		if (key == 0)
			key = 1;
		if (key == state.ZonesKey)
			return;

		// Without a maximum every candidate gets its drawing: off-screen ones cost nothing,
		// and the shading needs no study call when the chart scrolls.
		std::vector<int> ordinals;
		if (maximum > 0)
			ordinals = engine.Snapshot(sc.IndexOfFirstVisibleBar, sc.IndexOfLastVisibleBar, style.Extend, hideFilled, maximum, ZONE_END_BARS).Visible;
		else if (hideFilled)
			ordinals = engine.Active;
		else
			for (int k = 0; k < (int)engine.History.size(); k++)
				ordinals.push_back(k);

		for (auto& entry : state.Zones)
			entry.second.Wanted = false;

		bool complete = true;
		const int stored = (int)engine.History.size();
		for (int ordinal : ordinals)  // oldest first, so a newer zone is drawn over an older one
			for (const ZonePart& part : ZoneParts(engine.History[(size_t)ordinal], stored, engine.CurrentBar, style))
			{
				ZoneSlot& slot	= state.Zones[ordinal * 3 + part.Kind];
				slot.Wanted		= true;

				const uint32_t signature = PartSignature(part);
				if (slot.LineNumber != 0 && slot.Signature != signature && sc.ChartDrawingExists(sc.ChartNumber, slot.LineNumber) == 0)
					slot.LineNumber = 0;  // gone: add it again
				if (slot.LineNumber != 0 && slot.Signature == signature)
					continue;

				s_UseTool tool;
				tool.Clear();
				tool.ChartNumber				= sc.ChartNumber;
				tool.DrawingType				= DRAWING_RECTANGLEHIGHLIGHT;
				tool.AddMethod					= UTAM_ADD_OR_ADJUST;
				if (slot.LineNumber != 0)
					tool.LineNumber				= slot.LineNumber;
				tool.Region						= sc.GraphRegion;
				tool.BeginIndex					= part.BeginBar;
				tool.EndIndex					= ZoneEndIndex(part);  // two bars at least, fixed while extended
				tool.BeginValue					= (float)part.Top;
				tool.EndValue					= (float)part.Bottom;
				tool.Color						= part.Color;
				tool.SecondaryColor				= part.Color;
				tool.LineWidth					= 0;  // the outline is drawn in the callback, as NinjaTrader's
				tool.TransparencyLevel			= part.Transparency;
				tool.ExtendLeft					= 0;
				tool.ExtendRight				= part.ExtendRight ? 1 : 0;
				tool.DrawUnderneathMainGraph	= ZONES_UNDER_BARS ? 1 : 0;  // under the callback's labels and table
				tool.AddAsUserDrawnDrawing		= 0;
				if (sc.UseTool(tool) > 0)
				{
					slot.LineNumber	= tool.LineNumber;
					slot.Signature	= signature;
				}
				else
				{
					slot.Signature	= 0;
					complete		= false;  // try again on the next call
				}
			}

		for (auto it = state.Zones.begin(); it != state.Zones.end();)
		{
			if (it->second.Wanted)
			{
				++it;
				continue;
			}
			if (it->second.LineNumber != 0)
				sc.DeleteACSChartDrawing(sc.ChartNumber, TOOL_DELETE_CHARTDRAWING, it->second.LineNumber);
			it = state.Zones.erase(it);
		}
		state.ZonesKey = complete ? key : 0;
	}

	// ---- Drawing callback ----

	// The chart region in pixels, the DIP scale and the chart background.
	struct Canvas
	{
		int			Left		= 0;
		int			Top			= 0;
		int			Right		= 0;
		int			Bottom		= 0;
		int			FirstBar	= 0;
		int			LastBar		= 0;
		double		Scale		= 1;
		uint32_t	Background	= 0;

		int Dip(double dips) const { return (int)std::floor(dips * Scale + 0.5); }
		int Stroke(double dips) const { return (std::max)(1, Dip(dips)); }
	};

	struct DrawSettings
	{
		ZoneStyle	Style;
		bool		HideFilled		= true;
		bool		ShowZones		= true;
		bool		ShowLines		= true;
		bool		ShowLabels		= true;
		bool		ShowTable		= true;
		int			MaxVisible		= 0;
		int			LineStyle		= LS_DASHED;
		int			LineWidth		= 1;
		int			LabelPoints		= 9;
		int			TablePoints		= 10;
		int			TablePosition	= TP_TOP_RIGHT;
	};

	DrawSettings ReadDrawSettings(SCStudyInterfaceRef sc)
	{
		DrawSettings d;
		d.Style			= ReadZoneStyle(sc);
		d.HideFilled	= sc.Input[IN_HIDE_FILLED].GetYesNo() != 0;
		d.ShowZones		= sc.Input[IN_SHOW_ZONES].GetYesNo() != 0;
		d.ShowLines		= sc.Input[IN_SHOW_LINES].GetYesNo() != 0;
		d.ShowLabels	= sc.Input[IN_SHOW_LABELS].GetYesNo() != 0;
		d.ShowTable		= sc.Input[IN_SHOW_TABLE].GetYesNo() != 0;
		d.MaxVisible	= (std::max)(0, sc.Input[IN_MAX_VISIBLE].GetInt());
		d.LineStyle		= (std::min)((int)sc.Input[IN_LINE_STYLE].GetIndex(), (int)LS_DOTTED);
		d.LineWidth		= (std::max)(1, (std::min)(4, sc.Input[IN_LINE_WIDTH].GetInt()));
		d.LabelPoints	= (std::max)(6, (std::min)(27, sc.Input[IN_LABEL_FONT].GetInt()));
		d.TablePoints	= (std::max)(6, (std::min)(18, sc.Input[IN_TABLE_FONT].GetInt()));
		d.TablePosition	= (std::min)((int)sc.Input[IN_TABLE_POSITION].GetIndex(), (int)TP_MIDDLE_LEFT);
		return d;
	}

	// NinjaTrader's Segoe UI; its DIP sizes are given here in points (x 0.75).
	n_ACSIL::s_GraphicsFont SegoeFont(int points)
	{
		n_ACSIL::s_GraphicsFont font;
		font.m_FaceName	= "Segoe UI";
		font.m_Height	= points;
		font.m_Weight	= FW_NORMAL;
		return font;
	}

	int LineHeight(SCStudyInterfaceRef sc, const n_ACSIL::s_GraphicsFont& font)
	{
		return (std::max)(1, (std::max)(MeasureLine(sc, font, "Ag").Height, (int)sc.Graphics.GetTextHeight()));
	}

	int PriceY(SCStudyInterfaceRef sc, double price)
	{
		return sc.RegionValueToYPixelCoordinate((float)price, sc.GraphRegion);
	}

	// A bar's center; past the last loaded bar (the right-side fill space), one bar spacing
	// per bar.
	int BarX(SCStudyInterfaceRef sc, int index)
	{
		const int last = sc.ArraySize - 1;
		if (index <= last || last < 0)
			return sc.BarIndexToXPixelCoordinate(index);
		const int x		= sc.BarIndexToXPixelCoordinate(last);
		const int step	= last > 0 ? x - sc.BarIndexToXPixelCoordinate(last - 1) : (int)sc.ChartBarSpacing;
		return x + (index - last) * (std::max)(1, step);
	}

	// The zone's left side at its first bar and right side after its last bar, as its
	// Rectangle Highlight (ZONE_END_BARS, ZONE_EDGE_OFFSET).
	int ZoneLeft(SCStudyInterfaceRef sc, const Canvas& c, int firstBar)
	{
		return firstBar < c.FirstBar ? c.Left : (std::max)(c.Left, BarX(sc, firstBar) - ZONE_EDGE_OFFSET);
	}

	int ZoneRight(SCStudyInterfaceRef sc, const Canvas& c, int lastBar)
	{
		return lastBar > c.LastBar ? c.Right : (std::min)(c.Right, BarX(sc, lastBar + ZONE_END_BARS) + ZONE_EDGE_OFFSET);
	}

	void DrawLines(SCStudyInterfaceRef sc, const std::vector<std::string>& lines, int x, int y, int lineHeight, uint32_t color)
	{
		sc.Graphics.SetTextColor(GraphicsColor(color));
		for (size_t i = 0; i < lines.size(); i++)
			if (!lines[i].empty())
				sc.Graphics.DrawTextAt(SCString(lines[i].c_str()), x, y + (int)i * lineHeight);
	}

	// The outline's thickness and the pixel rows of a zone between two prices, clipped to the panel.
	struct ZoneRows
	{
		int		High	= 0;	// first row
		int		Low		= 0;	// one past the last row
		bool	Empty	= true;
	};

	ZoneRows RowsOf(SCStudyInterfaceRef sc, const Canvas& c, double top, double bottom)
	{
		const int y1 = PriceY(sc, top);
		const int y2 = PriceY(sc, bottom);
		ZoneRows rows;
		rows.High	= (std::max)(c.Top, (std::min)(y1, y2));
		rows.Low	= (std::min)(c.Bottom, (std::max)(y1, y2));
		rows.Empty	= rows.Low <= rows.High;
		return rows;
	}

	// NinjaTrader's 1-DIP zone border at min(0.7, opacity x fade + 0.25), drawn inside the
	// zone, over the zone's fill (fillOpacity, see OverZone). A side on the panel edge gets
	// half the strength: NinjaTrader's stroke is centered on the edge and the panel clip cuts
	// off its outer half.
	void DrawZoneOutline(SCStudyInterfaceRef sc, const Canvas& c, int left, int right, const ZoneRows& rows, uint32_t color, double alpha,
		double fillOpacity)
	{
		if (rows.Empty || right <= left)
			return;
		const int t			= c.Stroke(1);
		const int high		= rows.High;
		const int low		= rows.Low;
		const uint32_t full	= OverZone(color, alpha, fillOpacity, c.Background, CALLBACK_PAINTS_OVER_ZONES);
		const uint32_t half	= OverZone(color, alpha / 2, fillOpacity, c.Background, CALLBACK_PAINTS_OVER_ZONES);
		FillRect(sc, left, high, right, high + t, high <= c.Top ? half : full);
		FillRect(sc, left, low - t, right, low, low >= c.Bottom ? half : full);
		FillRect(sc, left, high + t, left + t, low - t, left <= c.Left ? half : full);
		FillRect(sc, right - t, high + t, right, low - t, right >= c.Right ? half : full);
	}

	void DrawGap(SCStudyInterfaceRef sc, const Canvas& c, const DrawSettings& d, const GapFrame& frame, const GapRecord& gap,
		const n_ACSIL::s_GraphicsFont& labelFont, int labelLineHeight, const PriceFormatter& price)
	{
		const bool extends	= d.Style.Extend && !gap.Filled();
		const int endBar	= gap.DrawingEndBar(frame.CurrentBar, d.Style.Extend);
		// The zone's right side is the next bar's center (ZONE_END_BARS), as its drawing's, so a
		// zone that ends the bar before the first visible one still shows half a bar, outlined.
		if ((endBar + ZONE_END_BARS < c.FirstBar && !extends) || gap.StartBar > c.LastBar)
			return;
		const int left		= ZoneLeft(sc, c, gap.StartBar);
		const int right		= extends ? c.Right : ZoneRight(sc, c, endBar);
		const int fade		= FadePercent(frame.StoredCount - 1 - gap.Ordinal);
		const bool up		= gap.Direction > 0;
		const uint32_t activeColor = gap.Filled() ? d.Style.FilledColor : up ? d.Style.UpColor : d.Style.DownColor;

		// The fills are Sierra Chart drawings (UpdateZones); their outlines are drawn here,
		// never around the touched part. The outlined part (the whole zone, or its remaining
		// part) is the one whose edge is the fill target.
		const int t = c.Stroke(1);
		bool outlined = false;
		double edgeAlpha = 0, edgeFill = 0;
		if (d.ShowZones)
			for (const ZonePart& part : ZoneParts(gap, frame.StoredCount, frame.CurrentBar, d.Style))
				if (part.Outline)
				{
					const ZoneRows rows			= RowsOf(sc, c, part.Top, part.Bottom);
					const double alpha			= OutlineAlpha(part.Opacity, fade);
					const double fillOpacity	= part.Opacity / 100.0 * (fade / 100.0);
					DrawZoneOutline(sc, c, left, right, rows, part.Color, alpha, fillOpacity);
					outlined	= !rows.Empty && right > left;
					edgeAlpha	= (up ? rows.Low >= c.Bottom : rows.High <= c.Top) ? alpha / 2 : alpha;
					edgeFill	= fillOpacity;
				}

		if (d.ShowLines)
		{
			const int y = PriceY(sc, gap.SettlePrice);
			if (y >= c.Top && y <= c.Bottom)
			{
				// The line lies on the zone's fill-target edge, inside the zone like the outline:
				// rows above the zone's bottom for an up gap, below its top for a down gap. So it
				// covers the outline's side there in both directions, as NinjaTrader's line and
				// outline, both centered on that edge, coincide. Where it covers the outline it
				// is painted over it, as NinjaTrader paints it.
				const int width			= c.Stroke(d.LineWidth);
				const int top			= up ? y - width : y;
				const double alpha		= 0.75 * fade / 100.0;
				DrawHorizontalLine(sc, left, right, top, top + width, width, d.LineStyle,
					OverZone(activeColor, alpha, edgeFill, c.Background, CALLBACK_PAINTS_OVER_ZONES));
				if (outlined)
				{
					const int edgeTop = up ? y - t : y;
					DrawHorizontalLine(sc, left, right, (std::max)(top, edgeTop), (std::min)(top + width, edgeTop + t), width, d.LineStyle,
						OverZone(activeColor, 1.0 - (1.0 - alpha) * (1.0 - edgeAlpha), edgeFill, c.Background, CALLBACK_PAINTS_OVER_ZONES));
				}
			}
		}

		// Labels stay at the gap origin; old extended zones do not pile labels at the left edge.
		if (!d.ShowLabels || gap.StartBar < c.FirstBar || gap.StartBar > c.LastBar)
			return;
		const int anchorY = PriceY(sc, gap.OpenPrice);
		if (anchorY < c.Top || anchorY > c.Bottom)
			return;

		// NinjaTrader lays the label out 240 DIPs wide; only large fonts wrap.
		const TextMeasure measure = [&sc, &labelFont](const std::string& text) { return MeasureLine(sc, labelFont, text).Width; };
		std::vector<std::string> lines;
		int width = 0;
		for (const std::string& line : LabelLines(gap, price))
			for (const std::string& wrapped : WrapWords(line, c.Dip(240), measure))
			{
				lines.push_back(wrapped);
				width = (std::max)(width, measure(wrapped));
			}
		const int height = labelLineHeight * (int)lines.size();
		int y = gap.Direction > 0 ? anchorY - height - c.Dip(5) : anchorY + c.Dip(5);
		y = (std::max)(c.Top, (std::min)(c.Bottom - height - c.Dip(4), y));
		const int x = (std::max)(c.Left, (std::min)(left, c.Right - width - c.Dip(8)));
		FillRect(sc, x, y, x + width + c.Dip(8), y + height + c.Dip(4), Blend(RGB(0, 0, 0), 0.70, c.Background));
		DrawLines(sc, lines, x + c.Dip(4), y + c.Dip(2), labelLineHeight, activeColor);
	}

	void DrawRectOutline(SCStudyInterfaceRef sc, int left, int top, int right, int bottom, int thickness, uint32_t color)
	{
		FillRect(sc, left, top, right, top + thickness, color);
		FillRect(sc, left, bottom - thickness, right, bottom, color);
		FillRect(sc, left, top + thickness, left + thickness, bottom - thickness, color);
		FillRect(sc, right - thickness, top + thickness, right, bottom - thickness, color);
	}

	// NinjaTrader's table: keys left, values right-aligned, black at 83 %, a 1-DIP border
	// in the Filled color at 60 %. Call after SetTextFont(font).
	void DrawTable(SCStudyInterfaceRef sc, const Canvas& c, const DrawSettings& d, const GapEngine& engine, const GapFrame& frame,
		const n_ACSIL::s_GraphicsFont& font, const PriceFormatter& price)
	{
		const std::vector<TableRow> rows = TableRows(engine, frame, price, d.Style.UpColor, d.Style.DownColor);
		int keyWidth = 0, valueWidth = 0;
		std::vector<int> valueWidths;
		for (const TableRow& row : rows)
		{
			keyWidth = (std::max)(keyWidth, MeasureLine(sc, font, row.Key).Width);
			valueWidths.push_back(MeasureLine(sc, font, row.Value).Width);
			valueWidth = (std::max)(valueWidth, valueWidths.back());
		}

		const int fontDips	= (int)std::floor(d.TablePoints / 0.75 + 0.5);
		const int width		= (std::min)(c.Right - c.Left - c.Dip(16), keyWidth + valueWidth + c.Dip(36));
		const int rowHeight	= (std::max)(c.Dip(fontDips + 9), LineHeight(sc, font));
		const int height	= rowHeight * (int)rows.size() + c.Dip(12);
		int x = 0, y = 0;
		TableOrigin(d.TablePosition, c.Left, c.Top, c.Right, c.Bottom, width, height, c.Dip(8), c.Dip(20), c.Dip(2), x, y);

		const uint32_t background = Blend(RGB(0, 0, 0), 0.83, c.Background);
		FillRect(sc, x, y, x + width, y + height, background);
		DrawRectOutline(sc, x, y, x + width, y + height, c.Stroke(1), Blend(d.Style.FilledColor, 0.60, background));

		for (size_t r = 0; r < rows.size(); r++)
		{
			const int rowY = y + c.Dip(6) + (int)r * rowHeight;
			sc.Graphics.SetTextColor(GraphicsColor(COLOR_WHITE_SMOKE));
			sc.Graphics.DrawTextAt(SCString(rows[r].Key.c_str()), x + c.Dip(10), rowY);
			sc.Graphics.SetTextColor(GraphicsColor(rows[r].ValueColor));
			sc.Graphics.DrawTextAt(SCString(rows[r].Value.c_str()), x + width - c.Dip(10) - valueWidths[r], rowY);
		}
	}

	// A configuration error replaces everything: the study name and the message in Goldenrod.
	void DrawMessage(SCStudyInterfaceRef sc, const Canvas& c, const n_ACSIL::s_GraphicsFont& font, const std::string& message)
	{
		const TextMeasure measure = [&sc, &font](const std::string& text) { return MeasureLine(sc, font, text).Width; };
		const int maxWidth = (std::max)(1, c.Right - c.Left - c.Dip(24));
		std::vector<std::string> lines = WrapWords("Tatanka Gap Analysis", maxWidth, measure);
		for (const std::string& line : WrapWords(message, maxWidth, measure))
			lines.push_back(line);
		DrawLines(sc, lines, c.Left + c.Dip(12), c.Top + c.Dip(20), LineHeight(sc, font), COLOR_GOLDENROD);
	}

	void DrawGapAnalysis(HWND, HDC, SCStudyInterfaceRef sc)
	{
		const StudyState* state = PeekState(sc);
		if (sc.HideStudy || state == nullptr || !sc.Input[IN_ENABLED].GetYesNo())
			return;

		Canvas c;
		c.Left		= sc.StudyRegionLeftCoordinate;
		c.Top		= sc.StudyRegionTopCoordinate;
		c.Right		= sc.StudyRegionRightCoordinate;
		c.Bottom	= sc.StudyRegionBottomCoordinate;
		c.FirstBar	= sc.IndexOfFirstVisibleBar;
		c.LastBar	= sc.IndexOfLastVisibleBar;
		if (c.Right <= c.Left || c.Bottom <= c.Top)
			return;

		const DrawSettings d = ReadDrawSettings(sc);
		const n_ACSIL::s_GraphicsFont tableFont = SegoeFont(d.TablePoints);
		const n_ACSIL::s_GraphicsFont labelFont = SegoeFont(d.LabelPoints);
		sc.Graphics.SetTextFont(tableFont);  // before any measuring: see MeasureLine
		c.Scale = DipScale(sc, tableFont);

		// NinjaTrader draws nothing on a panel smaller than 40 x 40 DIPs.
		if (c.Right - c.Left >= 40 * c.Scale && c.Bottom - c.Top >= 40 * c.Scale)
		{
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
			const PriceFormatter price = [&sc](double value) { return std::string(sc.FormatGraphValue(value, sc.BaseGraphValueFormat).GetChars()); };

			if (!state->Error.empty())
				DrawMessage(sc, c, tableFont, state->Error);
			else if (state->Built)
			{
				// Oldest to newest, so the newest gap is painted last.
				const GapFrame frame = state->Engine.Snapshot(c.FirstBar, c.LastBar, d.Style.Extend, d.HideFilled, d.MaxVisible, ZONE_END_BARS);
				if (d.ShowZones || d.ShowLines || d.ShowLabels)
				{
					sc.Graphics.SetTextFont(labelFont);
					const int labelLineHeight = LineHeight(sc, labelFont);
					for (int ordinal : frame.Visible)
						DrawGap(sc, c, d, frame, state->Engine.History[(size_t)ordinal], labelFont, labelLineHeight, price);
				}
				if (d.ShowTable)
				{
					sc.Graphics.SetTextFont(tableFont);
					DrawTable(sc, c, d, state->Engine, frame, tableFont, price);
				}
			}

			sc.Graphics.ResetTextAlign();
			sc.Graphics.ResetBackgroundMode();
			sc.Graphics.ResetTextColor();
			sc.Graphics.ResetClippingRegion();
		}
		sc.Graphics.ResetTextFont();
	}
}

SCSFExport scsf_TatankaGapAnalysis(SCStudyInterfaceRef sc)
{
	if (sc.SetDefaults)
	{
		sc.GraphName		= "Tatanka Gap Analysis";
		sc.StudyDescription	= "Tatanka Gap Analysis v1.0.0: RTH opening gaps with partial fills, optional right extension, "
							  "and all loaded chart history. Use Minute or Second bars. Free and open source (MPL 2.0). tatankatrading.com";
		sc.GraphRegion		= 0;
		sc.AutoLoop			= 0;
		sc.ValueFormat		= VALUEFORMAT_INHERITED;
		sc.ScaleRangeType	= SCALE_SAMEASREGION;
		sc.DisplayStudyInputValues				= 0;
		sc.DrawStudyUnderneathMainPriceGraph	= 0;  // over the bars, as NinjaTrader renders

		sc.Input[IN_ENABLED].Name = "Enable gap analysis";
		sc.Input[IN_ENABLED].SetYesNo(1);

		sc.Input[IN_RTH_START].Name = "RTH start (Chicago)";
		sc.Input[IN_RTH_START].SetTime(30600);
		sc.Input[IN_RTH_START].SetDescription("Chicago time, including daylight saving time. Default 08:30:00.");

		sc.Input[IN_RTH_END].Name = "RTH end (Chicago)";
		sc.Input[IN_RTH_END].SetTime(54000);
		sc.Input[IN_RTH_END].SetDescription("Default 15:00:00. Reference price is the last loaded RTH chart-bar close.");

		sc.Input[IN_MIN_GAP].Name = "Minimum gap size (points)";
		sc.Input[IN_MIN_GAP].SetDouble(0);
		sc.Input[IN_MIN_GAP].SetDoubleLimits(0, 1e9);

		sc.Input[IN_MAX_VISIBLE].Name = "Maximum visible gaps (0 = all)";
		sc.Input[IN_MAX_VISIBLE].SetInt(0);
		sc.Input[IN_MAX_VISIBLE].SetIntLimits(0, INT_MAX);
		sc.Input[IN_MAX_VISIBLE].SetDescription("Zero displays all eligible gaps intersecting the visible time range. "
			"All loaded gaps remain tracked regardless of this display setting.");

		sc.Input[IN_EXTEND_RIGHT].Name = "Extend unfilled gaps right";
		sc.Input[IN_EXTEND_RIGHT].SetYesNo(1);

		sc.Input[IN_SHOW_ZONES].Name = "Show gap shading";
		sc.Input[IN_SHOW_ZONES].SetYesNo(1);

		sc.Input[IN_SHRINK].Name = "Shrink partially filled zones";
		sc.Input[IN_SHRINK].SetYesNo(1);
		sc.Input[IN_SHRINK].SetDescription("Wicks reduce the unfilled area. Filled portions never grow back when price retreats.");

		sc.Input[IN_SHOW_TOUCHED].Name = "Show partially filled area";
		sc.Input[IN_SHOW_TOUCHED].SetYesNo(1);
		sc.Input[IN_SHOW_TOUCHED].SetDescription("Shade the touched portion separately. Applies when shrinking is enabled.");

		sc.Input[IN_HIDE_FILLED].Name = "Hide fully filled gaps";
		sc.Input[IN_HIDE_FILLED].SetYesNo(1);

		sc.Input[IN_SHOW_LINES].Name = "Show RTH close target lines";
		sc.Input[IN_SHOW_LINES].SetYesNo(1);

		sc.Input[IN_LINE_STYLE].Name = "Target line style";
		sc.Input[IN_LINE_STYLE].SetCustomInputStrings("Solid;Dashed;Dotted");
		sc.Input[IN_LINE_STYLE].SetCustomInputIndex(LS_DASHED);

		sc.Input[IN_LINE_WIDTH].Name = "Target line width";
		sc.Input[IN_LINE_WIDTH].SetInt(1);
		sc.Input[IN_LINE_WIDTH].SetIntLimits(1, 4);

		sc.Input[IN_SHOW_LABELS].Name = "Show gap labels";
		sc.Input[IN_SHOW_LABELS].SetYesNo(1);

		sc.Input[IN_LABEL_FONT].Name = "Label font size";
		sc.Input[IN_LABEL_FONT].SetInt(9);
		sc.Input[IN_LABEL_FONT].SetIntLimits(6, 27);
		sc.Input[IN_LABEL_FONT].SetDescription("Points. NinjaTrader's 12 DIPs = 9 points.");

		sc.Input[IN_GAP_OPACITY].Name = "Unfilled zone opacity (%)";
		sc.Input[IN_GAP_OPACITY].SetInt(20);
		sc.Input[IN_GAP_OPACITY].SetIntLimits(0, 100);
		sc.Input[IN_GAP_OPACITY].SetDescription("100 = solid.");

		sc.Input[IN_FILLED_OPACITY].Name = "Filled area opacity (%)";
		sc.Input[IN_FILLED_OPACITY].SetInt(10);
		sc.Input[IN_FILLED_OPACITY].SetIntLimits(0, 100);
		sc.Input[IN_FILLED_OPACITY].SetDescription("100 = solid.");

		sc.Input[IN_UP_COLOR].Name = "Up gap color";
		sc.Input[IN_UP_COLOR].SetColor(RGB(50, 205, 50));		// LimeGreen

		sc.Input[IN_DOWN_COLOR].Name = "Down gap color";
		sc.Input[IN_DOWN_COLOR].SetColor(RGB(205, 92, 92));		// IndianRed

		sc.Input[IN_FILLED_COLOR].Name = "Filled gap color";
		sc.Input[IN_FILLED_COLOR].SetColor(RGB(112, 128, 144));	// SlateGray

		sc.Input[IN_SHOW_TABLE].Name = "Show gap table";
		sc.Input[IN_SHOW_TABLE].SetYesNo(1);

		sc.Input[IN_TABLE_POSITION].Name = "Table position";
		sc.Input[IN_TABLE_POSITION].SetCustomInputStrings("Top Right;Top Left;Bottom Right;Bottom Left;Middle Right;Middle Left");
		sc.Input[IN_TABLE_POSITION].SetCustomInputIndex(TP_TOP_RIGHT);

		sc.Input[IN_TABLE_FONT].Name = "Table font size";
		sc.Input[IN_TABLE_FONT].SetInt(10);
		sc.Input[IN_TABLE_FONT].SetIntLimits(6, 18);
		sc.Input[IN_TABLE_FONT].SetDescription("Points. NinjaTrader's 13 DIPs = about 10 points.");

		sc.Input[IN_ALERT_NEW].Name = "Alert on new gap";
		sc.Input[IN_ALERT_NEW].SetYesNo(1);
		sc.Input[IN_ALERT_NEW].SetDescription("Real-time alerts only. Historical gaps do not replay alerts.");

		sc.Input[IN_ALERT_FILL].Name = "Alert on full gap fill";
		sc.Input[IN_ALERT_FILL].SetYesNo(1);

		sc.Input[IN_ALERT_SOUND].Name = "Alert sound";
		sc.Input[IN_ALERT_SOUND].SetAlertSoundNumber(2);	// Alert Sound 1
		sc.Input[IN_ALERT_SOUND].SetDescription("Sierra Chart alert sound (set up in Global Settings). "
			"No Sound = an Alerts Log entry only (a visual alert).");

		sc.Input[IN_ALERT_SOUND_FILE].Name = "Alert sound file";
		sc.Input[IN_ALERT_SOUND_FILE].SetString("");
		sc.Input[IN_ALERT_SOUND_FILE].SetDescription("Optional. A WAV file in Sierra Chart's AlertSounds folder, or a full path. "
			"Plays instead of the Alert sound. Blank uses the Alert sound.");

		return;
	}

	if (sc.LastCallToFunction)
	{
		// The study is removed (or the chart closed): its drawings and its state go with it.
		if (StudyState* state = PeekState(sc))
			DeleteZones(sc, *state);
		DeleteState(sc);
		return;
	}

	// Set on every call, after SetDefaults, so it survives a DLL reload.
	sc.p_GDIFunction = DrawGapAnalysis;

	// With a maximum, the selection depends on the visible bars, so follow scrolling.
	sc.UpdateAlways = sc.Input[IN_MAX_VISIBLE].GetInt() > 0 ? 1 : 0;

	StudyState& state = GetState(sc);
	if (!sc.Input[IN_ENABLED].GetYesNo())
	{
		state.ResetEngine();
		state.Error.clear();
		DeleteZones(sc, state);
		return;
	}

	const int rthStart	= sc.Input[IN_RTH_START].GetTime();
	const int rthEnd	= sc.Input[IN_RTH_END].GetTime();
	n_ACSIL::s_BarPeriod barPeriod;
	sc.GetBarPeriodParameters(barPeriod);
	state.Error = ConfigError(rthStart, rthEnd,
		SupportedBars(barPeriod.ChartDataType, barPeriod.IntradayChartBarPeriodType, sc.SecondsPerBar));
	if (!state.Error.empty())
	{
		state.ResetEngine();
		DeleteZones(sc, state);
		return;
	}

	// Hidden (sc.HideStudy) still tracks gaps and alerts, as NinjaTrader's Visible = false;
	// UpdateZones then removes the shading and the callback draws nothing.
	ProcessBars(sc, state, rthStart, rthEnd);
	UpdateZones(sc, state);
}

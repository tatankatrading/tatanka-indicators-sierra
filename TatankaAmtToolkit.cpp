// Copyright (c) 2026 Tatanka Trading LLC.
// This Source Code Form is subject to the Mozilla Public License, v. 2.0.
// If a copy of the MPL was not distributed with this file, obtain one at https://mozilla.org/MPL/2.0/.
// Tatanka AMT Toolkit v1.0.0 for Sierra Chart - tatankatrading.com
// Sierra Chart port of the NinjaTrader 8 "Tatanka AMT Toolkit" (chart label "Tatanka AMT").
//
// The whole toolkit, built in four stages (amt_parity_spec.md section 0.4). Stage 1: the developing
// volume profile (session, week, month or year) with its POC/VAH/VAL lines, the completed profiles
// and the walls; the prior day's value (pdPOC/pdVAH/pdVAL); the prior month's value (pmPOC/pmVAH/pmVAL); the RTH VWAP; the
// daily ATR; the dashboard frame; price-scale tags; Force on Top; Hide All Labels; the session-time
// warning; the alert pipeline. Stage 2 (the auction read): the overnight high/low; the previous
// day's high/low/open with the 15:00 roll and its history; the initial balance; the settlement and
// the overnight inventory with trap detection; the RTH open, the open location and the gap test; the
// Dalton day type; the 80% Rule and its fill; the late spike; the dashboard's DAY TYPE, OVN
// INVENTORY, OPEN and 80% RULE rows; their tags and alerts. Stage 3 (unfinished business): the
// daily, weekly and monthly naked POCs with their touch alerts; the TPO single prints (translucent
// ranges) and poor highs/lows; the previous week's and month's high/low; the weekly open and the RTH
// open line (dOpen, archived with each past day); the structure limit; the pwHigh/pwLow and
// pmHigh/pmLow tags; their alerts. Stage 4 (the daily levels): the paste box (NinjaTrader's one-line
// paste line or the labeled block, parsed as .NET parses it), edited in a multi-line editor from the
// chart's right-click menu or pasted from the clipboard; the levels file ({root}, kernel32 reads, the
// last-good cache, a re-read every 5 s while live, the STALE and wrong-symbol checks); the levels'
// lines, zones (translucent ranges), flips and labels; the dashboard's PIVOT row; the level alerts
// (Cross, Zone Entry, Both); and the optional Discord webhook (sc.MakeHTTPPOSTRequest, live alerts
// only). Every input and subgraph has the index Stage 1 gave it.
//
// The engine below (Profile, DailyHistory, Engine.Process, BuildVisuals, the alert tracker) is
// NinjaTrader's (TatankaAmtToolkit.cs, namespace TatankaTrading.AmtToolkit) statement for statement,
// with no Sierra Chart calls, so the tests can include this file and compare it bit for bit with
// NinjaTrader's own code (tests\amt_oracle). Where it differs on purpose, the comment says so.
//
// Times: the engine sees Chicago wall-clock times (CT, seconds since Sierra Chart's base date), as
// NinjaTrader works in CT. Sierra Chart stamps a bar at its START in the chart's time zone; each bar
// is converted to CT once (start and end), and the drawing places CT times on the chart's bars by
// their CT ends (NinjaTrader's GetXByTime on close stamps).
//
// Data: the chart's bars; 1-minute bars from the chart itself on a 1-minute chart, otherwise from a
// hidden 1-minute chart of the same symbol (the one Periodic and Auto Anchored VP use); 30-minute bars
// for the prior month built from those minutes; daily bars from the hidden daily chart that TPO
// Profile and If/Then share. A chart bar is committed to the engine once, when the minutes have
// moved past its end; the forming bar is previewed on a copy of the engine on every study call
// (NinjaTrader's commit / preview).

#include "sierrachart.h"

#include <algorithm>
#include <array>
#include <climits>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <deque>
#include <functional>
#include <limits>
#include <map>
#include <memory>
#include <set>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

SCDLLName("Tatanka AMT Toolkit")

namespace
{
	// ---- Brand (NinjaTrader's AmtBrand, NT:36-42) ----

	const char* const BRAND_SHORT	= "Tatanka AMT";
	const char* const BRAND_VERSION	= "1.0.0";
	const char* const BRAND_SITE	= "tatankatrading.com";

	// ---- Palette (NinjaTrader's AmtPalette, NT:46-54): ARGB, TradingView's named colors ----

	enum Palette : uint32_t
	{
		PAL_RED			= 0xFFF23645u,
		PAL_GREEN		= 0xFF4CAF50u,
		PAL_LIME		= 0xFF00E676u,
		PAL_YELLOW		= 0xFFFDD835u,
		PAL_ORANGE		= 0xFFFF9800u,
		PAL_GRAY		= 0xFF787B86u,
		PAL_BLUE		= 0xFF2196F3u,
		PAL_PURPLE		= 0xFF9C27B0u,
		PAL_MAROON		= 0xFF880E4Fu,
		PAL_AQUA		= 0xFF00BCD4u,
		PAL_WHITE		= 0xFFFFFFFFu,
		PAL_ALERT_RED	= 0xFFFF1744u,
		PAL_PINK		= 0xFFEA80FCu,
		PAL_GREEN_SOFT	= 0xB34CAF50u,	// color.new(green, 30): 70% opaque
		PAL_RED_SOFT	= 0xB3F23645u
	};

	// ---- Inputs (spec A.2): index = enum value, final from Stage 1. Never renumber. ----

	enum InputIndex
	{
		IN_ROW_SCALE,				// 0  1. Global
		IN_MANUAL_TICK,
		IN_FORCE_ON_TOP,
		IN_HIDE_ALL_LABELS,
		IN_SHOW_TAGS,
		IN_TZ_GUARD,
		IN_LEVELS_FILE,				// 6  2. Levels (Stage 4)
		IN_LEVELS_TEXT,
		IN_LVL_FLIP,
		IN_LVL_FLIP_ATR,
		IN_LVL_SHOW_ZONES,
		IN_LVL_ZONE_MODE,
		IN_LVL_ZONE_ATR_PCT,
		IN_LVL_ZONE_TICKS,
		IN_LVL_ZONE_TRANSP,
		IN_LVL_LABELS,
		IN_LVL_LABEL_OFFSET,
		IN_LVL_ALERTS,
		IN_LVL_ALERT_PIVOT,
		IN_LVL_ALERT_RES,
		IN_LVL_ALERT_SUPP,
		IN_PD_USE_RTH,				// 21 3. Prev Day (Stage 2)
		IN_PD_SESSION,
		IN_PD_LABELS,
		IN_PD_LABEL_OFFSET,
		IN_PD_ALERT_HL,
		IN_CC_ENABLE,				// 26 4. Prev Value
		IN_CC_VA_PCT,
		IN_CC_SESSION,
		IN_CC_LABELS,
		IN_CC_LABEL_OFFSET,
		IN_CC_VA_OPACITY,
		IN_CC_FILL_TRANSP,
		IN_CC_ALERT_VA,
		IN_CC_ALERT_80,
		IN_OVN_ENABLE,				// 35 5. OVN (Stage 2)
		IN_OVN_SESSION,
		IN_OVN_DELETE,
		IN_OVN_LABELS,
		IN_OVN_LABEL_OFFSET,
		IN_OVN_ALERT,
		IN_IB_ENABLE,				// 41 6. IB (Stage 2)
		IN_IB_SESSION,
		IN_IB_EXTEND,
		IN_IB_LIMIT_EXT,
		IN_IB_STOP_TIME,
		IN_IB_LABELS,
		IN_IB_LABEL_LOC,
		IN_IB_LABEL_OFFSET,
		IN_IB_ALERT_HIGH,
		IN_IB_ALERT_LOW,
		IN_IB_ALERT_WINDOW,
		IN_VWAP_START,				// 52 7. VWAP
		IN_VWAP_END,
		IN_VWAP_ALERT,
		IN_OPEN_LABELS,				// 55 8. Opens (Stage 3)
		IN_OPEN_LABEL_OFFSET,
		IN_WK_OPEN_LABELS,
		IN_WK_OPEN_LABEL_OFFSET,
		IN_WK_OPEN_ALERT,
		IN_PW_LABELS,				// 60 9. Prev Week (Stage 3)
		IN_PW_LABEL_OFFSET,
		IN_PW_ALERT,
		IN_PM_LABELS,				// 63 10. Prev Month
		IN_PM_LABEL_OFFSET,
		IN_PM_ALERT,
		IN_MVP_ENABLE,				// 66 11. Profile
		IN_MVP_PERIOD,
		IN_MVP_SESSION,
		IN_MVP_SESSION_DURATION,
		IN_MVP_CALC_PRECISION,
		IN_MVP_ROW_SIZE,
		IN_MVP_VA_PCT,
		IN_MVP_WIDTH,
		IN_MVP_ALIGN_RIGHT,
		IN_MVP_OFFSET,
		IN_MVP_VA_TRANSP,
		IN_MVP_OUT_TRANSP,
		IN_MVP_LABELS,
		IN_MVP_ALERTS,
		IN_MVP_ALERT_WINDOW,
		IN_WALL_TRANSP,				// 81 12. Walls
		IN_WALL_EXTEND,
		IN_WALL_SMOOTHING,
		IN_WALL_MIN_DISTANCE,
		IN_WALL_AUTO_SCALE,
		IN_WALL_START_MULT,
		IN_WALL_END_MULT,
		IN_WALL_FIXED_MULT,
		IN_TPO_SESSION,				// 89 13. TPO (Stage 3)
		IN_TPO_MINUTES,
		IN_TPO_TICKS_PER_BLOCK,
		IN_TPO_MIN_SINGLE_TICKS,
		IN_TPO_FILTER_TAILS,
		IN_TPO_MAX_TAIL,
		IN_TPO_MAX_DAYS,
		IN_SP_TRANSP,
		IN_POOR_LABELS,
		IN_NPOC_ENABLE,				// 98 14. nPOC (Stage 3)
		IN_NPOC_BIN,
		IN_NPOC_LABELS,
		IN_NPOC_LABEL_OFFSET,
		IN_NPOC_ALERT,
		IN_INV_ENABLE,				// 103 15. Inventory (Stage 2)
		IN_INV_GLOBEX_START,
		IN_INV_RTH_OPEN,
		IN_INV_LABELS,
		IN_INV_LABEL_OFFSET,
		IN_INV_ALERT,
		IN_SPIKE_WINDOW,			// 109 16. Spike (Stage 2)
		IN_SPIKE_LABELS,
		IN_SPIKE_LABEL_OFFSET,
		IN_SPIKE_ALERT,
		IN_TBL_SHOW,				// 113 17. Dashboard
		IN_TBL_POSITION,
		IN_TBL_TEXT_SIZE,
		IN_TBL_SESSION,
		IN_CONTEXT_SESSION,
		IN_ATR_PERIOD,
		IN_CAP_ENABLE,				// 119 18. Alerts
		IN_CAP_MAX,
		IN_CAP_WINDOW,
		IN_ALERT_MODE,
		IN_ALERT_ZONE_TICKS,
		IN_ALERT_SOUND,
		IN_DISCORD_ENABLE,			// 125 19. Discord (Stage 4)
		IN_DISCORD_URL,
		IN_COUNT					// 127; Sierra Chart's 128th input is kept spare
	};

	// ---- Subgraphs (spec A.3): one per drawn line kind, named with NinjaTrader's name. Final. ----

	enum SubgraphIndex
	{
		SG_PIVOT,			// 0
		SG_RES,
		SG_SUPP,
		SG_LEVEL_ZONE_BORDER,
		SG_PD_HIGH,			// 4  tag
		SG_PD_LOW,			// 5  tag
		SG_PD_OPEN,
		SG_PD_POC,
		SG_PD_VAH,
		SG_PD_VAL,
		SG_FILL80,			// 10
		SG_OVN_HIGH,
		SG_OVN_LOW,
		SG_IB_HIGH,			// 13 tag
		SG_IB_LOW,			// 14 tag
		SG_IB_MID,
		SG_VWAP,			// 16
		SG_DOPEN,
		SG_WK_OPEN,
		SG_PW_HIGH,			// 19 tag
		SG_PW_LOW,			// 20 tag
		SG_PM_VAH,			// 21 tag
		SG_PM_VAL,			// 22 tag
		SG_PM_POC,			// 23 tag
		SG_PM_HIGH,			// 24 tag
		SG_PM_LOW,			// 25 tag
		SG_VA_HIST,			// 26
		SG_OUT_HIST,
		SG_DEV_POC,			// 28 tag
		SG_DEV_VAH,
		SG_DEV_VAL,
		SG_WALL,			// 31
		SG_SP,
		SG_SP_BORDER,
		SG_POOR_HIGH,
		SG_POOR_LOW,
		SG_NPOC_DAILY,		// 36
		SG_NPOC_WEEKLY,
		SG_NPOC_MONTHLY,
		SG_SETTLE,			// 39
		SG_TRAP,
		SG_SPIKE_SUP,		// 41
		SG_SPIKE_RES,
		SG_COUNT			// 43; subgraphs 43-59 are not created
	};

	// Persistent variable keys (spec C.1): fixed now; ints 7-20 reserved.
	enum PersistentPointerKey
	{
		PP_STATE			= 1,
		PP_EDITOR			= 2		// Stage 4: the shared editor
	};

	enum PersistentIntKey
	{
		PI_MINUTE_CHART		= 1,
		PI_DAILY_CHART		= 2,
		PI_EDIT_MENU_ID		= 3,	// Stage 4
		PI_PASTE_MENU_ID	= 4,	// Stage 4
		PI_ERROR_LOGGED		= 5,
		PI_NO_CHART_LOGGED	= 6
	};

	// NinjaTrader Limits (group 20, NT:3513-3518) as constants (spec A.4).
	const int MAX_PROFILE_ROWS		= 100000;
	const int MAX_STRUCTURES		= 2000;
	// NinjaTrader's RenderHistory capacity for samples (NT:1690).
	const size_t MAX_SAMPLES		= 50000;

	const double NaN = std::numeric_limits<double>::quiet_NaN();

	const int64_t US_PER_SECOND		= 1000000;
	const int64_t US_PER_MINUTE		= 60 * US_PER_SECOND;
	const int64_t US_PER_HOUR		= 60 * US_PER_MINUTE;
	const int64_t SECONDS_DAY		= 86400;
	// 1970-01-01 in Sierra Chart's day numbers (days since 1899-12-30).
	const int SIERRA_UNIX_DATE		= 25569;
	// NinjaTrader's DateTime.MinValue: "no date" for date keys, "no time" for times.
	const int NO_DATE				= INT_MIN;
	const int64_t CT_MIN			= INT64_MIN;

	// Every text the study draws or logs (spec B.0.10, A.5), character for character.
	const char* const TEXT_LOADING_TAIL	= " \xE2\x80\x94" " loading chart and secondary history\xE2\x80\xA6";
	const char* const TEXT_NOT_MINUTES	= "Use a standard 1\xE2\x80\x93" "30 minute chart. Tick, volume, range, Renko and daily bars are not supported by this port.";
	const char* const TEXT_NOT_GLOBEX	= "Set Chart Settings > Session Times to the full Globex session (17:00-16:00 CT). Overnight ranges, "
		"full-day profiles and inventory require overnight data.";
	const char* const TEXT_SESSION_WARNING	= "Session fields differ from defaults. All session fields are Central exchange time.";
	const char* const TEXT_NO_MINUTES	= " One-minute data unavailable; using chart-bar profile fallback.";
	const char* const TEXT_NO_MINUTE_CHART_LOG = "Tatanka AMT: Sierra Chart could not open a 1-minute chart of this symbol; profiles use the chart's bars.";

	// ---- Choice lists (NinjaTrader's TatankaAmtToolkitOptions, NT:3520-3567, in their order) ----

	const char* const ROW_SCALES[]		= {"Auto", "1x", "2x", "5x", "10x", "20x", "50x", "100x"};
	const char* const TOP_PICKS[]		= {"Daily Levels (All)", "Profile POC", "Profile VAH", "Profile VAL", "IB Midpoint", "IB High", "IB Low", "pdPOC",
		"Prev Day High", "Prev Day Low", "OVN High", "OVN Low", "Prev Month VAH", "Prev Month VAL", "Spike Base"};
	const char* const LVL_SIZES[]		= {"auto", "tiny", "small", "normal", "large", "huge"};
	const char* const ZONE_MODES[]		= {"ATR %", "Ticks"};
	const char* const SIZES_4[]			= {"Tiny", "Small", "Normal", "Large"};
	const char* const SIZES_5[]			= {"Tiny", "Small", "Normal", "Large", "Huge"};
	const char* const IB_SIZES[]		= {"Auto", "Huge", "Large", "Normal", "Small", "Tiny"};
	const char* const IB_EXTENDS[]		= {"Right", "Left", "Both", "None"};
	const char* const IB_LOCATIONS[]	= {"Left", "Right"};
	const char* const PERIODS[]			= {"Session", "Weekly", "Monthly", "Yearly"};
	const char* const TBL_POSITIONS[]	= {"Top Right", "Top Left", "Bottom Right", "Bottom Left", "Middle Right", "Middle Left"};
	const char* const ALERT_MODES[]		= {"Cross", "Zone Entry", "Both"};

	template <size_t N>
	std::string Choice(const char* const (&list)[N], unsigned index)
	{
		return list[(std::min)((size_t)index, N - 1)];
	}

	// ---- Small helpers (Periodic VP's) ----

	uint32_t Fnv1a(uint32_t hash, const void* data, size_t size)
	{
		const unsigned char* bytes = (const unsigned char*)data;
		for (size_t i = 0; i < size; i++)
			hash = (hash ^ bytes[i]) * 16777619u;
		return hash;
	}

	const uint64_t FNV64_BASIS = 14695981039346656037ull;

	uint64_t Fnv1a64(uint64_t hash, const void* data, size_t size)
	{
		const unsigned char* bytes = (const unsigned char*)data;
		for (size_t i = 0; i < size; i++)
			hash = (hash ^ bytes[i]) * 1099511628211ull;
		return hash;
	}

	uint64_t Fnv1a64Text(uint64_t hash, const std::string& text)
	{
		const uint64_t size = text.size();
		return Fnv1a64(Fnv1a64(hash, &size, sizeof(size)), text.data(), text.size());
	}

	int64_t FloorDiv(int64_t value, int64_t divisor)
	{
		const int64_t quotient = value / divisor;
		return (value % divisor != 0 && (value < 0) != (divisor < 0)) ? quotient - 1 : quotient;
	}

	// Half up: 2.5 -> 3, exact for |x| < 2^52.
	double RoundHalfUp(double x)
	{
		const double f = std::floor(x);
		return x - f >= 0.5 ? f + 1 : f;
	}

	// .NET's Math.Round(x, MidpointRounding.AwayFromZero).
	double RoundHalfAway(double x)
	{
		return x >= 0 ? RoundHalfUp(x) : -RoundHalfUp(-x);
	}

	// .NET Framework's Math.Max / Math.Min (double): NaN wins.
	double MaxNet(double a, double b)
	{
		if (a > b)
			return a;
		if (a != a)
			return a;
		return b;
	}

	double MinNet(double a, double b)
	{
		if (a < b)
			return a;
		if (a != a)
			return a;
		return b;
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

	// Sierra stores prices as floats (GC 2650.1f is 2650.10009765625). Snapped to the tick grid
	// they match NinjaTrader's tick-rounded doubles (spec B.0.1).
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

	// ---- Calendar (Sierra date ints: days since 1899-12-30, a Saturday) ----

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

	// ---- .NET number formats (spec B.0.12) ----

	// .NET Framework's custom formats "0" and "0.00" (decimals 0 or 2), as NinjaTrader's dashboard
	// uses them: the double rounded to 15 significant digits (half away from zero), then half away
	// from zero to the decimals; "0.00" keeps its zeros (keepZeros). Periodic VP's FormatNet.
	std::string FormatNet(double value, int decimals, bool keepZeros)
	{
		if (!(value == value))
			return "NaN";
		char text[64];
		if (!(std::fabs(value) < 1e18))
		{
			snprintf(text, sizeof(text), "%.0f", value);
			return text;
		}
		snprintf(text, sizeof(text), "%.30e", std::fabs(value));
		int digits[16];
		digits[0] = text[0] - '0';
		for (int k = 1; k < 16; k++)
			digits[k] = text[k + 1] - '0';
		const char* exponentText = strchr(text, 'e');
		int exponent = exponentText ? atoi(exponentText + 1) : 0;
		unsigned long long unit = 1;
		for (int k = 0; k < decimals; k++)
			unit *= 10;
		auto zero = [&]()
		{
			if (!keepZeros || decimals == 0)
				return std::string("0");
			snprintf(text, sizeof(text), "0.%0*d", decimals, 0);
			return std::string(text);
		};
		if (digits[0] == 0)
			return zero();
		if (digits[15] >= 5)
		{
			int k = 14;
			while (k >= 0 && digits[k] == 9)
				digits[k--] = 0;
			if (k >= 0)
				digits[k]++;
			else
			{
				digits[0] = 1;
				exponent++;
			}
		}
		const int keep = exponent + 1 + decimals;
		if (keep < 0)
			return zero();
		unsigned long long scaled = 0;
		for (int k = 0; k < keep; k++)
			scaled = scaled * 10 + (unsigned long long)(k < 15 ? digits[k] : 0);
		if (keep < 15 && digits[keep] >= 5)
			scaled++;
		if (scaled == 0)
			return zero();
		const char* sign = value < 0 ? "-" : "";
		unsigned long long fraction = scaled % unit;
		int places = decimals;
		if (!keepZeros)
			while (places > 0 && fraction % 10 == 0 && fraction != 0)
			{
				fraction /= 10;
				places--;
			}
		if (places == 0 || (!keepZeros && fraction == 0))
			snprintf(text, sizeof(text), "%s%llu", sign, scaled / unit);
		else
			snprintf(text, sizeof(text), "%s%llu.%0*llu", sign, scaled / unit, places, fraction);
		return text;
	}

	// ---- .NET TimeSpan (Framework 4.x, NinjaTrader 8's runtime): ticks times the per-tick constant ----

	struct TimeSpanNet
	{
		static double TotalDays(int64_t seconds) { return (double)(seconds * 10000000LL) * (1.0 / 864000000000.0); }
		// The 80% Rule's 60 minutes (NT:757).
		static double TotalMinutes(int64_t seconds) { return (double)(seconds * 10000000LL) * (1.0 / 600000000.0); }
	};

	double TotalDays(int64_t seconds)
	{
		return TimeSpanNet::TotalDays(seconds);
	}

	// ---- Text helpers ----

	// .NET's string.Trim() for the white space these texts can hold.
	std::string Trim(const std::string& text)
	{
		const char* const space = " \t\r\n\v\f";
		const size_t first = text.find_first_not_of(space);
		if (first == std::string::npos)
			return std::string();
		const size_t last = text.find_last_not_of(space);
		return text.substr(first, last - first + 1);
	}

	// The notice box text (NT:1870, NT:2064): the snapshot's warning, then the Discord warnings, each
	// joined with a space and trimmed as NinjaTrader does (so its spacing is NinjaTrader's).
	std::string NoticeText(const std::string& settingsWarning, const std::string& levelsWarning, const std::string& frameWarning,
		const std::string& discordSetupWarning, const std::string& discordWarning)
	{
		const std::string snapshot = Trim(settingsWarning + " " + levelsWarning + " " + frameWarning);
		return Trim(snapshot + " " + discordSetupWarning + " " + discordWarning);
	}

	bool StartsWith(const std::string& text, const char* prefix)
	{
		return text.compare(0, strlen(prefix), prefix) == 0;
	}

	// UTF-16 code units of a UTF-8 text (NinjaTrader's string.Length).
	int Utf16Length(const std::string& text)
	{
		int units = 0;
		for (size_t i = 0; i < text.size(); i++)
		{
			const unsigned char c = (unsigned char)text[i];
			if ((c & 0xC0) == 0x80)
				continue;
			units += c >= 0xF0 ? 2 : 1;
		}
		return units;
	}

	// .NET's int.TryParse(text) with NumberStyles.Integer: optional white space around, an
	// optional sign, decimal digits.
	bool TryParseNetInt(const std::string& text, int& value)
	{
		auto white = [](char c) { return c == ' ' || (c >= '\t' && c <= '\r'); };
		size_t i = 0, n = text.size();
		while (i < n && white(text[i]))
			i++;
		while (n > i && white(text[n - 1]))
			n--;
		bool negative = false;
		if (i < n && (text[i] == '+' || text[i] == '-'))
		{
			negative = text[i] == '-';
			i++;
		}
		if (i >= n)
			return false;
		long long v = 0;
		for (; i < n; i++)
		{
			if (text[i] < '0' || text[i] > '9')
				return false;
			v = v * 10 + (text[i] - '0');
			if (v > 2147483648LL)
				return false;
		}
		v = negative ? -v : v;
		if (v > INT_MAX || v < INT_MIN)
			return false;
		value = (int)v;
		return true;
	}

	// ---- CT time model (spec B.0.1; NinjaTrader's MathEx, NT:351-365) ----

	// Chicago wall-clock time: seconds since Sierra Chart's base date.
	typedef int64_t CtTime;

	int DateOfCt(CtTime t)
	{
		return (int)FloorDiv(t, SECONDS_DAY);
	}

	// NinjaTrader's MathEx.Minute: the CT minute of the day.
	int MinuteOfDay(CtTime t)
	{
		return (int)((t - (int64_t)DateOfCt(t) * SECONDS_DAY) / 60);
	}

	int WeekdayOfCt(CtTime t)
	{
		return WeekdayOf(DateOfCt(t));
	}

	// 17:00 CT starts the next trading date (NT:351), whatever the chart's Session Times.
	int TradingDate(CtTime t)
	{
		const int date = DateOfCt(t);
		return t - (int64_t)date * SECONDS_DAY >= 17 * 3600 ? date + 1 : date;
	}

	// The Monday on or before a trading date (NT:352).
	int WeekOf(int td)
	{
		return td - (WeekdayOf(td) + 6) % 7;
	}

	// The first of the trading date's month (NT:353).
	int MonthOf(int td)
	{
		const CivilDate c = CivilOf(td);
		return DateOf(c.Year, c.Month, 1);
	}

	int YearOf(int td)
	{
		return DateOf(CivilOf(td).Year, 1, 1);
	}

	CtTime CtAt(int date, int seconds)
	{
		return (CtTime)date * SECONDS_DAY + seconds;
	}

	// One NinjaTrader session text "HHmm-HHmm[:days]" (NT:355-365), parsed once. Days: digits 1-7,
	// 1 = Sunday; NinjaTrader tests string.Contains, so any other character is ignored and an empty
	// day list matches no day.
	struct SessionSpec
	{
		int		A			= 0;
		int		B			= 0;
		bool	AllDays		= true;
		uint8_t	DayMask		= 0;	// bit d for day digit d (1..7)
	};

	// NinjaTrader's parser: the range must split into two 4-character halves; each half is
	// int.Parse(first two) * 60 + int.Parse(last two) (so "+830" and " 830" are 08:30); a <= 1439,
	// b <= 1440 (2400 ends at midnight), minutes <= 59. False where NinjaTrader throws.
	bool ParseSession(const std::string& text, SessionSpec& out)
	{
		const size_t colon = text.find(':');
		const std::string range = text.substr(0, colon);
		const size_t dash = range.find('-');
		if (dash == std::string::npos || range.find('-', dash + 1) != std::string::npos)
			return false;
		const std::string first = range.substr(0, dash), second = range.substr(dash + 1);
		if (first.size() != 4 || second.size() != 4)
			return false;
		int h1 = 0, m1 = 0, h2 = 0, m2 = 0;
		if (!TryParseNetInt(first.substr(0, 2), h1) || !TryParseNetInt(first.substr(2), m1) || !TryParseNetInt(second.substr(0, 2), h2)
			|| !TryParseNetInt(second.substr(2), m2))
			return false;
		const int a = h1 * 60 + m1, b = h2 * 60 + m2;
		if (a > 1439 || b > 1440 || m1 > 59 || m2 > 59)
			return false;
		SessionSpec s;
		s.A = a;
		s.B = b;
		if (colon != std::string::npos)
		{
			// Split(':')[1]: up to the next colon.
			const size_t next = text.find(':', colon + 1);
			const std::string days = text.substr(colon + 1, next == std::string::npos ? std::string::npos : next - colon - 1);
			s.AllDays = false;
			for (char c : days)
				if (c >= '1' && c <= '7')
					s.DayMask = (uint8_t)(s.DayMask | (1u << (c - '0')));
		}
		out = s;
		return true;
	}

	bool InSession(CtTime t, const SessionSpec& s)
	{
		const int m = MinuteOfDay(t);
		const bool day = s.AllDays || (s.DayMask & (1u << (WeekdayOfCt(t) + 1))) != 0;
		return day && (s.A == s.B || (s.A < s.B ? m >= s.A && m < s.B : m >= s.A || m < s.B));
	}

	// ---- MathEx (NT:346-412) ----

	bool Valid(double x)
	{
		return std::isfinite(x);
	}

	// Pine rounds ties toward positive infinity, unlike Math.Round's banker's rounding.
	int64_t Bin(double x, double step)
	{
		return (int64_t)std::floor(x / step + .5);
	}

	std::string Upper(const std::string& text)
	{
		std::string out = text;
		for (char& c : out)
			if (c >= 'a' && c <= 'z')
				c = (char)(c - 'a' + 'A');
		return out;
	}

	struct MathEx
	{
		// Micro contracts trade at the parent's prices, so they load the parent's levels (NT:368-378:
		// {root} in the levels path, the levels cache, the Symbol: check).
		static std::string LevelsRoot(const std::string& root)
		{
			const std::string u = Upper(root);
			if (u == "MES")
				return "ES";
			if (u == "MNQ")
				return "NQ";
			if (u == "MCL")
				return "CL";
			if (u == "MGC")
				return "GC";
			return root;
		}
	};

	// Profile row scale (NT:382-397): Auto keeps rows near 0.0035% of price, 1, 2 or 5 times a power
	// of ten in ticks.
	int RowMult(const std::string& scale, double price, double tick)
	{
		int m = 1;
		if (scale != "Auto")
		{
			std::string number = scale;
			while (!number.empty() && number.back() == 'x')
				number.pop_back();
			if (!TryParseNetInt(number, m))
				m = 1;
		}
		else if (Valid(price) && price > 0 && tick > 0)
		{
			const double raw = price * 0.000035 / tick;
			if (raw >= std::sqrt(2.0))
			{
				const double dec = std::pow(10.0, std::floor(std::log10(raw))), f = raw / dec;
				const double n = f < std::sqrt(2.0) ? 1 : f < std::sqrt(10.0) ? 2 : f < std::sqrt(50.0) ? 5 : 10;
				m = (int)RoundHalfAway(n * dec);
			}
		}
		return (std::max)(1, m);
	}

	double AutoTick(const std::string& root, double tick, double close)
	{
		const std::string u = Upper(root);
		if (u == "CL" || u == "MCL")
			return .05;
		if (u == "NG" || u == "QG")
			return .005;
		if (u == "GC" || u == "MGC")
			return .5;
		if (u == "SI" || u == "SIL")
			return .05;
		if (u == "HG" || u == "QC")
			return .005;
		if (u == "ZB" || u == "ZN")
			return .015625;
		if (u == "6E" || u == "M6E")
			return .0005;
		if (u == "6J" || u == "M6J")
			return .0000005;
		return close > 1000 && tick < .1 ? .25 : tick;
	}

	// The instrument root from Sierra Chart's symbol (spec B.0.2, SIERRA: Sierra Chart has no root
	// field): upper case, cut at the first _ . - space or #, then a trailing futures month code and
	// year ([FGHJKMNQUVXZ] + 1-4 digits) removed when something remains. ESZ26_FUT_CME -> ES,
	// ESZ6.CME -> ES, MESZ2026 -> MES, 6EZ26-CME -> 6E, ES# -> ES.
	std::string RootOf(const std::string& symbol)
	{
		std::string s = Upper(symbol);
		const size_t cut = s.find_first_of("_.- #");
		if (cut != std::string::npos)
			s = s.substr(0, cut);
		size_t digits = 0;
		while (digits < s.size() && digits < 4 && s[s.size() - 1 - digits] >= '0' && s[s.size() - 1 - digits] <= '9')
			digits++;
		if (digits >= 1 && s.size() >= digits + 2)
		{
			const char month = s[s.size() - 1 - digits];
			if (strchr("FGHJKMNQUVXZ", month) != nullptr)
				s = s.substr(0, s.size() - 1 - digits);
		}
		return s;
	}

	// ---- Engine data (NT:340-345, NT:428-522) ----

	// Index: the chart bar's index (where it is drawn, its samples, its alert ids). Seq: NinjaTrader's
	// bar number, the chart bars holding trades before it (Sierra Chart's empty columns, Include
	// Columns With No Data, are not bars to NinjaTrader): the completed profiles' 4,500-bar window
	// counts these (NT:998).
	struct Bar
	{
		CtTime	Start	= 0;
		CtTime	End		= 0;
		int		Index	= 0;
		int		Seq		= 0;
		double	Open	= 0;
		double	High	= 0;
		double	Low		= 0;
		double	Close	= 0;
		double	Volume	= 0;
	};

	struct ProfileStats
	{
		double Poc		= NaN;
		double Vah		= NaN;
		double Val		= NaN;
		double Total	= 0;
	};

	// NinjaTrader's Profile (NT:432-470): volume per row key (Bin of the price), the keys in
	// first-insertion order, the oldest evicted at the row limit.
	struct Profile
	{
		double						Step		= 1;
		int							Limit		= 1;
		std::map<int64_t, double>	Rows;
		std::deque<int64_t>			Insertion;
		int64_t						PrunedRows	= 0;

		Profile() = default;
		Profile(double step, int limit) : Step(step), Limit((std::max)(1, limit)) {}

		// Upper-exclusive (the top bin gets nothing unless the bar is one bin), at most the lowest 200
		// rows of a wider bar when capped (both originals, KEPT).
		void Add(const Bar& b, bool capped)
		{
			const int64_t lo = Bin(b.Low, Step), hi = Bin(b.High, Step);
			int64_t count = (std::max)((int64_t)1, hi - lo);
			if (capped)
				count = (std::min)((int64_t)200, count);
			const double per = (std::max)(0.0, b.Volume) / (double)count;
			const int64_t skip = (std::max)((int64_t)0, count - Limit);
			PrunedRows += skip;
			for (int64_t k = lo + skip; k < lo + count; k++)
			{
				auto found = Rows.find(k);
				if (found == Rows.end())
				{
					while ((int64_t)Rows.size() >= Limit)
					{
						Rows.erase(Insertion.front());
						Insertion.pop_front();
						PrunedRows++;
					}
					Insertion.push_back(k);
					found = Rows.emplace(k, 0.0).first;
				}
				found->second = found->second + per;
			}
		}

		// The POC (first-inserted wins ties) and the value area walk (NT:454-469).
		ProfileStats Stats(double pct) const
		{
			ProfileStats s;
			if (Rows.empty())
				return s;
			double max = -1;
			int64_t poc = 0;
			for (int64_t k : Insertion)
			{
				const double v = Rows.at(k);
				s.Total += v;
				if (v > max)
				{
					max = v;
					poc = k;
				}
			}
			if (s.Total <= 0)
				return s;
			std::vector<int64_t> keys;
			std::vector<double> values;
			keys.reserve(Rows.size());
			values.reserve(Rows.size());
			for (const auto& row : Rows)
			{
				keys.push_back(row.first);
				values.push_back(row.second);
			}
			const int n = (int)keys.size();
			int up = (int)(std::lower_bound(keys.begin(), keys.end(), poc) - keys.begin()), dn = up;
			double area = max;
			const double target = s.Total * (pct > 1 ? pct / 100 : pct);
			while (area < target && (up < n - 1 || dn > 0))
			{
				const double vu = up < n - 1 ? values[(size_t)up + 1] : 0, vd = dn > 0 ? values[(size_t)dn - 1] : 0;
				if ((vu >= vd && up < n - 1) || dn <= 0)
					area += values[(size_t)++up];
				else
					area += values[(size_t)--dn];
			}
			s.Poc = (double)poc * Step;
			s.Vah = (double)keys[(size_t)up] * Step;
			s.Val = (double)keys[(size_t)dn] * Step;
			return s;
		}
	};

	// Wilder's average (NT:471-477): the first n values are summed, then the running average.
	struct Rma
	{
		int		Period	= 1;
		int		Count	= 0;
		double	Sum		= 0;
		double	Value	= NaN;

		explicit Rma(int n = 1) : Period((std::max)(1, n)) {}

		double Add(double x)
		{
			if (!Valid(x))
				return Value;
			if (++Count <= Period)
			{
				Sum += x;
				if (Count == Period)
					Value = Sum / Period;
			}
			else
				Value = (Value * (Period - 1) + x) / Period;
			return Value;
		}
	};

	struct DailyValue
	{
		int		Date	= 0;
		double	Close	= 0;
		double	High	= 0;
		double	Low		= 0;
		double	Atr14	= NaN;
		double	Atr		= NaN;
	};

	// Daily bars in date order with their true-range averages (NT:482-493).
	struct DailyHistory
	{
		std::vector<DailyValue>	Data;
		Rma						R14		= Rma(14);
		Rma						Ra		= Rma(14);
		double					Prev	= NaN;

		explicit DailyHistory(int atr = 14) : Ra(atr) {}

		void Add(int date, double h, double l, double c)
		{
			if (!Data.empty() && date <= Data.back().Date)
				return;
			const double tr = Valid(Prev) ? MaxNet(h - l, MaxNet(std::fabs(h - Prev), std::fabs(l - Prev))) : h - l;
			DailyValue v;
			v.Date	= date;
			v.Close	= c;
			v.High	= h;
			v.Low	= l;
			v.Atr14	= R14.Add(tr);
			v.Atr	= Ra.Add(tr);
			Data.push_back(v);
			Prev = c;
		}

		// The last entry dated before `date`, or null.
		const DailyValue* Before(int date) const
		{
			for (size_t i = Data.size(); i-- > 0;)
				if (Data[i].Date < date)
					return &Data[i];
			return nullptr;
		}
	};

	// A daily level (NT:494-499). LevelsDocument::Parse fills the list.
	struct Level
	{
		std::string	Name;
		double		Price	= 0;
		int			Kind	= 0;	// 0 pivot, -1 resistance, 1 support
		bool		Flipped	= false;
	};

	// ---- .NET text and numbers, as NinjaTrader's levels code sees them (spec B.4.1) ----
	// NinjaTrader's strings are UTF-16, so the levels text is parsed as UTF-16 here too: lengths, trims,
	// the regular expressions and the number parsing and formatting behave as .NET Framework 4.x's
	// (checked against NinjaTrader's own code in tests\amt_oracle over large corpora).

	typedef std::wstring Text16;	// wchar_t is 16 bits on Windows

	Text16 Utf16Of(const std::string& utf8)
	{
		if (utf8.empty())
			return Text16();
		const int length = MultiByteToWideChar(CP_UTF8, 0, utf8.data(), (int)utf8.size(), nullptr, 0);
		Text16 wide((size_t)(std::max)(0, length), L'\0');
		if (length > 0)
			MultiByteToWideChar(CP_UTF8, 0, utf8.data(), (int)utf8.size(), &wide[0], length);
		return wide;
	}

	std::string Utf8Of(const Text16& wide)
	{
		if (wide.empty())
			return std::string();
		const int length = WideCharToMultiByte(CP_UTF8, 0, wide.data(), (int)wide.size(), nullptr, 0, nullptr, nullptr);
		std::string utf8((size_t)(std::max)(0, length), '\0');
		if (length > 0)
			WideCharToMultiByte(CP_UTF8, 0, wide.data(), (int)wide.size(), &utf8[0], length, nullptr, nullptr);
		return utf8;
	}

	// .NET's char.IsWhiteSpace, which is also its regular expressions' \s and String.Trim()'s set.
	bool IsWhiteNet(wchar_t c)
	{
		return c == L' ' || (c >= 0x09 && c <= 0x0D) || c == 0x85 || c == 0xA0 || c == 0x1680 || (c >= 0x2000 && c <= 0x200A) || c == 0x2028 || c == 0x2029
			|| c == 0x202F || c == 0x205F || c == 0x3000;
	}

	Text16 TrimNet(const Text16& s)
	{
		size_t a = 0, b = s.size();
		while (a < b && IsWhiteNet(s[a]))
			a++;
		while (b > a && IsWhiteNet(s[b - 1]))
			b--;
		return s.substr(a, b - a);
	}

	// String.Trim(params char[]).
	Text16 TrimChars(const Text16& s, const wchar_t* chars)
	{
		auto in = [chars](wchar_t c) { return c != 0 && wcschr(chars, c) != nullptr; };
		size_t a = 0, b = s.size();
		while (a < b && in(s[a]))
			a++;
		while (b > a && in(s[b - 1]))
			b--;
		return s.substr(a, b - a);
	}

	// .NET's regular-expression \d: Unicode decimal digits of the Basic Multilingual Plane (a supplementary
	// digit is two UTF-16 units, neither a digit). The ranges .NET Framework 4.x knows (measured).
	bool IsDigitNet(wchar_t c)
	{
		static const uint16_t starts[] = {0x0030, 0x0660, 0x06F0, 0x07C0, 0x0966, 0x09E6, 0x0A66, 0x0AE6, 0x0B66, 0x0BE6, 0x0C66, 0x0CE6, 0x0D66, 0x0DE6,
			0x0E50, 0x0ED0, 0x0F20, 0x1040, 0x1090, 0x17E0, 0x1810, 0x1946, 0x19D0, 0x1A80, 0x1A90, 0x1B50, 0x1BB0, 0x1C40, 0x1C50, 0xA620, 0xA8D0, 0xA900,
			0xA9D0, 0xA9F0, 0xAA50, 0xABF0, 0xFF10};
		for (uint16_t s : starts)
			if (c >= s && c < s + 10)
				return true;
		return false;
	}

	// A character as .NET's IgnoreCase regular expressions compare it with the ASCII letters of these
	// patterns (current culture lower case): A-Z, and the two non-ASCII letters that lower to ASCII
	// (U+0130 to i, the Kelvin sign U+212A to k; measured over the whole BMP).
	wchar_t FoldNet(wchar_t c)
	{
		if (c >= L'A' && c <= L'Z')
			return (wchar_t)(c - L'A' + L'a');
		if (c == 0x0130)
			return L'i';
		if (c == 0x212A)
			return L'k';
		return c;
	}

	// An IgnoreCase literal (ASCII, lower case) at position `at`.
	bool LiteralAt(const Text16& s, size_t at, const wchar_t* lower)
	{
		for (size_t k = 0; lower[k] != 0; k++)
			if (at + k >= s.size() || FoldNet(s[at + k]) != lower[k])
				return false;
		return true;
	}

	// String.StartsWith(prefix, StringComparison.OrdinalIgnoreCase) for an ASCII prefix: invariant upper
	// case, so only ASCII letters fold.
	bool StartsWithOrdinalIgnoreCase(const Text16& s, const wchar_t* prefix)
	{
		for (size_t k = 0; prefix[k] != 0; k++)
		{
			if (k >= s.size())
				return false;
			wchar_t a = s[k], b = prefix[k];
			a = a >= L'a' && a <= L'z' ? (wchar_t)(a - 32) : a;
			b = b >= L'a' && b <= L'z' ? (wchar_t)(b - 32) : b;
			if (a != b)
				return false;
		}
		return true;
	}

	// .NET Framework 4.x's double parsing (Number.ParseNumber + the CLR's NumberToDouble) and its "G"/"R"
	// formatting (DoubleToNumber), bit for bit. Its parser keeps 18 digits and multiplies with rounded
	// 64-bit powers of ten, so it is not always the nearest double (NinjaTrader's prices are what it gives).
	struct NetDouble
	{
		static uint64_t Bits(double v) { uint64_t b; memcpy(&b, &v, 8); return b; }
		static double FromBits(uint64_t b) { double v; memcpy(&v, &b, 8); return v; }

		static uint64_t Mul64Lossy(uint64_t a, uint64_t b, int& exponent)
		{
			uint64_t v = (a >> 32) * (b >> 32) + (((a >> 32) * (uint32_t)b) >> 32) + (((uint64_t)(uint32_t)a * (b >> 32)) >> 32);
			if ((v & 0x8000000000000000ull) == 0)
			{
				v <<= 1;
				exponent--;
			}
			return v;
		}

		// The CLR's NumberToDouble: digits (no leading zeros, as many as the parse kept), the decimal point
		// `scale` digits from the first one. The bits of the (positive) result.
		static uint64_t NumberToDouble(const std::string& digits, int scale)
		{
			static const uint64_t p10[30] = {0xa000000000000000ull, 0xc800000000000000ull, 0xfa00000000000000ull, 0x9c40000000000000ull,
				0xc350000000000000ull, 0xf424000000000000ull, 0x9896800000000000ull, 0xbebc200000000000ull, 0xee6b280000000000ull, 0x9502f90000000000ull,
				0xba43b74000000000ull, 0xe8d4a51000000000ull, 0x9184e72a00000000ull, 0xb5e620f480000000ull, 0xe35fa931a0000000ull,
				0xcccccccccccccccdull, 0xa3d70a3d70a3d70bull, 0x83126e978d4fdf3cull, 0xd1b71758e219652eull, 0xa7c5ac471b478425ull, 0x8637bd05af6c69b7ull,
				0xd6bf94d5e57a42beull, 0xabcc77118461ceffull, 0x89705f4136b4a599ull, 0xdbe6fecebdedd5c2ull, 0xafebff0bcb24ab02ull, 0x8cbccc096f5088cfull,
				0xe12e13424bb40e18ull, 0xb424dc35095cd813ull, 0x901d7cf73ab0acdcull};
			static const int e10[15] = {4, 7, 10, 14, 17, 20, 24, 27, 30, 34, 37, 40, 44, 47, 50};
			static const uint64_t p16[42] = {0x8e1bc9bf04000000ull, 0x9dc5ada82b70b59eull, 0xaf298d050e4395d6ull, 0xc2781f49ffcfa6d4ull, 0xd7e77a8f87daf7faull,
				0xefb3ab16c59b14a0ull, 0x850fadc09923329cull, 0x93ba47c980e98cdeull, 0xa402b9c5a8d3a6e6ull, 0xb616a12b7fe617a8ull, 0xca28a291859bbf90ull,
				0xe070f78d39275566ull, 0xf92e0c3537826140ull, 0x8a5296ffe33cc92cull, 0x9991a6f3d6bf1762ull, 0xaa7eebfb9df9de8aull, 0xbd49d14aa79dbc7eull,
				0xd226fc195c6a2f88ull, 0xe950df20247c83f8ull, 0x81842f29f2cce373ull, 0x8fcac257558ee4e2ull,
				0xe69594bec44de160ull, 0xcfb11ead453994c3ull, 0xbb127c53b17ec165ull, 0xa87fea27a539e9b3ull, 0x97c560ba6b0919b5ull, 0x88b402f7fd7553abull,
				0xf64335bcf065d3a0ull, 0xddd0467c64bce4c4ull, 0xc7caba6e7c5382edull, 0xb3f4e093db73a0b7ull, 0xa21727db38cb0053ull, 0x91ff83775423cc29ull,
				0x8380dea93da4bc82ull, 0xece53cec4a314f00ull, 0xd5605fcdcf32e217ull, 0xc0314325637a1978ull, 0xad1c8eab5ee43ba2ull, 0x9becce62836ac5b0ull,
				0x8c71dcd9ba0b495cull, 0xfd00b89747823938ull, 0xe3e27a444d8d991aull};
			static const int e16[21] = {54, 107, 160, 213, 266, 319, 373, 426, 479, 532, 585, 638, 691, 745, 798, 851, 904, 957, 1010, 1064, 1117};
			const int total = (int)digits.size();
			int remaining = total;
			if (remaining == 0)
				return 0;
			auto take = [&digits](int from, int count)
			{
				uint64_t v = 0;
				for (int k = 0; k < count; k++)
					v = v * 10 + (uint64_t)(digits[(size_t)(from + k)] - '0');
				return v;
			};
			int count = (std::min)(remaining, 9);
			remaining -= count;
			uint64_t val = take(0, count);
			if (remaining > 0)
			{
				count = (std::min)(remaining, 9);
				remaining -= count;
				const uint32_t mult = (uint32_t)(p10[count - 1] >> (64 - e10[count - 1]));
				val = val * mult + take(9, count);
			}
			const int sc = scale - (total - remaining);
			const int absScale = sc < 0 ? -sc : sc;
			if (absScale >= 22 * 16)
				return sc > 0 ? 0x7FF0000000000000ull : 0;
			int exponent = 64;
			if ((val & 0xFFFFFFFF00000000ull) == 0) { val <<= 32; exponent -= 32; }
			if ((val & 0xFFFF000000000000ull) == 0) { val <<= 16; exponent -= 16; }
			if ((val & 0xFF00000000000000ull) == 0) { val <<= 8; exponent -= 8; }
			if ((val & 0xF000000000000000ull) == 0) { val <<= 4; exponent -= 4; }
			if ((val & 0xC000000000000000ull) == 0) { val <<= 2; exponent -= 2; }
			if ((val & 0x8000000000000000ull) == 0) { val <<= 1; exponent -= 1; }
			int index = absScale & 15;
			if (index != 0)
			{
				const int multExponent = e10[index - 1];
				exponent += sc < 0 ? -multExponent + 1 : multExponent;
				val = Mul64Lossy(val, p10[index + (sc < 0 ? 15 : 0) - 1], exponent);
			}
			index = absScale >> 4;
			if (index != 0)
			{
				const int multExponent = e16[index - 1];
				exponent += sc < 0 ? -multExponent + 1 : multExponent;
				val = Mul64Lossy(val, p16[index + (sc < 0 ? 21 : 0) - 1], exponent);
			}
			if (((uint32_t)val & (1u << 10)) != 0)
			{
				uint64_t rounded = val + ((1u << 10) - 1) + (((uint32_t)val >> 11) & 1);
				if (rounded < val)
				{
					rounded = (rounded >> 1) | 0x8000000000000000ull;
					exponent++;
				}
				val = rounded;
			}
			exponent += 0x3FE;
			if (exponent <= 0)
			{
				if (exponent == -52 && val >= 0x8000000000000058ull)
					return 1;
				if (exponent <= -52)
					return 0;
				return val >> (-exponent + 12);
			}
			if (exponent >= 0x7FF)
				return 0x7FF0000000000000ull;
			return ((uint64_t)exponent << 52) + ((val >> 11) & 0x000FFFFFFFFFFFFFull);
		}

		// double.TryParse(s, NumberStyles.Float, CultureInfo.InvariantCulture, out v).
		static bool TryParse(const Text16& s, double& value)
		{
			value = 0;
			auto white = [](wchar_t c) { return c == L' ' || (c >= 0x09 && c <= 0x0D); };
			const size_t n = s.size();
			size_t i = 0;
			while (i < n && white(s[i]))
				i++;
			bool negative = false;
			if (i < n && (s[i] == L'+' || s[i] == L'-'))
				negative = s[i++] == L'-';
			std::string digits;
			size_t digitEnd = 0;
			int scale = 0;
			bool anyDigit = false, nonZero = false, decimal = false;
			for (; i < n; i++)
			{
				const wchar_t c = s[i];
				if (c >= L'0' && c <= L'9')
				{
					anyDigit = true;
					if (c != L'0' || nonZero)
					{
						if (digits.size() < 50)
						{
							digits += (char)c;
							if (c != L'0')
								digitEnd = digits.size();
						}
						if (!decimal)
							scale++;
						nonZero = true;
					}
					else if (decimal)
						scale--;
				}
				else if (c == L'.' && !decimal)
					decimal = true;
				else
					break;
			}
			bool ok = anyDigit;
			if (ok)
			{
				digits.resize(digitEnd);
				if (i < n && (s[i] == L'e' || s[i] == L'E'))
				{
					const size_t mark = i++;
					bool negativeExponent = false;
					if (i < n && (s[i] == L'+' || s[i] == L'-'))
						negativeExponent = s[i++] == L'-';
					if (i < n && s[i] >= L'0' && s[i] <= L'9')
					{
						int exponent = 0;
						while (i < n && s[i] >= L'0' && s[i] <= L'9')
						{
							exponent = exponent * 10 + (s[i++] - L'0');
							if (exponent > 1000)
							{
								exponent = 9999;
								while (i < n && s[i] >= L'0' && s[i] <= L'9')
									i++;
							}
						}
						scale += negativeExponent ? -exponent : exponent;
					}
					else
						i = mark;
				}
				while (i < n && white(s[i]))
					i++;
				while (i < n && s[i] == 0)
					i++;
				ok = i == n;
			}
			if (ok)
			{
				uint64_t bits = NumberToDouble(digits, scale);
				if (((bits >> 52) & 0x7FF) == 0x7FF)
					ok = false;
				else
				{
					// NumberBufferToDouble: a zero result is +0 (the sign is dropped).
					if (bits != 0 && negative)
						bits |= 0x8000000000000000ull;
					value = FromBits(bits);
					return true;
				}
			}
			// The culture's symbols, after a failed parse.
			const Text16 trimmed = TrimNet(s);
			if (trimmed == L"Infinity")
				value = std::numeric_limits<double>::infinity();
			else if (trimmed == L"-Infinity")
				value = -std::numeric_limits<double>::infinity();
			else if (trimmed == L"NaN")
				value = NaN;
			else
				return false;
			return true;
		}

		// The exact decimal digits of a finite positive double and the position of its decimal point.
		static void ExactDigits(double v, std::string& digits, int& scale)
		{
			const uint64_t bits = Bits(v);
			const int biased = (int)((bits >> 52) & 0x7FF);
			uint64_t mantissa = bits & 0x000FFFFFFFFFFFFFull;
			int exponent = biased == 0 ? -1074 : biased - 1075;
			if (biased != 0)
				mantissa |= 0x0010000000000000ull;
			std::vector<uint32_t> limbs;	// base 1e9, little endian
			auto multiply = [&limbs](uint32_t factor)
			{
				uint64_t carry = 0;
				for (uint32_t& limb : limbs)
				{
					const uint64_t x = (uint64_t)limb * factor + carry;
					limb = (uint32_t)(x % 1000000000u);
					carry = x / 1000000000u;
				}
				while (carry != 0)
				{
					limbs.push_back((uint32_t)(carry % 1000000000u));
					carry /= 1000000000u;
				}
			};
			limbs.push_back((uint32_t)(mantissa % 1000000000u));
			if (mantissa >= 1000000000u)
			{
				limbs.push_back((uint32_t)(mantissa / 1000000000u % 1000000000u));
				if (mantissa >= 1000000000000000000ull)
					limbs.push_back((uint32_t)(mantissa / 1000000000000000000ull));
			}
			int fraction = 0;
			if (exponent > 0)
				for (int k = exponent; k > 0; k -= 29)
					multiply(1u << (std::min)(k, 29));
			else if (exponent < 0)
			{
				fraction = -exponent;
				for (int k = fraction; k > 0; k -= 13)
				{
					uint32_t f = 1;
					for (int j = 0; j < (std::min)(k, 13); j++)
						f *= 5;
					multiply(f);
				}
			}
			std::string text;
			char chunk[16];
			snprintf(chunk, sizeof(chunk), "%u", limbs.back());
			text = chunk;
			for (size_t k = limbs.size() - 1; k-- > 0;)
			{
				snprintf(chunk, sizeof(chunk), "%09u", limbs[k]);
				text += chunk;
			}
			const size_t first = text.find_first_not_of('0');
			text = first == std::string::npos ? std::string("0") : text.substr(first);
			scale = (int)text.size() - fraction;
			const size_t last = text.find_last_not_of('0');
			digits = text.substr(0, last + 1);
		}

		// DoubleToNumber: `precision` significant digits of |v|, the exact value rounded half away from zero.
		static void ToDigits(double v, int precision, std::string& digits, int& scale)
		{
			std::string exact;
			ExactDigits(std::fabs(v), exact, scale);
			if ((int)exact.size() <= precision)
			{
				digits = exact + std::string((size_t)(precision - (int)exact.size()), '0');
				return;
			}
			digits = exact.substr(0, (size_t)precision);
			if (exact[(size_t)precision] >= '5')
			{
				int k = precision - 1;
				while (k >= 0 && digits[(size_t)k] == '9')
					digits[(size_t)k--] = '0';
				if (k >= 0)
					digits[(size_t)k]++;
				else
				{
					digits = "1" + digits.substr(0, (size_t)precision - 1);
					scale++;
				}
			}
		}

		// NumberToString with format 'G' and nMaxDigits (trailing zeros trimmed).
		static std::string General(std::string digits, int scale, bool negative, int maxDigits)
		{
			while (!digits.empty() && digits.back() == '0')
				digits.pop_back();
			if (digits.empty())
				return "0";
			const bool scientific = scale > maxDigits || scale < -3;
			int point = scientific ? 1 : scale;
			std::string out = negative ? "-" : "";
			size_t i = 0;
			if (point > 0)
				for (; point > 0; point--)
					out += i < digits.size() ? digits[i++] : '0';
			else
				out += '0';
			if (i < digits.size() || point < 0)
			{
				out += '.';
				for (; point < 0; point++)
					out += '0';
				out += digits.substr(i);
			}
			if (scientific)
			{
				const int e = scale - 1;
				char text[16];
				snprintf(text, sizeof(text), "E%c%02d", e < 0 ? '-' : '+', e < 0 ? -e : e);
				out += text;
			}
			return out;
		}

		// double.ToString(CultureInfo.InvariantCulture) ("G", 15 digits) or ToString("R", ...): 15 digits
		// when they parse back (with .NET's own parser) to the value, else 17.
		static std::string Format(double v, bool roundTrip)
		{
			if (v != v)
				return "NaN";
			if (std::isinf(v))
				return v > 0 ? "Infinity" : "-Infinity";
			if (v == 0)
				return "0";
			std::string digits;
			int scale = 0;
			ToDigits(v, 15, digits, scale);
			if (!roundTrip || NumberToDouble(digits, scale) == (Bits(v) & 0x7FFFFFFFFFFFFFFFull))
				return General(digits, scale, v < 0, 15);
			ToDigits(v, 17, digits, scale);
			return General(digits, scale, v < 0, 17);
		}
	};

	// DateTime.TryParseExact(text, "yyyy-MM-dd", InvariantCulture, DateTimeStyles.None): ASCII digits
	// only, a real calendar date. Sierra Chart's date number.
	bool ParseIsoDate(const Text16& s, int& date)
	{
		if (s.size() != 10 || s[4] != L'-' || s[7] != L'-')
			return false;
		int v[3] = {0, 0, 0};
		const int at[3] = {0, 5, 8}, length[3] = {4, 2, 2};
		for (int k = 0; k < 3; k++)
			for (int j = 0; j < length[k]; j++)
			{
				const wchar_t c = s[(size_t)(at[k] + j)];
				if (c < L'0' || c > L'9')
					return false;
				v[k] = v[k] * 10 + (c - L'0');
			}
		static const int days[12] = {31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31};
		const bool leap = (v[0] % 4 == 0 && v[0] % 100 != 0) || v[0] % 400 == 0;
		if (v[0] < 1 || v[1] < 1 || v[1] > 12 || v[2] < 1 || v[2] > days[v[1] - 1] + (v[1] == 2 && leap ? 1 : 0))
			return false;
		date = DateOf(v[0], v[1], v[2]);
		return true;
	}

	std::string IsoDate(int date)
	{
		const CivilDate c = CivilOf(date);
		char text[16];
		snprintf(text, sizeof(text), "%04d-%02d-%02d", c.Year, c.Month, c.Day);
		return text;
	}

	// yyyy-MM-dd HH:mm:ss of a CT time (the Discord message's stamp, NT:1898).
	std::string CtStamp(CtTime t)
	{
		const int date = DateOfCt(t);
		const int s = (int)(t - (int64_t)date * SECONDS_DAY);
		char text[16];
		snprintf(text, sizeof(text), " %02d:%02d:%02d", s / 3600, s / 60 % 60, s % 60);
		return IsoDate(date) + text;
	}

	// ---- The levels text (LevelsDocument, NT:1117-1238) ----

	struct LevelsDocument
	{
		std::vector<Level>	Levels;
		bool				HasDate		= false;
		int					Date		= 0;
		bool				HasSymbol	= false;
		std::string			Symbol;

		// NinjaTrader's LevelsDocument.Parse: false with NinjaTrader's message where it throws.
		static bool Parse(const std::string& utf8, bool allowEmpty, LevelsDocument& result, std::string& error)
		{
			result = LevelsDocument();
			error.clear();
			const Text16 text = Utf16Of(utf8);
			if (TrimNet(text).empty())
			{
				if (!allowEmpty)
				{
					error = "The levels file is empty.";
					return false;
				}
				return true;
			}
			if (text.size() > 1048576)
			{
				error = "Levels input exceeds 1 MB.";
				return false;
			}
			// Split order: real line breaks, then "||" (the If/Then one-liner).
			Text16 unified;
			unified.reserve(text.size());
			for (size_t i = 0; i < text.size(); i++)
			{
				if (text[i] == L'\r')
				{
					unified += L'\n';
					if (i + 1 < text.size() && text[i + 1] == L'\n')
						i++;
				}
				else
					unified += text[i];
			}
			std::vector<Text16> lines;
			size_t start = 0;
			for (size_t i = 0; i <= unified.size(); i++)
				if (i == unified.size() || unified[i] == L'\n')
				{
					const Text16 piece = unified.substr(start, i - start);
					size_t from = 0;
					for (size_t bar = piece.find(L"||"); bar != Text16::npos; bar = piece.find(L"||", from))
					{
						lines.push_back(piece.substr(from, bar - from));
						from = bar + 2;
					}
					lines.push_back(piece.substr(from));
					start = i + 1;
				}
			bool found[3] = {false, false, false};	// pivot, resistance, support
			int foundCount = 0;
			std::vector<Level> labeled;
			bool hasHeaderDate = false, hasPaste = false, hasLabeledError = false;
			int headerDate = 0;
			Text16 paste;
			std::string labeledError;
			for (const Text16& raw : lines)
			{
				// A Discord mobile copy brings the whole message: title, code fences, bold markers.
				const Text16 line = TrimChars(TrimNet(raw), L"\xFEFF`* \t");
				// Comments and If/Then band lines (^[UVND]\|) belong to other parsers.
				const bool band = line.size() >= 2 && (line[0] == L'U' || line[0] == L'V' || line[0] == L'N' || line[0] == L'D') && line[1] == L'|';
				if (line.empty() || line[0] == L'#' || band)
					continue;
				Text16 group, unused;
				if (MatchPaste(line, group, unused))
				{
					if (hasPaste)
					{
						error = "Use one paste line per symbol.";
						return false;
					}
					hasPaste = true;
					paste = line;
					continue;
				}
				if (MatchDate(line, group))
				{
					int parsed = 0;
					if (hasHeaderDate || !ParseIsoDate(TrimNet(group), parsed))
					{
						error = "Use one Date: YYYY-MM-DD line.";
						return false;
					}
					hasHeaderDate = true;
					headerDate = parsed;
					continue;
				}
				if (MatchSymbol(line, group))
				{
					if (result.HasSymbol)
					{
						error = "Use one Symbol: line.";
						return false;
					}
					Text16 upper = group;
					for (wchar_t& c : upper)
						if (c >= L'a' && c <= L'z')
							c = (wchar_t)(c - 32);
					result.HasSymbol = true;
					result.Symbol = Utf8Of(upper);
					continue;
				}
				Text16 name, values;
				if (!MatchSection(line, name, values))
					continue;	// Titles, report headings and commentary are deliberately ignored.
				// Labeled-block problems only matter when there is no paste line (the paste line wins).
				if (hasLabeledError)
					continue;
				labeledError = ParseLabeled(name, values, found, foundCount, labeled);
				hasLabeledError = !labeledError.empty();
			}
			if (hasPaste)
			{
				if (!ParsePaste(paste, result, error))
					return false;
				if (hasHeaderDate && headerDate != result.Date)
				{
					error = "The Date: line and the paste-line date differ.";
					return false;
				}
			}
			else
			{
				if (hasLabeledError)
				{
					error = labeledError;
					return false;
				}
				if (foundCount == 0)
				{
					error = "No levels found. Paste the Discord line (2026-09-30, pivot, resistance..., support...) or the Pivot Level / Resistance Levels / "
						"Support Levels block.";
					return false;
				}
				if (foundCount != 3)
				{
					error = "Include Pivot Level:, Resistance Levels:, and Support Levels:.";
					return false;
				}
				result.Levels = labeled;
				result.HasDate = hasHeaderDate;
				result.Date = headerDate;
			}
			// A thousands separator splits one price into two, e.g. "7,745.25" becomes 7 and 745.25.
			const Level* pivot = nullptr;
			for (const Level& l : result.Levels)
				if (pivot == nullptr && l.Kind == 0)
					pivot = &l;
			for (const Level& l : result.Levels)
				if (pivot != nullptr && std::fabs(l.Price - pivot->Price) > std::fabs(pivot->Price) * .2)
				{
					error = "Price " + NetDouble::Format(l.Price, false) + " is more than 20% from the pivot. Write prices without thousands separators.";
					return false;
				}
			return true;
		}

		// NinjaTrader's Serialize (NT:1230-1237): the accepted document, prices in .NET's "R" format.
		std::string Serialize() const
		{
			if (Levels.empty())
				return "";
			std::string out = (HasSymbol ? "Symbol: " + Symbol + "\n" : std::string()) + (HasDate ? "Date: " + IsoDate(Date) + "\n" : std::string());
			for (int kind : {0, -1, 1})
			{
				out += kind == 0 ? "Pivot Level: " : kind == -1 ? "Resistance Levels: " : "Support Levels: ";
				bool first = true;
				for (const Level& l : Levels)
					if (l.Kind == kind)
					{
						out += (first ? "" : ", ") + NetDouble::Format(l.Price, true);
						first = false;
					}
				out += "\n";
			}
			return out;
		}

	private:
		// ^(\d{4}-\d{2}-\d{2})\s*,(.*)$
		static bool MatchPaste(const Text16& s, Text16& date, Text16& rest)
		{
			if (s.size() < 11)
				return false;
			for (size_t k = 0; k < 10; k++)
				if (k == 4 || k == 7 ? s[k] != L'-' : !IsDigitNet(s[k]))
					return false;
			size_t i = 10;
			while (i < s.size() && IsWhiteNet(s[i]))
				i++;
			if (i >= s.size() || s[i] != L',')
				return false;
			const Text16 d = s.substr(0, 10);
			rest = s.substr(i + 1);
			date = d;
			return true;
		}

		// After a literal: \s*:\s*(.*)$
		static bool ColonRest(const Text16& s, size_t i, Text16& rest)
		{
			while (i < s.size() && IsWhiteNet(s[i]))
				i++;
			if (i >= s.size() || s[i] != L':')
				return false;
			i++;
			while (i < s.size() && IsWhiteNet(s[i]))
				i++;
			rest = s.substr(i);
			return true;
		}

		// ^(?:Date|Trading Date)\s*:\s*(.*)$, IgnoreCase.
		static bool MatchDate(const Text16& s, Text16& rest)
		{
			return (LiteralAt(s, 0, L"date") && ColonRest(s, 4, rest)) || (LiteralAt(s, 0, L"trading date") && ColonRest(s, 12, rest));
		}

		// ^Symbol\s*:\s*([A-Za-z0-9]+)\s*$, IgnoreCase (its class also takes U+0130 and U+212A).
		static bool MatchSymbol(const Text16& s, Text16& symbol)
		{
			Text16 rest;
			if (!LiteralAt(s, 0, L"symbol") || !ColonRest(s, 6, rest))
				return false;
			size_t i = 0;
			while (i < rest.size())
			{
				const wchar_t c = FoldNet(rest[i]);
				if (!((c >= L'a' && c <= L'z') || (c >= L'0' && c <= L'9')))
					break;
				i++;
			}
			if (i == 0)
				return false;
			for (size_t j = i; j < rest.size(); j++)
				if (!IsWhiteNet(rest[j]))
					return false;
			symbol = rest.substr(0, i);
			return true;
		}

		// ^(Pivot Level|Resistance Levels|Support Levels)\s*:\s*(.*)$, IgnoreCase.
		static bool MatchSection(const Text16& s, Text16& name, Text16& rest)
		{
			for (const wchar_t* literal : {L"pivot level", L"resistance levels", L"support levels"})
			{
				const size_t length = wcslen(literal);
				if (LiteralAt(s, 0, literal) && ColonRest(s, length, rest))
				{
					name = s.substr(0, length);
					return true;
				}
			}
			return false;
		}

		static std::vector<Text16> SplitCommas(const Text16& s)
		{
			std::vector<Text16> out;
			size_t start = 0;
			for (size_t i = 0; i <= s.size(); i++)
				if (i == s.size() || s[i] == L',')
				{
					out.push_back(s.substr(start, i - start));
					start = i + 1;
				}
			return out;
		}

		static bool Price(const Text16& item, double& price)
		{
			return NetDouble::TryParse(TrimNet(item), price) && Valid(price);
		}

		static std::string ParseLabeled(const Text16& name, const Text16& text, bool found[3], int& foundCount, std::vector<Level>& labeled)
		{
			const int kind = StartsWithOrdinalIgnoreCase(name, L"Pivot") ? 0 : StartsWithOrdinalIgnoreCase(name, L"Resistance") ? -1 : 1;
			const int slot = kind == 0 ? 0 : kind == -1 ? 1 : 2;
			if (found[slot])
				return "Duplicate levels section: " + Utf8Of(name);
			found[slot] = true;
			foundCount++;
			const std::vector<Text16> values = SplitCommas(text);
			if (kind == 0 && values.size() != 1)
				return "Pivot requires one price without thousands separators.";
			if (kind != 0 && values.size() > 50)
				return "Maximum 50 prices in each support/resistance section.";
			for (size_t i = 0; i < values.size(); i++)
			{
				double price = 0;
				if (!Price(values[i], price))
					return "Invalid price in " + Utf8Of(name) + ". Use decimal prices separated by commas.";
				Level l;
				l.Kind	= kind;
				l.Price	= price;
				l.Name	= kind == 0 ? "PIVOT" : std::string(kind == 1 ? "SUPP" : "RES") + std::to_string(i + 1);
				labeled.push_back(l);
			}
			return std::string();
		}

		// First price is the pivot; above it is resistance, below it support, numbered outward (NT:1204-1229).
		static bool ParsePaste(const Text16& line, LevelsDocument& result, std::string& error)
		{
			Text16 dateText, rest;
			MatchPaste(line, dateText, rest);
			int date = 0;
			if (!ParseIsoDate(dateText, date))
			{
				error = "The paste line must start with a YYYY-MM-DD date.";
				return false;
			}
			std::vector<double> prices;
			for (const Text16& item : SplitCommas(rest))
			{
				double price = 0;
				if (!Price(item, price))
				{
					error = "Invalid price in the paste line: '" + Utf8Of(TrimNet(item)) + "'. Use decimal prices separated by commas.";
					return false;
				}
				prices.push_back(price);
			}
			const double pivot = prices[0];
			for (size_t i = 1; i < prices.size(); i++)
				if (std::fabs(prices[i] - pivot) > std::fabs(pivot) * .2)
				{
					error = "A paste-line price is more than 20% from the pivot. Write prices without thousands separators.";
					return false;
				}
			for (size_t i = 1; i < prices.size(); i++)
				if (prices[i] == pivot)
				{
					error = "A paste-line price equals the pivot.";
					return false;
				}
			std::vector<double> res, sup;
			for (size_t i = 1; i < prices.size(); i++)
			{
				if (prices[i] > pivot)
					res.push_back(prices[i]);
				if (prices[i] < pivot)
					sup.push_back(prices[i]);
			}
			std::stable_sort(res.begin(), res.end(), [](double a, double b) { return a < b; });
			std::stable_sort(sup.begin(), sup.end(), [](double a, double b) { return a > b; });
			if (res.empty() || sup.empty())
			{
				error = "The paste line needs at least one price above and one below the pivot.";
				return false;
			}
			if (res.size() > 50 || sup.size() > 50)
			{
				error = "Maximum 50 prices on each side of the pivot.";
				return false;
			}
			result.HasDate = true;
			result.Date = date;
			Level p;
			p.Kind	= 0;
			p.Price	= pivot;
			p.Name	= "PIVOT";
			result.Levels.push_back(p);
			for (size_t i = 0; i < res.size(); i++)
			{
				Level l;
				l.Kind	= -1;
				l.Price	= res[i];
				l.Name	= "RES" + std::to_string(i + 1);
				result.Levels.push_back(l);
			}
			for (size_t i = 0; i < sup.size(); i++)
			{
				Level l;
				l.Kind	= 1;
				l.Price	= sup[i];
				l.Name	= "SUPP" + std::to_string(i + 1);
				result.Levels.push_back(l);
			}
			return true;
		}
	};

	// NinjaTrader's Level.Parse (NT:498): the levels of a (serialized, accepted) text; none if it does not
	// parse (NinjaTrader would fault; its engine only ever gets an accepted document's text).
	std::vector<Level> ParseLevels(const std::string& text)
	{
		LevelsDocument document;
		std::string error;
		if (!LevelsDocument::Parse(text, true, document, error))
			return std::vector<Level>();
		return document.Levels;
	}

	// ---- The levels file (LevelFileSource, NT:1242-1356), with kernel32 calls only ----

	// .NET's message for a failed file call (System.IO.__Error.WinIOError), naming the path.
	std::string IoErrorMessage(DWORD error, const std::string& path)
	{
		switch (error)
		{
			case ERROR_FILE_NOT_FOUND:		return "Could not find file '" + path + "'.";
			case ERROR_PATH_NOT_FOUND:		return "Could not find a part of the path '" + path + "'.";
			case ERROR_ACCESS_DENIED:		return "Access to the path '" + path + "' is denied.";
			case ERROR_SHARING_VIOLATION:	return "The process cannot access the file '" + path + "' because it is being used by another process.";
			case ERROR_INVALID_DRIVE:		return "Could not find the drive '" + path + "'. The drive might not be ready or might not be mapped.";
			case ERROR_FILENAME_EXCED_RANGE:
				return "The specified path, file name, or both are too long. The fully qualified file name must be less than 260 characters, and the directory "
					"name must be less than 248 characters.";
			default:
			{
				wchar_t text[512] = {};
				const DWORD n = FormatMessageW(FORMAT_MESSAGE_FROM_SYSTEM | FORMAT_MESSAGE_IGNORE_INSERTS, nullptr, error, 0, text, 511, nullptr);
				return n > 0 ? Utf8Of(Text16(text, n)) : "Unknown error " + std::to_string((int)error) + ".";
			}
		}
	}

	// The file's last write time (FILETIME, UTC); 0 (1601-01-01, .NET's answer) when it cannot be read.
	uint64_t LastWriteTime(const Text16& path)
	{
		WIN32_FILE_ATTRIBUTE_DATA data;
		if (!GetFileAttributesExW(path.c_str(), GetFileExInfoStandard, &data))
			return 0;
		return ((uint64_t)data.ftLastWriteTime.dwHighDateTime << 32) | data.ftLastWriteTime.dwLowDateTime;
	}

	bool FileExists(const Text16& path)
	{
		const DWORD attributes = path.empty() ? INVALID_FILE_ATTRIBUTES : GetFileAttributesW(path.c_str());
		return attributes != INVALID_FILE_ATTRIBUTES && (attributes & FILE_ATTRIBUTE_DIRECTORY) == 0;
	}

	// NinjaTrader's ReadLimited (NT:1285-1303): shared read, at most 1 MB, UTF-8 or the encoding of a byte
	// order mark (StreamReader's detection). False with .NET's message.
	bool ReadLimited(const std::string& path, std::string& text, std::string& error)
	{
		const Text16 wide = Utf16Of(path);
		HANDLE file = CreateFileW(wide.c_str(), GENERIC_READ, FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE, nullptr, OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL,
			nullptr);
		if (file == INVALID_HANDLE_VALUE)
		{
			error = IoErrorMessage(GetLastError(), path);
			return false;
		}
		// Files only, as .NET's FileStream (its message): a read from a named pipe or a device (\\.\pipe\..., COM1,
		// CON) can wait forever, and this runs on Sierra Chart's chart thread.
		if (GetFileType(file) != FILE_TYPE_DISK)
		{
			CloseHandle(file);
			error = "FileStream was asked to open a device that was not a file. For support for devices like 'com1:' or 'lpt1:', call CreateFile, then use the "
				"FileStream constructors that take an OS handle as an IntPtr.";
			return false;
		}
		const char* const tooLarge = "Levels file exceeds 1 MB.";
		LARGE_INTEGER size;
		if (GetFileSizeEx(file, &size) && size.QuadPart > 1048576)
		{
			CloseHandle(file);
			error = tooLarge;
			return false;
		}
		// Keep enforcing the limit if another process grows the file after the size check.
		std::string bytes;
		char buffer[65536];
		DWORD read = 0;
		bool ok = true;
		while ((ok = ReadFile(file, buffer, sizeof(buffer), &read, nullptr) != 0) && read > 0)
		{
			bytes.append(buffer, read);
			if (bytes.size() > 4 * 1048576)
				break;
		}
		const DWORD readError = ok ? 0 : GetLastError();
		CloseHandle(file);
		if (!ok)
		{
			error = IoErrorMessage(readError, path);
			return false;
		}
		Text16 decoded;
		const unsigned char* b = (const unsigned char*)bytes.data();
		const size_t n = bytes.size();
		auto utf16 = [&decoded, b, n](size_t from, bool big)
		{
			for (size_t i = from; i + 1 < n; i += 2)
				decoded += (wchar_t)(big ? (b[i] << 8) | b[i + 1] : b[i] | (b[i + 1] << 8));
			if ((n - from) % 2 != 0)
				decoded += (wchar_t)0xFFFD;
		};
		auto utf32 = [&decoded, b, n](size_t from, bool big)
		{
			for (size_t i = from; i + 3 < n; i += 4)
			{
				const uint32_t c = big ? ((uint32_t)b[i] << 24) | ((uint32_t)b[i + 1] << 16) | ((uint32_t)b[i + 2] << 8) | b[i + 3]
					: b[i] | ((uint32_t)b[i + 1] << 8) | ((uint32_t)b[i + 2] << 16) | ((uint32_t)b[i + 3] << 24);
				if (c >= 0x10000 && c <= 0x10FFFF)
				{
					decoded += (wchar_t)(0xD800 + ((c - 0x10000) >> 10));
					decoded += (wchar_t)(0xDC00 + ((c - 0x10000) & 0x3FF));
				}
				else
					decoded += (wchar_t)(c > 0x10FFFF || (c >= 0xD800 && c <= 0xDFFF) ? 0xFFFD : c);
			}
		};
		if (n >= 4 && b[0] == 0xFF && b[1] == 0xFE && b[2] == 0 && b[3] == 0)
			utf32(4, false);
		else if (n >= 4 && b[0] == 0 && b[1] == 0 && b[2] == 0xFE && b[3] == 0xFF)
			utf32(4, true);
		else if (n >= 2 && b[0] == 0xFF && b[1] == 0xFE)
			utf16(2, false);
		else if (n >= 2 && b[0] == 0xFE && b[1] == 0xFF)
			utf16(2, true);
		else
			decoded = Utf16Of(n >= 3 && b[0] == 0xEF && b[1] == 0xBB && b[2] == 0xBF ? bytes.substr(3) : bytes);
		if (decoded.size() > 1048576)
		{
			error = tooLarge;
			return false;
		}
		text = Utf8Of(decoded);
		return true;
	}

	// UTC seconds since Sierra Chart's base date of a FILETIME.
	int64_t UtcSecondsOf(uint64_t fileTime)
	{
		return (int64_t)(fileTime / 10000000ull) - 11644473600LL + (int64_t)SIERRA_UNIX_DATE * SECONDS_DAY;
	}

	// NinjaTrader's last-good levels source (NT:1242-1356): the file named by the template (or the paste
	// box), the last valid document, its revision, and the notices. Each instance is NinjaTrader's one
	// LevelFileSource of a chart load.
	struct LevelFileSource
	{
		LevelsDocument	Current;
		std::string		ResolvedPath, Error, CacheWarning, CachePath;
		int				Revision		= 0;
		double			ReferencePrice	= NaN;	// the chart price that catches another symbol's levels; NaN skips the check
		std::function<CtTime(int64_t)>	ToCt;		// UTC seconds since the base date -> CT (NinjaTrader's TimeZoneInfo)
		std::function<void()>			AfterRead;	// tests: runs between the read and the second time check

		// NinjaTrader's ResolvePath (NT:1251-1258): .NET's checks and messages.
		static bool ResolvePath(const std::string& templateText, const std::string& root, std::string& path, std::string& error)
		{
			bool rootOk = !root.empty();
			for (char c : root)
				rootOk = rootOk && ((c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') || c == '_' || c == '-');
			if (!rootOk)
			{
				error = "Unsupported instrument root in levels path.";
				return false;
			}
			Text16 value = TrimChars(TrimNet(Utf16Of(templateText)), L"\"");
			if (!value.empty())
			{
				const DWORD needed = ExpandEnvironmentStringsW(value.c_str(), nullptr, 0);
				if (needed > 0)
				{
					Text16 expanded((size_t)needed, L'\0');
					const DWORD written = ExpandEnvironmentStringsW(value.c_str(), &expanded[0], needed);
					if (written > 0 && written <= needed)
					{
						expanded.resize(written - 1);
						value = expanded;
					}
				}
			}
			// {root}, any case.
			const Text16 wideRoot = Utf16Of(root);
			Text16 replaced;
			for (size_t i = 0; i < value.size();)
				if (LiteralAt(value, i, L"{root}"))
				{
					replaced += wideRoot;
					i += 6;
				}
				else
					replaced += value[i++];
			value = replaced;
			const char* const illegal = "Illegal characters in path.";
			for (wchar_t c : value)
				if (c == L'"' || c == L'<' || c == L'>' || c == L'|' || c < 32)
				{
					error = illegal;
					return false;
				}
			if (!(value.size() >= 1 && (value[0] == L'\\' || value[0] == L'/')) && !(value.size() >= 2 && value[1] == L':'))
			{
				error = "Use a full path for the levels file.";
				return false;
			}
			for (wchar_t c : value)
				if (c == L'*' || c == L'?')
				{
					error = illegal;
					return false;
				}
			const bool letter = (value[0] >= L'A' && value[0] <= L'Z') || (value[0] >= L'a' && value[0] <= L'z');
			if (value[0] == L':' || (value.size() >= 2 && value[1] == L':' && !letter) || (value.size() > 2 && value.find(L':', 2) != Text16::npos))
			{
				error = "The given path's format is not supported.";
				return false;
			}
			const DWORD needed = GetFullPathNameW(value.c_str(), 0, nullptr, nullptr);
			Text16 full((size_t)(std::max)((DWORD)1, needed), L'\0');
			const DWORD written = needed > 0 ? GetFullPathNameW(value.c_str(), needed, &full[0], nullptr) : 0;
			if (written == 0 || written >= needed)
			{
				error = IoErrorMessage(GetLastError(), Utf8Of(value));
				return false;
			}
			full.resize(written);
			// Short (8.3) names are expanded, as .NET does when the path holds a '~' (the part that exists).
			if (full.find(L'~') != Text16::npos)
			{
				Text16 head = full, tail;
				while (!head.empty())
				{
					wchar_t longPath[32768];
					const DWORD length = GetLongPathNameW(head.c_str(), longPath, 32768);
					if (length > 0 && length < 32768)
					{
						full = Text16(longPath, length) + tail;
						break;
					}
					const size_t slash = head.find_last_of(L"\\/");
					if (slash == Text16::npos || slash == 0)
						break;
					tail = head.substr(slash) + tail;
					head = head.substr(0, slash);
				}
			}
			if (full.size() >= 260)
			{
				error = IoErrorMessage(ERROR_FILENAME_EXCED_RANGE, "");
				return false;
			}
			path = Utf8Of(full);
			return true;
		}

		// Initialize (NT:1259-1283): the paste box alone without a template; else the paste as a fallback, the
		// file's last-good cache, then the file.
		void Initialize(const std::string& templateText, const std::string& root, const std::string& paste, const std::string& cacheDirectory)
		{
			rootName = root;
			LevelsDocument pasted;
			std::string error;
			const bool parsed = LevelsDocument::Parse(paste, true, pasted, error);
			if (TrimNet(Utf16Of(templateText)).empty())
			{
				if (parsed)
					error = Accept(pasted);
				Error = error.empty() ? std::string() : "Pasted levels rejected; no daily levels loaded. " + error;
				return;
			}
			// A valid pasted block is a fallback when no file/cache has ever loaded.
			if (parsed)
				Accept(pasted);
			std::string resolved;
			if (!ResolvePath(templateText, root, resolved, error))
			{
				Error = "Levels file unavailable; " + Retained() + " " + error;
				return;
			}
			ResolvedPath = resolved;
			if (!cacheDirectory.empty())
			{
				const Text16 key = UpperInvariant(Utf16Of(root + "|" + ResolvedPath));
				char name[24];
				snprintf(name, sizeof(name), "%016llX", (unsigned long long)Fnv1a64(FNV64_BASIS, Utf8Of(key).data(), Utf8Of(key).size()));
				const char last = cacheDirectory.back();
				CachePath = cacheDirectory + (last == '\\' || last == '/' ? "" : "\\") + name + ".txt";
				if (FileExists(Utf16Of(CachePath)))
				{
					std::string text, problem;
					LevelsDocument cached;
					if (!ReadLimited(CachePath, text, problem) || !LevelsDocument::Parse(text, false, cached, problem) || !(problem = Accept(cached)).empty())
						CacheWarning = "Last-good cache not used: " + problem;
				}
			}
			Refresh();
		}

		// Refresh (NT:1320-1335): true when the levels changed.
		bool Refresh()
		{
			if (ResolvedPath.empty())
				return false;
			const int before = Revision;
			const Text16 wide = Utf16Of(ResolvedPath);
			std::string text, error;
			LevelsDocument document;
			const uint64_t written = LastWriteTime(wide);
			if (ReadLimited(ResolvedPath, text, error) && LevelsDocument::Parse(text, false, document, error))
			{
				if (AfterRead)
					AfterRead();
				if (written != LastWriteTime(wide))
					error = "File changed while being read; retrying on the next refresh.";
				else
				{
					if (!document.HasDate)
					{
						document.HasDate = true;
						document.Date = TradingDate(ToCt ? ToCt(UtcSecondsOf(written)) : UtcSecondsOf(written));
					}
					error = Accept(document);
				}
			}
			if (!error.empty())
				Error = "Levels file rejected; " + Retained() + " " + error;
			else
			{
				Error.clear();
				if (before != Revision || !FileExists(Utf16Of(CachePath)))
					SaveCache();
			}
			return Revision != before;
		}

		// Warning (NT:1349-1355): STALE when the levels' date is before the chart's trading date (a later date
		// is normal: the 16:45 Globex publish carries the next trading date), then the error and the cache's.
		std::string Warning(int tradingDate) const
		{
			const std::string stale = Current.HasDate && Current.Date < tradingDate
				? "STALE LEVELS: levels date " + IsoDate(Current.Date) + "; chart trading date " + IsoDate(tradingDate) + "." : std::string();
			return Utf8Of(TrimNet(Utf16Of(stale + " " + Error + " " + CacheWarning)));
		}

	private:
		std::string	rootName, signature;

		std::string Retained() const
		{
			return !Current.Levels.empty() ? "last valid levels retained." : "structure features remain active without daily levels.";
		}

		static Text16 UpperInvariant(const Text16& text)
		{
			if (text.empty())
				return text;
			Text16 out(text.size(), L'\0');
			const int n = LCMapStringEx(LOCALE_NAME_INVARIANT, LCMAP_UPPERCASE, text.c_str(), (int)text.size(), &out[0], (int)out.size(), nullptr, nullptr, 0);
			return n == (int)text.size() ? out : text;
		}

		// Validate (NT:1312-1319): the wrong-symbol guards. NinjaTrader's message, or "".
		std::string Validate(const LevelsDocument& document) const
		{
			if (document.HasSymbol && !rootName.empty())
			{
				const std::string a = Upper(MathEx::LevelsRoot(document.Symbol)), b = Upper(rootName);
				if (a != b)
					return "Levels are for " + document.Symbol + "; this chart reads " + rootName + " levels.";
			}
			for (const Level& l : document.Levels)
				if (l.Kind == 0)
				{
					if (Valid(ReferencePrice) && ReferencePrice > 0 && std::fabs(l.Price / ReferencePrice - 1) > .2)
						return "Pivot " + NetDouble::Format(l.Price, false) + " is more than 20% from the chart price " + NetDouble::Format(ReferencePrice, false)
							+ "; these look like another symbol's levels.";
					break;
				}
			return std::string();
		}

		std::string Accept(const LevelsDocument& document)
		{
			const std::string problem = Validate(document);
			if (!problem.empty())
				return problem;
			const std::string next = document.Serialize();
			if (next == signature)
				return std::string();
			Current = document;
			signature = next;
			Revision++;
			return std::string();
		}

		static bool CreateDirectories(const Text16& directory)
		{
			if (directory.empty())
				return false;
			const DWORD attributes = GetFileAttributesW(directory.c_str());
			if (attributes != INVALID_FILE_ATTRIBUTES)
				return (attributes & FILE_ATTRIBUTE_DIRECTORY) != 0;
			const size_t slash = directory.find_last_of(L"\\/");
			if (slash != Text16::npos && slash > 2)
				CreateDirectories(directory.substr(0, slash));
			return CreateDirectoryW(directory.c_str(), nullptr) != 0 || GetLastError() == ERROR_ALREADY_EXISTS;
		}

		// SaveCache (NT:1336-1348): a temporary file replaced into place.
		void SaveCache()
		{
			if (CachePath.empty())
				return;
			static unsigned counter = 0;
			char unique[48];
			snprintf(unique, sizeof(unique), ".%08lX%016llX%04X.tmp", (unsigned long)GetCurrentProcessId(), (unsigned long long)GetTickCount64(), ++counter & 0xFFFF);
			const Text16 cache = Utf16Of(CachePath), temp = Utf16Of(CachePath + unique);
			bool ok = false;
			const size_t slash = cache.find_last_of(L"\\/");
			if (slash != Text16::npos && CreateDirectories(cache.substr(0, slash)))
			{
				HANDLE file = CreateFileW(temp.c_str(), GENERIC_WRITE, 0, nullptr, CREATE_NEW, FILE_ATTRIBUTE_NORMAL, nullptr);
				if (file != INVALID_HANDLE_VALUE)
				{
					const std::string text = Current.Serialize();
					DWORD written = 0;
					ok = WriteFile(file, text.data(), (DWORD)text.size(), &written, nullptr) != 0 && written == (DWORD)text.size();
					ok = CloseHandle(file) != 0 && ok;
					if (ok)
						ok = FileExists(cache) ? ReplaceFileW(cache.c_str(), temp.c_str(), nullptr, REPLACEFILE_WRITE_THROUGH, nullptr, nullptr) != 0
							: MoveFileExW(temp.c_str(), cache.c_str(), MOVEFILE_WRITE_THROUGH) != 0;
				}
			}
			CacheWarning = ok ? std::string() : "Levels loaded; last-good cache could not be saved.";
			if (GetFileAttributesW(temp.c_str()) != INVALID_FILE_ATTRIBUTES)
				DeleteFileW(temp.c_str());
		}
	};

	// ---- Discord webhook (spec D; NinjaTrader's DiscordAlerts, NT:1416-1559) ----

	bool AsciiEqualsIgnoreCase(const Text16& a, const wchar_t* b)
	{
		if (a.size() != wcslen(b))
			return false;
		for (size_t i = 0; i < a.size(); i++)
		{
			const wchar_t x = a[i] >= L'A' && a[i] <= L'Z' ? (wchar_t)(a[i] + 32) : a[i];
			if (x != b[i])
				return false;
		}
		return true;
	}

	// NinjaTrader's ValidateEndpoint (NT:1442-1450): an absolute https URI on discord.com with the default
	// port, no user info and no fragment, whose path is a webhook's; the endpoint is rebuilt from those
	// parts plus ?wait=true and a numeric thread_id. The parts .NET's Uri gives it are reproduced here
	// (measured against NinjaTrader's code): ASCII case-insensitive scheme and host, port 443 written
	// any way, "\" in the path as "/", dot segments removed and trailing dots of a segment dropped, %2E as
	// a dot; any other escape, character or user info rejects (an empty user info "@" is kept, as .NET's
	// GetLeftPart keeps it). Nothing the user typed reaches the request but the path's letters, digits,
	// "-", "_" and "/" and the thread's digits.
	bool ValidateDiscordEndpoint(const std::string& url, std::string& endpoint, std::string& error)
	{
		error = "Use an HTTPS discord.com webhook URL from the channel's Integrations settings.";
		const Text16 s = TrimNet(Utf16Of(url));
		if (s.size() < 8 || !AsciiEqualsIgnoreCase(s.substr(0, 5), L"https") || s.compare(5, 3, L"://") != 0)
			return false;
		const size_t end = s.find_first_of(L"/?#\\", 8);
		if (end == Text16::npos || s[end] != L'/')
			return false;
		Text16 authority = s.substr(8, end - 8);
		const bool emptyUser = !authority.empty() && authority[0] == L'@';
		if (emptyUser)
			authority = authority.substr(1);
		if (authority.find(L'@') != Text16::npos)
			return false;
		const size_t colon = authority.find(L':');
		if (!AsciiEqualsIgnoreCase(authority.substr(0, colon), L"discord.com"))
			return false;
		if (colon != Text16::npos)
		{
			const Text16 port = authority.substr(colon + 1);
			long long value = 0;
			for (wchar_t c : port)
			{
				if (c < L'0' || c > L'9')
					return false;
				value = (std::min)(value * 10 + (c - L'0'), 1000000LL);
			}
			if (!port.empty() && value != 443)
				return false;
		}
		const size_t q = s.find_first_of(L"?#", end);
		Text16 path = s.substr(end, q == Text16::npos ? Text16::npos : q - end), query;
		if (q != Text16::npos)
		{
			if (s[q] == L'#')
				return false;
			const size_t hash = s.find(L'#', q);
			if (hash != Text16::npos)
				return false;
			query = s.substr(q);
		}
		for (wchar_t& c : path)
			c = c == L'\\' ? L'/' : c;
		for (wchar_t c : path)
			if (!((c >= L'a' && c <= L'z') || (c >= L'A' && c <= L'Z') || (c >= L'0' && c <= L'9') || c == L'_' || c == L'-' || c == L'.' || c == L'/' || c == L'%'))
				return false;
		// The segments after the first "/": dot segments (".", "..", or only dots), trailing dots dropped.
		std::vector<Text16> segments, output;
		for (size_t from = 1;;)
		{
			const size_t slash = path.find(L'/', from);
			segments.push_back(path.substr(from, slash == Text16::npos ? Text16::npos : slash - from));
			if (slash == Text16::npos)
				break;
			from = slash + 1;
		}
		for (size_t k = 0; k < segments.size(); k++)
		{
			Text16 segment;
			for (size_t i = 0; i < segments[k].size(); i++)
				if (segments[k][i] == L'%' && i + 2 < segments[k].size() && segments[k][i + 1] == L'2' && (segments[k][i + 2] == L'e' || segments[k][i + 2] == L'E'))
				{
					segment += L'.';
					i += 2;
				}
				else
					segment += segments[k][i];
			if (segment.find(L'%') != Text16::npos)
				return false;
			const bool last = k + 1 == segments.size();
			const bool dots = !segment.empty() && segment.find_first_not_of(L'.') == Text16::npos;
			if (segment == L"..")
			{
				if (!output.empty())
					output.pop_back();
				if (last)
					output.push_back(Text16());
				continue;
			}
			if (dots)
			{
				if (last)
					output.push_back(Text16());
				continue;
			}
			while (!segment.empty() && segment.back() == L'.')
				segment.pop_back();
			output.push_back(segment);
		}
		Text16 canonical;
		for (const Text16& segment : output)
			canonical += L"/" + segment;
		if (canonical.empty())
			canonical = L"/";
		// ^/api/(?:v\d+/)?webhooks/\d+/[A-Za-z0-9_-]+$
		auto digitsAt = [&canonical](size_t& i)
		{
			const size_t from = i;
			while (i < canonical.size() && canonical[i] >= L'0' && canonical[i] <= L'9')
				i++;
			return i > from;
		};
		size_t i = 0;
		if (canonical.compare(0, 5, L"/api/") != 0)
			return false;
		i = 5;
		if (i < canonical.size() && canonical[i] == L'v')
		{
			size_t j = i + 1;
			if (digitsAt(j) && j < canonical.size() && canonical[j] == L'/')
				i = j + 1;
		}
		if (canonical.compare(i, 9, L"webhooks/") != 0)
			return false;
		i += 9;
		if (!digitsAt(i) || i >= canonical.size() || canonical[i] != L'/')
			return false;
		i++;
		if (i >= canonical.size())
			return false;
		for (; i < canonical.size(); i++)
		{
			const wchar_t c = canonical[i];
			if (!((c >= L'a' && c <= L'z') || (c >= L'A' && c <= L'Z') || (c >= L'0' && c <= L'9') || c == L'_' || c == L'-'))
				return false;
		}
		// (?:^\?|&)thread_id=(\d+)(?:&|$) in the query: the first match.
		std::string thread;
		for (size_t at = query.find(L"thread_id="); at != Text16::npos && thread.empty(); at = query.find(L"thread_id=", at + 1))
		{
			if (!(at == 1 && query[0] == L'?') && !(at > 0 && query[at - 1] == L'&'))
				continue;
			size_t j = at + 10;
			const size_t from = j;
			while (j < query.size() && query[j] >= L'0' && query[j] <= L'9')
				j++;
			if (j > from && (j == query.size() || query[j] == L'&'))
				thread = Utf8Of(query.substr(from, j - from));
		}
		endpoint = std::string("https://") + (emptyUser ? "@" : "") + "discord.com" + Utf8Of(canonical) + "?wait=true" + (thread.empty() ? "" : "&thread_id=" + thread);
		error.clear();
		return true;
	}

	// The URL the study posts to for a validated endpoint (FIX, spec D.3 review): Discord's API version 10, whatever
	// version the pasted URL names. Discord routes a URL without a version (the form Copy Webhook URL gives) to its
	// default version, v6, whose 429 answer gives retry_after in milliseconds; from v8 on it is seconds. NinjaTrader
	// reads the Retry-After header, seconds in every version, but Sierra Chart gives the study only the answer's
	// body, so the version is fixed here, where the unit is documented (the same webhook in every version). Built
	// from the webhook's id, token and thread id only: no user info ("https://@discord.com", which NinjaTrader's
	// URL keeps), so one webhook pasted in different forms is one URL and shares one pacing gate.
	std::string DiscordRequestUrl(const std::string& endpoint)
	{
		const size_t at = endpoint.find("/webhooks/");
		return at == std::string::npos ? std::string() : "https://discord.com/api/v10" + endpoint.substr(at);
	}

	// NinjaTrader's Payload (NT:1451-1463): the text cut to 1900 UTF-16 units, JSON-escaped (quotes and
	// backslashes, control characters and every surrogate as \uxxxx), mentions disabled. FIX G8: the cut
	// never splits a surrogate pair (NinjaTrader's can leave a lone surrogate); it cuts before the pair.
	std::string DiscordPayload(const std::string& textUtf8)
	{
		Text16 text = Utf16Of(textUtf8);
		if (text.size() > 1900)
			text.resize((text[1899] & 0xFC00) == 0xD800 ? 1899 : 1900);
		Text16 b = L"{\"allowed_mentions\":{\"parse\":[]},\"content\":\"";
		for (wchar_t c : text)
		{
			if (c == L'"' || c == L'\\')
			{
				b += L'\\';
				b += c;
			}
			else if (c < 32 || (c >= 0xD800 && c <= 0xDFFF))
			{
				wchar_t escape[8];
				swprintf(escape, 8, L"\\u%04x", (unsigned)c);
				b += escape;
			}
			else
				b += c;
		}
		b += L"\"}";
		return Utf8Of(b);
	}

	// The top-level members of a JSON object, each value's text (a string's without its quotes).
	bool JsonMembers(const std::string& json, std::map<std::string, std::string>& members)
	{
		size_t i = 0;
		const size_t n = json.size();
		auto space = [&]() { while (i < n && (json[i] == ' ' || json[i] == '\t' || json[i] == '\r' || json[i] == '\n')) i++; };
		auto readString = [&](std::string& out)
		{
			if (i >= n || json[i] != '"')
				return false;
			for (i++; i < n && json[i] != '"'; i++)
			{
				if (json[i] == '\\' && i + 1 < n)
					i++;
				out += json[i];
			}
			if (i >= n)
				return false;
			i++;
			return true;
		};
		space();
		if (i >= n || json[i] != '{')
			return false;
		i++;
		space();
		if (i < n && json[i] == '}')
			return true;
		while (i < n)
		{
			std::string key, value;
			space();
			if (!readString(key))
				return false;
			space();
			if (i >= n || json[i] != ':')
				return false;
			i++;
			space();
			if (i < n && json[i] == '"')
			{
				if (!readString(value))
					return false;
			}
			else
			{
				const size_t from = i;
				int depth = 0;
				for (; i < n; i++)
				{
					const char c = json[i];
					if (c == '"')
					{
						std::string skipped;
						if (!readString(skipped))
							return false;
						i--;
					}
					else if (c == '{' || c == '[')
						depth++;
					else if (c == '}' || c == ']')
					{
						if (depth == 0)
							break;
						depth--;
					}
					else if (c == ',' && depth == 0)
						break;
				}
				value = Trim(json.substr(from, i - from));
			}
			members[key] = value;
			space();
			if (i < n && json[i] == ',')
			{
				i++;
				continue;
			}
			return i < n && json[i] == '}';
		}
		return false;
	}

	// What sends one request: Sierra Chart's sc.MakeHTTPPOSTRequest in the study, a recorder in the tests
	// (NinjaTrader's testTransport seam, NT:1433). The request id, 0 when it could not be sent.
	struct DiscordTransport
	{
		virtual int Post(const std::string& url, const std::string& body) = 0;

	protected:
		~DiscordTransport() = default;
	};

	// The pacing gate of one webhook, shared by every study instance in the DLL (NT:1419-1421): at least
	// 500 ms between posts, pushed back by a 429.
	struct DiscordGate
	{
		int			Users	= 0;
		uint64_t	NextMs	= 0;
	};

	SRWLOCK g_DiscordGatesLock = SRWLOCK_INIT;

	std::map<std::string, DiscordGate>& DiscordGates()
	{
		static std::map<std::string, DiscordGate> gates;
		return gates;
	}

	const char* const DISCORD_CONNECTION_ERROR = "Discord notification not delivered (network timeout or connection error). Native alerts remain active.";

	// NinjaTrader's sender (NT:1464-1526) on Sierra Chart's call model (spec D.3): a queue of 32 payloads,
	// one request in flight, pumped on every study call. sc.MakeHTTPPOSTRequest gives no HTTP status, so
	// the response body decides: "channel_id" delivered (?wait=true returns the message), "retry_after" or
	// a rate-limit page a 429 (the gate pushed back, one resend), Discord's "code" an error, an empty body
	// or Sierra Chart's HTTP_REQUEST_ERROR a connection error, Sierra Chart's "ERROR" an HTTP or connection
	// error; no answer in 15 s is a timeout and that request's late answer is ignored. Sierra Chart runs one
	// request of a study at a time (its documentation), so the next post waits for the open request's answer
	// (at most 60 s). Failures are never resent (they could duplicate a message). The URL is never logged or
	// shown.
	class DiscordSender
	{
	public:
		explicit DiscordSender(const std::string& endpoint) : Endpoint(endpoint)
		{
			AcquireSRWLockExclusive(&g_DiscordGatesLock);
			DiscordGates()[Endpoint].Users++;
			ReleaseSRWLockExclusive(&g_DiscordGatesLock);
		}

		~DiscordSender()
		{
			AcquireSRWLockExclusive(&g_DiscordGatesLock);
			auto found = DiscordGates().find(Endpoint);
			if (found != DiscordGates().end() && --found->second.Users <= 0)
				DiscordGates().erase(found);
			ReleaseSRWLockExclusive(&g_DiscordGatesLock);
		}

		DiscordSender(const DiscordSender&) = delete;
		DiscordSender& operator=(const DiscordSender&) = delete;

		const std::string	Endpoint;
		std::string			Warning;
		int					Posts		= 0;	// diagnostics
		int					Delivered	= 0;

		void Enqueue(const std::string& text)
		{
			if (queue.size() >= 32)
			{
				Warning = "Discord queue full; notification dropped.";
				return;
			}
			queue.push_back(DiscordPayload(text));
		}

		bool Busy() const { return !queue.empty() || hasCurrent || pending != 0; }
		size_t Queued() const { return queue.size(); }
		int Pending() const { return pending; }

		// A sender replacing another (a changed URL or switch) takes over the request the old one still has
		// open in Sierra Chart: its answer is not this sender's, and this sender's first post waits for it.
		void Adopt(const DiscordSender& old)
		{
			if (old.pending == 0)
				return;
			pending		= old.pending;
			sentAt		= old.sentAt;
			detached	= true;
			late		= old.late;
			lastAnswer	= old.lastAnswer;
		}

		// One study call: the response (sc.HTTPRequestID, sc.HTTPResponse), the timeout, the next post.
		void Pump(uint64_t nowMs, int responseId, const std::string& response, DiscordTransport& transport)
		{
			// While a request is open, an answer is its answer: by its id when Sierra Chart's sc.HTTPRequestID is the
			// value sc.MakeHTTPPOSTRequest returned, and also when it is not (Sierra Chart documents that call as
			// returning 1 for any success; only sc.MakeHTTPBinaryRequest is documented to return the id), but never an
			// id answered before (sc.HTTPRequestID left over from an earlier answer) or given up on.
			if (responseId != 0)
			{
				if (pending != 0 && (responseId == pending || (responseId != lastAnswer && late.count(responseId) == 0)))
				{
					const bool mine = !detached;
					pending		= 0;
					detached	= false;
					lastAnswer	= responseId;
					if (mine)
						Classify(nowMs, response);
				}
				else
					late.erase(responseId);		// the late answer of a request given up on: ignored
			}
			// No answer in 15 s: a connection error, never resent (NinjaTrader's 5 s timeout). Its answer may still
			// come, and Sierra Chart runs one request at a time, so the next post waits for it, 60 s at most.
			if (pending != 0 && !detached && nowMs - sentAt >= 15000)
			{
				detached	= true;
				hasCurrent	= false;
				Warning		= DISCORD_CONNECTION_ERROR;
			}
			if (pending != 0 && nowMs - sentAt >= 60000)
			{
				late.insert(pending);
				while (late.size() > 64)
					late.erase(late.begin());
				pending		= 0;
				detached	= false;
			}
			if (pending != 0)
				return;
			if (!hasCurrent && !queue.empty())
			{
				current = queue.front();
				queue.pop_front();
				hasCurrent = true;
				attempt = 0;
			}
			if (!hasCurrent)
				return;
			bool open = false;
			AcquireSRWLockExclusive(&g_DiscordGatesLock);
			DiscordGate& gate = DiscordGates()[Endpoint];
			if (gate.NextMs <= nowMs)
			{
				gate.NextMs = nowMs + 500;
				open = true;
			}
			ReleaseSRWLockExclusive(&g_DiscordGatesLock);
			if (!open)
				return;
			Posts++;
			const int id = transport.Post(Endpoint, current);
			if (id == 0)
			{
				hasCurrent = false;
				Warning = DISCORD_CONNECTION_ERROR;
				return;
			}
			pending = id;
			sentAt = nowMs;
			detached = false;
		}

	private:
		std::deque<std::string>	queue;
		std::string				current;
		bool					hasCurrent	= false;
		int						attempt		= 0;
		int						pending		= 0;		// the open request's id (0: none)
		bool					detached	= false;	// its answer is not reported (timed out, or adopted)
		uint64_t				sentAt		= 0;
		int						lastAnswer	= 0;		// sc.HTTPRequestID of the last answer taken
		std::set<int>			late;					// requests given up on after 60 s

		// Later posts to this webhook wait until `nowMs + seconds` (NinjaTrader's gate after a 429).
		void Delay(uint64_t nowMs, double seconds)
		{
			AcquireSRWLockExclusive(&g_DiscordGatesLock);
			DiscordGate& gate = DiscordGates()[Endpoint];
			const uint64_t until = nowMs + (uint64_t)(seconds * 1000);
			if (until > gate.NextMs)
				gate.NextMs = until;
			ReleaseSRWLockExclusive(&g_DiscordGatesLock);
		}

		void Classify(uint64_t nowMs, const std::string& response)
		{
			const std::string body = Trim(response);
			if (body.empty() || body == "HTTP_REQUEST_ERROR" || body == "EMPTY_RESPONSE")
			{
				hasCurrent = false;
				Warning = DISCORD_CONNECTION_ERROR;
				return;
			}
			// Sierra Chart's answer when the request failed or the server answered with an error status (its
			// documentation): a connection problem or any HTTP error, a 429 among them, which it does not tell
			// apart. Not resent (it could duplicate a message); later posts wait NinjaTrader's default Retry-After
			// (2 s) in case it was a rate limit.
			if (body == "ERROR")
			{
				hasCurrent = false;
				Delay(nowMs, 2);
				Warning = "Discord notification not delivered (HTTP or connection error). Native alerts remain active.";
				return;
			}
			std::map<std::string, std::string> members;
			const bool json = JsonMembers(body, members);
			if (json && members.count("channel_id") != 0)
			{
				hasCurrent = false;
				Warning.clear();
				Delivered++;
				return;
			}
			std::string lower = body;
			for (char& c : lower)
				c = c >= 'A' && c <= 'Z' ? (char)(c + 32) : c;
			if ((json && members.count("retry_after") != 0) || (!json && lower.find("rate limited") != std::string::npos))
			{
				// NinjaTrader's Retry-After seconds (2 when absent), clamped to 1-60 for the gate; resent once.
				// retry_after is in seconds because the request names API v10 (DiscordRequestUrl).
				double retry = 2;
				if (json && members.count("retry_after") != 0 && !NetDouble::TryParse(Utf16Of(members["retry_after"]), retry))
					retry = 2;
				if (!(retry == retry))
					retry = 2;
				Delay(nowMs, (std::max)(1.0, (std::min)(60.0, retry)));
				Warning = "Discord rate limited; notifications delayed.";
				if (attempt == 0 && retry <= 60)
				{
					attempt = 1;
					return;
				}
				hasCurrent = false;
				Warning = "Discord notification not delivered (HTTP 429). Native alerts remain active.";
				return;
			}
			hasCurrent = false;
			std::string code;
			for (char c : json && members.count("code") != 0 ? members["code"] : std::string())
				if (code.size() < 16 && ((c >= '0' && c <= '9') || (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || c == '_'))
					code += c;
			if (!code.empty())
				Warning = "Discord notification not delivered (Discord error " + code + "). Native alerts remain active.";
			else
				Warning = "Discord notification not delivered (unexpected response). Native alerts remain active.";
		}
	};

	// A drawn line (NT:501-504). Name is NinjaTrader's name, the internal id (spec B.0.8): the label
	// text is the matching subgraph's Name, resolved when drawn.
	struct LineItem
	{
		std::string	Name;
		std::string	Group;
		double		Price		= 0;
		CtTime		Start		= 0;
		CtTime		End			= 0;
		uint32_t	Color		= 0;
		int			Width		= 1;
		int			Offset		= 2;
		std::string	Style		= "Solid";
		std::string	Size		= "Normal";
		std::string	Extend		= "None";
		bool		Label		= true;
		uint32_t	TextColor	= 0;
	};

	struct ZoneItem
	{
		double		Top			= 0;
		double		Bottom		= 0;
		CtTime		Start		= 0;
		CtTime		Created		= 0;
		uint32_t	Color		= 0;
		bool		Live		= false;
		uint32_t	BorderColor	= 0;
		int			BorderWidth	= 0;
		std::string	BorderStyle	= "Solid";
	};

	struct Naked
	{
		std::string	Kind;
		double		Price	= 0;
		CtTime		Start	= 0;
		int			Width	= 0;
	};

	struct Poor
	{
		double	Price	= 0;
		bool	High	= false;
		CtTime	Start	= 0;
		CtTime	Created	= 0;
	};

	struct TpoRow
	{
		int		Hits	= 0;
		int		Last	= 0;
		CtTime	First	= 0;
	};

	// A completed profile (NT:513). The engine never edits one after it is completed, so copies of
	// the engine share them. EndIndex: the chart bar that completed it; EndSeq: NinjaTrader's
	// EndIndex, that bar's Seq.
	struct PastProfile
	{
		std::shared_ptr<const Profile>	Data;
		ProfileStats					Stats;
		CtTime							Start		= 0;
		CtTime							End			= 0;
		int								EndIndex	= 0;
		int								EndSeq		= 0;
	};

	struct Notice
	{
		std::string	Key;
		std::string	Text;
	};

	struct LevelWatch
	{
		std::string	Name;
		double		Price		= 0;
		double		HalfWidth	= 0;
		bool		Enabled		= false;
		bool		Moving		= false;
	};

	// One processed bar's picture (NT:515-522). Profiles: the completed profiles in view and the
	// current one (Current), which the frame owns a copy of.
	struct FrameProfile
	{
		std::shared_ptr<const Profile>	Data;
		ProfileStats					Stats;
		CtTime							Start		= 0;
		CtTime							End			= 0;
		int								EndIndex	= 0;
		int								EndSeq		= 0;
		bool							Current		= false;
	};

	struct Frame
	{
		Bar							Bar;
		double						RthVwap		= 0;
		double						DailyAtr	= 0;
		std::vector<LevelWatch>		Watches;
		std::vector<Notice>			Notices;
		std::vector<LineItem>		Lines;
		std::vector<ZoneItem>		Zones;
		std::vector<FrameProfile>	Profiles;
		std::vector<std::string>	Labels;
		std::vector<std::string>	Values;
		std::vector<uint32_t>		Colors;
		std::string					Warning;
		bool						RuleActive		= false;
		bool						RuleConfirmed	= false;
		double						VaHigh			= 0;
		double						VaLow			= 0;
	};

	// ---- Settings (NinjaTrader's Settings, NT:56-329): every field with NinjaTrader's name and
	// default, so the engine's statements read as NinjaTrader's. Colors are NinjaTrader's ARGB. The
	// study fills it from its inputs and subgraphs (spec A.5); the tests and the oracle from text.

	struct Settings
	{
		bool tzguard_enable = true;
		std::string row_scale = "Auto";
		bool tick_auto = true;
		double tick_manual_val = 0.25;
		std::string layer_top_pick = "Daily Levels (All)";
		bool alertcap_enable = true;
		int alertcap_max = 30;
		int alertcap_window_min = 60;
		std::string lvl_text = "";
		uint32_t lvl_ip_color = 0xFFFDD835u;
		uint32_t lvl_bull_color = 0xFFF23645u;
		uint32_t lvl_bear_color = 0xFF4CAF50u;
		int lvl_thickness = 1;
		std::string lvl_style_in = "Dotted";
		std::string lvl_zone_style_in = "Solid";
		std::string lvl_text_size_opt = "large";
		int lvl_x_offset = 40;
		bool lvl_showLine = true;
		bool lvl_showZones = true;
		std::string lvl_zone_mode = "ATR %";
		double lvl_zone_atr_pct = 0.02;
		int lvl_zoneWidthTicks = 8;
		int lvl_zoneOpacity = 85;
		bool lvl_color_flip = true;
		double lvl_flip_atr = 0.05;
		uint32_t lvl_txt_c = 0x00FFFFFFu;
		bool lvl_alerts = false;
		bool lvl_alert_ip = true;
		bool lvl_alert_bull = true;
		bool lvl_alert_bear = true;
		bool mvp_master = true;
		std::string mvp_tf_mode = "Weekly";
		std::string mvp_sess_time = "0830-1500";
		double mvp_sess_dur = 6.5;
		std::string mvp_calc_tf = "1";
		double mvp_row_size = 0.25;
		double mvp_val_pct = 68.0;
		int mvp_profile_width = 50;
		bool mvp_align_right = true;
		int mvp_offset = 50;
		bool mvp_show_walls = false;
		bool mvp_use_auto_scale = true;
		double mvp_scale_start = 2.0;
		double mvp_scale_end = 1.5;
		bool mvp_extend_walls = true;
		int mvp_smooth_len = 2;
		double mvp_vol_mult = 2;
		int mvp_min_wall_dist = 40;
		int mvp_w_wall = 1;
		uint32_t mvp_c_wall_base = 0xFFE6B300u;
		int mvp_wall_transp = 25;
		uint32_t mvp_c_poc = 0xFF78909Cu;
		int mvp_poc_width = 2;
		uint32_t mvp_c_levels = 0xFF787B86u;
		int mvp_lvl_width = 2;
		uint32_t mvp_c_hist_va = 0xFF78909Cu;
		int mvp_hist_va_transp = 75;
		uint32_t mvp_c_hist_out = 0xFF787B86u;
		int mvp_hist_out_transp = 90;
		bool mvp_show_poc = true;
		bool mvp_show_vah = true;
		bool mvp_show_val = true;
		std::string mvp_poc_style = "Solid";
		std::string mvp_lvl_style = "Solid";
		std::string mvp_wall_style = "Solid";
		std::string mvp_lb_size = "Normal";
		uint32_t mvp_txt_c = 0x00FFFFFFu;
		bool mvp_use_cur_alerts = true;
		std::string mvp_alert_time = "0830-1500";
		bool macro_show_month = true;
		bool macro_show_poc = true;
		bool macro_show_hl = true;
		bool macro_alert_lvl = true;
		uint32_t macro_color = 0xFFFFFFFFu;
		uint32_t macro_poc_color = 0xFFFFFFFFu;
		int macro_width = 3;
		int macro_poc_width = 3;
		std::string macro_style = "Solid";
		std::string macro_poc_style = "Solid";
		int macro_offset = 2;
		std::string macro_text_size = "Normal";
		uint32_t macro_txt_c = 0x00FFFFFFu;
		bool ib_enable = true;
		bool ib_alert_ibh = true;
		bool ib_alert_ibl = true;
		std::string ib_session = "0830-0930";
		std::string ib_alert_time = "0830-1500";
		bool ib_show_mid = false;
		bool ib_show_labels = true;
		std::string ib_label_loc = "Right";
		std::string ib_label_size = "Normal";
		int ib_lbl_offset = 0;
		int ib_lvl_width = 1;
		uint32_t ib_col_hi = 0xFFFFCC80u;
		uint32_t ib_col_lo = 0xFFFFCC80u;
		uint32_t ib_col_mid = 0xFFFFCC80u;
		std::string ib_extend = "None";
		bool ib_limit_ext = true;
		std::string ib_stop_time = "0830-1515";
		std::string ib_style_main = "Solid";
		std::string ib_style_int = "Dotted";
		uint32_t ib_txt_c = 0x00FFFFFFu;
		bool vwap_enable = false;
		uint32_t vwap_col = 0xFFFFFFFFu;
		int vwap_width = 2;
		std::string vwap_style = "Solid";
		int vwap_start_h = 8;
		int vwap_start_m = 30;
		int vwap_end_h = 15;
		int vwap_end_m = 0;
		bool vwap_alert = false;
		bool cc_showOpen = false;
		uint32_t cc_c_open = 0xFF2196F3u;
		int cc_open_width = 1;
		int cc_open_offset = 3;
		std::string cc_open_style = "Solid";
		std::string cc_open_lb_size = "Normal";
		bool wk_showOpen = true;
		uint32_t wk_c_open = 0xFFFFFFFFu;
		int wk_open_width = 2;
		int wk_open_offset = 2;
		std::string wk_open_style = "Solid";
		std::string wk_open_lb_size = "Normal";
		uint32_t opens_txt_c = 0x00FFFFFFu;
		bool wk_alert_open = true;
		bool amt_enable = true;
		std::string amt_sess = "1700-0830:123456";
		std::string amt_del_sess = "1500-1505";
		bool amt_showLb = true;
		int amt_width = 1;
		std::string amt_style_in = "Solid";
		uint32_t amt_c_hi = 0xFFFFFFFFu;
		uint32_t amt_c_txt_hi = 0xFFFFFFFFu;
		uint32_t amt_c_lo = 0xFFFFFFFFu;
		uint32_t amt_c_txt_lo = 0xFFFFFFFFu;
		std::string amt_lb_size_in = "Normal";
		int amt_offset = 2;
		bool amt_alert_ovn = true;
		bool amt_vauto = true;
		bool amt_vres = false;
		double amt_res_val = 0.25;
		bool pd_enable = true;
		bool pd_use_rth = true;
		std::string pd_sess_time = "0830-1500";
		bool pd_showH = true;
		bool pd_showL = true;
		bool pd_showOpen = false;
		uint32_t pd_high_c = 0xFFFFFFFFu;
		uint32_t pd_low_c = 0xFFFFFFFFu;
		uint32_t pd_open_c = 0xFF2196F3u;
		int pd_high_width = 1;
		int pd_low_width = 1;
		int pd_open_width = 1;
		std::string pd_style_in = "Solid";
		std::string pd_lb_size_in = "Normal";
		int pd_offset_val = 2;
		uint32_t pd_txt_c = 0x00FFFFFFu;
		bool pd_alert_hl = true;
		bool cc_enable = true;
		bool cc_show_poc = true;
		bool cc_show_vah = true;
		bool cc_show_val = true;
		bool cc_alert_va = false;
		bool cc_alert_80 = true;
		uint32_t pd_poc_c = 0xFFFFFFFFu;
		uint32_t pd_vah_c = 0x809C27B0u;
		uint32_t pd_val_c = 0x809C27B0u;
		int cc_poc_width = 1;
		int cc_vah_width = 1;
		int cc_val_width = 1;
		std::string cc_poc_style_in = "Solid";
		int cc_lb_offset = 2;
		std::string cc_lb_size_in = "Normal";
		uint32_t cc_txt_c = 0x00FFFFFFu;
		bool cc_showFill = true;
		uint32_t cc_col_active = 0x129C27B0u;
		uint32_t cc_col_conf = 0x12EA80FCu;
		double cc_va_pct = 0.68;
		std::string cc_sess_def = "0830-1500:23456";
		bool pw_enable = true;
		bool pw_showH = true;
		bool pw_showL = true;
		uint32_t pw_col = 0xFFFFFFFFu;
		uint32_t pw_c_txt = 0xFFFFFFFFu;
		int pw_width = 2;
		std::string pw_style_in = "Solid";
		int pw_offset = 2;
		std::string pw_lb_size_in = "Normal";
		bool pw_alert_hl = true;
		std::string sp_rth_session = "0830-1500";
		int sp_tpo_minutes = 30;
		int sp_ticks_per_block = 1;
		uint32_t sp_color_hist = 0x19FF9800u;
		uint32_t sp_border_c = 0xFFFF9800u;
		int sp_border_w = 0;
		std::string sp_border_style = "Solid";
		int sp_max_days = 10;
		bool sp_filter_tails = true;
		int sp_tail_max = 15;
		int sp_min_ticks = 1;
		bool sp_show_poor = true;
		int sp_poor_width = 2;
		std::string sp_poor_style_in = "Dotted";
		uint32_t sp_col_poor_h = 0xFFF23645u;
		uint32_t sp_col_poor_l = 0xFF4CAF50u;
		std::string sp_poor_lb_size = "Small";
		uint32_t sp_poor_txt_c = 0x00FFFFFFu;
		bool showSpike = true;
		std::string spikeTimeRange = "1430-1500";
		int spike_width = 1;
		std::string spike_style = "Solid";
		uint32_t spike_c_sup = 0xFF4CAF50u;
		uint32_t spike_c_res = 0xFFF23645u;
		int spike_offset = 15;
		std::string spike_lbl_size = "Normal";
		uint32_t spike_txt_c = 0x00FFFFFFu;
		bool spike_alert = true;
		bool inv_enable = true;
		bool inv_show_line = true;
		int inv_start_h = 17;
		int inv_end_h = 8;
		int inv_end_m = 30;
		uint32_t inv_c_trap = 0xFF00FF00u;
		uint32_t inv_c_settle = 0xFF787B86u;
		std::string inv_txt_trap = "TRAP ACTIVE";
		int inv_width = 1;
		std::string inv_style_in = "Dashed";
		int inv_settle_width = 1;
		std::string inv_settle_style = "Dashed";
		std::string inv_lb_size_in = "Normal";
		int inv_offset = 40;
		uint32_t inv_txt_c = 0x00FFFFFFu;
		bool inv_alert = true;
		bool npoc_enable = true;
		uint32_t npoc_c = 0xFFFFC0CBu;
		uint32_t npoc_c_w = 0xFFFFC0CBu;
		uint32_t npoc_c_m = 0xFFFFC0CBu;
		bool npoc_d_show = true;
		bool npoc_w_show = true;
		bool npoc_m_show = true;
		std::string npoc_style_in = "Solid";
		int npoc_w_d = 1;
		int npoc_w_w = 2;
		int npoc_w_m = 3;
		std::string npoc_lb_size = "Small";
		int npoc_lb_offset = 2;
		uint32_t npoc_txt_c = 0x00FFFFFFu;
		bool npoc_alert = true;
		std::string context_session = "0815-1500";
		int daily_atr_length = 14;
		bool tbl_show = true;
		std::string tbl_session = "0830-1500";
		std::string tbl_pos = "Top Right";
		std::string tbl_size = "Normal";
		bool HideAllLabels = false;
		bool LabelsLevels = true;
		bool LabelsProfiles = true;
		bool LabelsPriorDay = true;
		bool LabelsPriorValue = true;
		bool LabelsOpens = true;
		bool LabelsPriorWeek = true;
		bool LabelsPriorMonth = true;
		bool LabelsInventory = true;
		bool LabelsSpike = true;
		bool LabelsNakedPoc = true;
		bool LabelsPoor = true;
		bool ShowPriceTags = true;
		std::string LevelAlertMode = "Cross";
		int AlertZoneTicks = 4;
		int MaxProfileRows = MAX_PROFILE_ROWS;
		int MaxStructures = MAX_STRUCTURES;

		// Sierra Chart only (supersets of NinjaTrader's settings, spec A.2/A.3, used from Stage 2/3):
		int inv_start_minute = 17 * 60;		// Globex Start as a Time input (NinjaTrader: whole hours)
		bool spike_show_sup = true;			// subgraph 41 visible: a bullish spike is created
		bool spike_show_res = true;			// subgraph 42 visible: a bearish spike is created
		bool LabelsDOpen = true;			// input 55 not Off (NinjaTrader's one Opens switch, split)
		bool LabelsWkOpen = true;			// input 57 not Off
		// Stage 4: the paste box and the levels file as typed (inputs 7 and 6). lvl_text is NinjaTrader's
		// cfg.lvl_text: the accepted document, serialized (NT:1713), which the study sets.
		std::string lvl_paste = "";
		std::string levels_file = "";
	};

	// The sessions of a Settings, parsed once (an engine is built only from validated settings).
	struct SessionSet
	{
		SessionSpec rth, ibWindow, mvp_sess_time, mvp_alert_time, ib_session, ib_alert_time, ib_stop_time, amt_sess, amt_del_sess, pd_sess_time,
			cc_sess_def, sp_rth_session, spikeTimeRange, context_session, tbl_session;

		explicit SessionSet(const Settings& s)
		{
			ParseSession("0830-1500", rth);		// SESS_RTH, a constant (PINE:41)
			ParseSession("0830-0930", ibWindow);	// Classify's opening-hour test (NT:858)
			ParseSession(s.mvp_sess_time, mvp_sess_time);
			ParseSession(s.mvp_alert_time, mvp_alert_time);
			ParseSession(s.ib_session, ib_session);
			ParseSession(s.ib_alert_time, ib_alert_time);
			ParseSession(s.ib_stop_time, ib_stop_time);
			ParseSession(s.amt_sess, amt_sess);
			ParseSession(s.amt_del_sess, amt_del_sess);
			ParseSession(s.pd_sess_time, pd_sess_time);
			ParseSession(s.cc_sess_def, cc_sess_def);
			ParseSession(s.sp_rth_session, sp_rth_session);
			ParseSession(s.spikeTimeRange, spikeTimeRange);
			ParseSession(s.context_session, context_session);
			ParseSession(s.tbl_session, tbl_session);
		}
	};

	// A price as text: NinjaTrader's MathEx.Price (snap to the instrument tick, the tick's decimals)
	// in the tests; the chart's own format in Sierra Chart (spec Notation "Price").
	using PriceFormatter = std::function<std::string(double)>;

	// ---- Engine (NT:524-1035) ----

	// A completed chart bar is committed once; live previews run on a copy (Clone).
	class Engine
	{
	public:
		const Settings*	S		= nullptr;	// the study's current settings (display edits keep the engine)
		std::string		Root;
		double			Tick	= 0;
		double			Step	= 0;
		int				Minutes	= 0;
		std::vector<Level>	Levels;
		PriceFormatter	PriceText;

		// NinjaTrader's engine state (NT:528-553). Public so the tests can inspect it.
		SessionSet sess;
		Profile day, macro, nd, nw, nm;
		std::shared_ptr<Profile> main;		// shared with the frames that show it (never edited after Clone)
		ProfileStats prevDay, prevMonth;
		std::vector<std::shared_ptr<const PastProfile>> profiles;
		std::vector<Naked> naked;
		std::vector<ZoneItem> single;
		std::vector<Poor> poor;
		std::map<int64_t, TpoRow> tpo;
		std::deque<int64_t> tpoOrder;
		bool rowsPruned = false, structuresPruned = false;
		bool hasPrevious = false;
		Bar previous;
		int td = NO_DATE, week = NO_DATE, month = NO_DATE, mainKey = NO_DATE, macroKey = NO_DATE;
		CtTime mainStart = CT_MIN, weekStart = CT_MIN, monthStart = CT_MIN, dayStart = CT_MIN, rthStart = CT_MIN, ibStart = CT_MIN,
			settleStart = CT_MIN, spikeStart = CT_MIN;
		double tradeH = NaN, tradeL = NaN, weekH = NaN, weekL = NaN, monthH = NaN, monthL = NaN;
		double pdH = NaN, pdL = NaN, pdO = NaN, pwH = NaN, pwL = NaN, pmH = NaN, pmL = NaN, weekOpen = NaN;
		double rthH = NaN, rthL = NaN, rthO = NaN, rthPreviousOpen = NaN, ibH = NaN, ibL = NaN, ibWorkH = 0, ibWorkL = 0;
		double ovnH = NaN, ovnL = NaN, settle = NaN, spike = NaN, preH = NaN, preL = NaN, frozenH = 0, frozenL = 0;
		double dayH = NaN, dayL = NaN, tableH = 0, tableL = 0, vSrc = 0, vVol = 0, contextHlc = 0, contextVol = 0;
		int above = 0, below = 0, total = 0, otfUp = 0, otfDn = 0, tpoPeriod = -1;
		bool trap = false, resolved = false, trapAlert = false, bullSpike = false, auction = false, isTrapDay = false, outsideAbove = false,
			outsideBelow = false, gapUp = false, gapDown = false, rule = false, dayFull = false, weekFull = false, monthFull = false,
			macroFull = false;
		bool hasVaEntry = false;
		CtTime vaEntry = 0;
		std::string inventoryFrozen = "---", dayType = "DEVELOPING", pivotBias = "---";
		uint32_t dayColor = PAL_GRAY;
		double spStep = 0;
		// Row scale in effect (set from the last trade before each month starts). Each profile keeps
		// the step it was created with, so a scale change never mixes row sizes inside a profile.
		int rowMult = 1;
		double lastMacroClose = NaN;
		// The last bar's zone ATR (Process's local zoneAtr, NT:744), kept for the tests; the zones and flips
		// read the local.
		double lastZoneAtr = NaN;

		double RowStep(int mult) const { return (std::max)(Step * mult, S->mvp_row_size); }
		// Daily and prior-month profiles keep the plain Row Size at 1x, as before.
		double ValueStep(int mult) const { return mult > 1 ? (std::max)(S->mvp_row_size, Step * mult) : S->mvp_row_size; }
		double NakedStep(int mult) const { return (S->amt_vauto ? Step : S->amt_vres ? S->amt_res_val : Step) * mult; }
		double BlockStep(int mult) const { return Step * (std::max)(1, S->sp_ticks_per_block) * mult; }

	public:
		int RowMultInEffect() const { return rowMult; }

		Engine(const Settings* s, const std::string& root, double tick, double initialClose, int minutes)
			: S(s), Root(root), Tick(tick), Minutes(minutes), sess(*s)
		{
			Step = s->tick_auto ? AutoTick(root, tick, initialClose) : s->tick_manual_val;
			rowMult = RowMult(s->row_scale, initialClose, Step);
			main = std::make_shared<Profile>(RowStep(rowMult), s->MaxProfileRows);
			day = Profile(ValueStep(rowMult), s->MaxProfileRows);
			macro = Profile(ValueStep(rowMult), s->MaxProfileRows);
			nd = Profile(NakedStep(rowMult), s->MaxProfileRows);
			nw = Profile(NakedStep(rowMult), s->MaxProfileRows);
			nm = Profile(NakedStep(rowMult), s->MaxProfileRows);
			spStep = BlockStep(rowMult);
			Levels = ParseLevels(s->lvl_text);	// NT:567: the accepted document's text (spec B.4.7)
		}

		// A deep copy; completed profiles are shared (NT:569-575).
		std::unique_ptr<Engine> Clone() const
		{
			std::unique_ptr<Engine> e(new Engine(*this));
			e->main = std::make_shared<Profile>(*main);
			return e;
		}

		void ReplaceLevels(const std::vector<Level>& levels)
		{
			Levels = levels;
			for (Level& l : Levels)
				l.Flipped = false;
			pivotBias = "---";
		}

	private:
		bool Was(const SessionSpec& session) const { return hasPrevious && InSession(previous.Start, session); }
		// NinjaTrader's Max/Min: NaN (not yet set) is absent (NT:578-579).
		static double Max(double a, double b) { return Valid(a) ? MaxNet(a, b) : b; }
		static double Min(double a, double b) { return Valid(a) ? MinNet(a, b) : b; }
		std::string Price(double v) const { return PriceText ? PriceText(v) : std::string(); }
		static void Event(Frame& f, const std::string& key, const std::string& text) { f.Notices.push_back({key, text}); }

		void Cross(Frame& f, const char* name, double p, bool enabled, bool moving, double halfWidth = -1) const
		{
			if (Valid(p))
			{
				LevelWatch w;
				w.Name		= name;
				w.Price		= p;
				w.Enabled	= enabled;
				w.Moving	= moving;
				w.HalfWidth	= halfWidth >= 0 ? halfWidth : S->AlertZoneTicks * Tick;
				f.Watches.push_back(w);
			}
		}

		std::string Inventory() const
		{
			if (!S->inv_enable || total == 0)
				return "---";
			const double l = 100.0 * above / total, s = 100.0 * below / total;
			return l == 100 ? "TRAP LONG (100%)" : s == 100 ? "TRAP SHORT (100%)" : l > 60 ? "LONG (" + FormatNet(l, 0, false) + "%)"
				: s > 60 ? "SHORT (" + FormatNet(s, 0, false) + "%)" : "BALANCED";
		}

		// A completed day's, week's or month's POC becomes naked (NT:592-596). `complete` is the period's
		// dayFull/weekFull/monthFull before the roll, so the first, partial period never makes one.
		void NakedRoll(const Profile& p, const char* kind, bool complete, bool show, int width, CtTime start)
		{
			const double poc = p.Stats(.68).Poc;
			if (S->npoc_enable && complete && show && Valid(poc))
			{
				Naked n;
				n.Kind	= kind;
				n.Price	= poc;
				n.Start	= start;
				n.Width	= width;
				naked.push_back(n);
			}
		}

	public:
		int ProfileKey(const Bar& b) const
		{
			const int d = TradingDate(b.Start);
			return S->mvp_tf_mode == "Weekly" ? WeekOf(d) : S->mvp_tf_mode == "Monthly" ? MonthOf(d) : S->mvp_tf_mode == "Yearly" ? YearOf(d)
				: DateOfCt(b.Start);
		}

		// Sub-bars merged into clock-aligned buckets of `size` minutes (NT:602-612).
		static std::vector<Bar> Aggregate(const std::vector<Bar>& input, int size)
		{
			std::vector<Bar> result;
			CtTime bucket = CT_MIN;
			for (const Bar& b : input)
			{
				const CtTime k = CtAt(DateOfCt(b.Start), (MinuteOfDay(b.Start) / size) * size * 60);
				if (result.empty() || k != bucket)
				{
					Bar cur;
					cur.Start	= b.Start;
					cur.End		= b.End;
					cur.Open	= b.Open;
					cur.High	= b.High;
					cur.Low		= b.Low;
					cur.Close	= b.Close;
					cur.Volume	= b.Volume;
					result.push_back(cur);
					bucket = k;
				}
				else
				{
					Bar& cur = result.back();
					cur.High	= MaxNet(cur.High, b.High);
					cur.Low		= MinNet(cur.Low, b.Low);
					cur.Close	= b.Close;
					cur.Volume	+= b.Volume;
					cur.End		= b.End;
				}
			}
			return result;
		}

	public:
		// The previous-month profile takes completed 30-minute bars; never a future HTF close (NT:614-620).
		void AddMacro(const Bar& b)
		{
			const int key = MonthOf(TradingDate(b.Start));
			RollMacro(key, Valid(lastMacroClose) ? lastMacroClose : b.Close);
			macro.Add(b, true);
			lastMacroClose = b.Close;
		}

	private:
		void RollMacro(int key, double lastPrice)
		{
			if (macroKey != key)
			{
				if (macroKey != NO_DATE && macroFull)
					prevMonth = macro.Stats(S->mvp_val_pct);
				macroFull = macroKey != NO_DATE;
				macro = Profile(ValueStep(RowMult(S->row_scale, lastPrice, Step)), S->MaxProfileRows);
				macroKey = key;
			}
		}

	public:
		// One chart bar (NT:629-792), statements in NinjaTrader's order (spec B.0.7). full = false (a
		// committed bar, spec C.4) builds only what the history archive reads.
		Frame Process(const Bar& b, const std::vector<Bar>& subbars, const DailyValue* daily, bool full)
		{
			Frame f;
			f.Bar = b;
			const int d = TradingDate(b.Start), w = WeekOf(d), m = MonthOf(d);
			const bool newDay = td != d, newWeek = week != w, newMonth = month != m;
			const double lastPrice = hasPrevious ? previous.Close : b.Close;
			if (newMonth)
				rowMult = RowMult(S->row_scale, lastPrice, Step);
			RollMacro(m, lastPrice);
			const bool rth = InSession(b.Start, sess.rth), ib = InSession(b.Start, sess.ib_session), ovn = InSession(b.Start, sess.amt_sess);
			const bool pdSession = InSession(b.Start, sess.pd_sess_time), track = InSession(b.Start, sess.context_session),
				table = InSession(b.Start, sess.tbl_session);
			const bool spikeWindow = InSession(b.Start, sess.spikeTimeRange), spSession = InSession(b.Start, sess.sp_rth_session);
			if (newDay)
			{
				if (td != NO_DATE && dayFull && !day.Rows.empty())
					prevDay = day.Stats(S->cc_va_pct);
				if (!S->pd_use_rth && td != NO_DATE)
				{
					pdH = tradeH;
					pdL = tradeL;
				}
				NakedRoll(nd, "Daily", dayFull, S->npoc_d_show, S->npoc_w_d, b.Start);
				dayFull = td != NO_DATE || MinuteOfDay(b.Start) == 1020;
				day = Profile(ValueStep(rowMult), S->MaxProfileRows);
				nd = Profile(NakedStep(rowMult), S->MaxProfileRows);
				td = d;
				dayStart = b.Start;
				tradeH = b.High;
				tradeL = b.Low;
				rule = false;
				hasVaEntry = false;
				rthO = NaN;
				contextHlc = contextVol = 0;
				above = below = total = 0;
				trapAlert = false;
				trap = resolved = false;
			}
			else
			{
				tradeH = Max(tradeH, b.High);
				tradeL = Min(tradeL, b.Low);
			}
			// The week (NT:651-659): the prior week's high and low once a whole week is known, the weekly
			// naked POC, the weekly open (only from a Sunday 17:00 bar: NinjaTrader keeps none otherwise).
			if (newWeek)
			{
				if (weekFull)
				{
					pwH = weekH;
					pwL = weekL;
				}
				NakedRoll(nw, "Weekly", weekFull, S->npoc_w_show, S->npoc_w_w, b.Start);
				weekFull = week != NO_DATE || (WeekdayOfCt(b.Start) == 0 && MinuteOfDay(b.Start) == 1020);
				week = w;
				weekStart = b.Start;
				weekH = b.High;
				weekL = b.Low;
				nw = Profile(NakedStep(rowMult), S->MaxProfileRows);
				weekOpen = WeekdayOfCt(b.Start) == 0 && MinuteOfDay(b.Start) == 1020 ? b.Open : NaN;
			}
			else
			{
				weekH = Max(weekH, b.High);
				weekL = Min(weekL, b.Low);
			}
			// The month (NT:660-666): the prior month's high and low, the monthly naked POC.
			if (newMonth)
			{
				if (monthFull)
				{
					pmH = monthH;
					pmL = monthL;
				}
				NakedRoll(nm, "Monthly", monthFull, S->npoc_m_show, S->npoc_w_m, b.Start);
				monthFull = month != NO_DATE;
				month = m;
				monthStart = b.Start;
				monthH = b.High;
				monthL = b.Low;
				nm = Profile(NakedStep(rowMult), S->MaxProfileRows);
			}
			else
			{
				monthH = Max(monthH, b.High);
				monthL = Min(monthL, b.Low);
			}
			// Naked POC profiles use the 1-minute bars inside this chart bar, so they don't move with the
			// chart timeframe; the chart bar is the fallback when 1-minute data is missing (NT:667-671).
			const std::vector<Bar> self{b};
			const std::vector<Bar>& ones = !subbars.empty() ? subbars : self;
			if (S->npoc_enable)
				for (const Bar& one : ones)
				{
					if (S->npoc_d_show)
						nd.Add(one, false);
					if (S->npoc_w_show)
						nw.Add(one, false);
					if (S->npoc_m_show)
						nm.Add(one, false);
				}
			// A naked POC this bar trades through is no longer naked (NT:672), newest first. One made on this
			// bar (the new period's first bar) and touched by it is never shown.
			for (size_t i = naked.size(); i-- > 0;)
				if (b.Low <= naked[i].Price && b.High >= naked[i].Price)
				{
					if (S->npoc_alert)
						Event(f, "nPOC" + naked[i].Kind + Price(naked[i].Price), naked[i].Kind + " nPOC Touch @ " + Price(naked[i].Price));
					naked.erase(naked.begin() + (std::ptrdiff_t)i);
				}
			// The overnight high and low (NT:673-677).
			if (ovn && S->amt_enable)
			{
				if (!Was(sess.amt_sess) || newDay)
				{
					ovnH = b.High;
					ovnL = b.Low;
				}
				else
				{
					ovnH = Max(ovnH, b.High);
					ovnL = Min(ovnL, b.Low);
				}
			}
			// The prior day's high, low and open (NT:678-684): pdHigh/pdLow switch to the custom session
			// that just closed when it ends (15:00); the daily bar is the fallback until one has.
			if (pdSession)
			{
				if (!Was(sess.pd_sess_time))
				{
					rthH = b.High;
					rthL = b.Low;
					rthPreviousOpen = b.Open;
				}
				else
				{
					rthH = Max(rthH, b.High);
					rthL = Min(rthL, b.Low);
				}
			}
			if (!pdSession && Was(sess.pd_sess_time))
			{
				if (S->pd_use_rth)
				{
					pdH = rthH;
					pdL = rthL;
				}
				pdO = rthPreviousOpen;
			}
			if (daily != nullptr)
			{
				if (!Valid(pdH))
					pdH = daily->High;
				if (!Valid(pdL))
					pdL = daily->Low;
			}
			// The settlement: the close of the last bar of 08:30-15:00 (NT:685-688).
			if (!rth && Was(sess.rth))
			{
				settle = previous.Close;
				settleStart = b.Start;
				trap = resolved = false;
			}
			// The overnight inventory against the settlement and the trap (NT:689-696). Globex Start is
			// a Time input here (whole minutes; NinjaTrader's is a whole hour, inv_start_h * 60).
			const int barMinute = MinuteOfDay(b.Start), rthOpenMinute = S->inv_end_h * 60 + S->inv_end_m;
			const bool globex = barMinute >= S->inv_start_minute || barMinute < rthOpenMinute;
			if (globex && Valid(settle))
			{
				if (b.Low >= settle)
					above++;
				else if (b.High <= settle)
					below++;
				total++;
			}
			const bool imbalance = total > 0 && (above == total || below == total);
			// Latch only while overnight bars are being counted, so the prior night's counts can't latch against a new settlement.
			if (globex && imbalance && !resolved)
				trap = true;
			if (trap && b.Low <= settle && b.High >= settle)
			{
				trap = false;
				resolved = true;
			}
			if (S->inv_alert && S->inv_enable && trap && !trapAlert && barMinute >= rthOpenMinute && barMinute < rthOpenMinute + 30)
			{
				Event(f, "Inventory", "Inventory Trap Active @ " + Price(settle));
				trapAlert = true;
			}
			// The initial balance (NT:697-702): set when its window ends, kept until the next one starts.
			if (ib)
			{
				if (!Was(sess.ib_session) || newDay)
				{
					ibH = ibL = NaN;
					ibStart = b.Start;
					ibWorkH = b.High;
					ibWorkL = b.Low;
				}
				else
				{
					ibWorkH = MaxNet(ibWorkH, b.High);
					ibWorkL = MinNet(ibWorkL, b.Low);
				}
			}
			if (!ib && Was(sess.ib_session) && S->ib_enable)
			{
				ibH = ibWorkH;
				ibL = ibWorkL;
			}
			// The dashboard's inventory, frozen when the Context Tracking Session starts (NT:703).
			if (track && (!Was(sess.context_session) || newDay))
				inventoryFrozen = Inventory();
			// The RTH open: the first bar of the RTH Session for VA (NT:704).
			if (InSession(b.Start, sess.cc_sess_def) && (!Was(sess.cc_sess_def) || newDay))
				rthO = b.Open;
			// The RTH start (08:30): the day type's reset, the gap and outside-value tests (NT:705-711).
			if (rth && (!Was(sess.rth) || newDay))
			{
				rthStart = b.Start;
				preH = preL = NaN;
				dayH = b.High;
				dayL = b.Low;
				auction = false;
				otfUp = otfDn = 0;
				const double openPrice = Valid(rthO) ? rthO : b.Open;
				isTrapDay = S->inv_enable && imbalance;
				gapUp = Valid(pdH) && openPrice > pdH;
				gapDown = Valid(pdL) && openPrice < pdL;
				outsideAbove = Valid(prevDay.Vah) && openPrice > prevDay.Vah;
				outsideBelow = Valid(prevDay.Val) && openPrice < prevDay.Val;
			}
			// The late spike (NT:712-719): the RTH range before the window, frozen when it starts; a close
			// beyond it at the window's end leaves the spike's base, removed (with an alert) when touched.
			// Sierra Chart: a bullish spike needs the Spike Base (Supp) subgraph shown, a bearish one the
			// (Res) subgraph (NinjaTrader's one Show Late Spike switch is both, spec A.3).
			if (rth && !spikeWindow)
			{
				preH = Max(preH, b.High);
				preL = Min(preL, b.Low);
			}
			if (spikeWindow && !Was(sess.spikeTimeRange))
			{
				frozenH = preH;
				frozenL = preL;
				spikeStart = b.Start;
			}
			if (!spikeWindow && Was(sess.spikeTimeRange))
			{
				spike = NaN;
				if (S->showSpike && hasPrevious)
				{
					bullSpike = previous.Close > frozenH;
					if (bullSpike ? S->spike_show_sup : previous.Close < frozenL && S->spike_show_res)
						spike = bullSpike ? frozenH : frozenL;
				}
			}
			if (!spikeWindow && Valid(spike) && b.Low <= spike && b.High >= spike)
			{
				if (S->spike_alert)
					Event(f, "Spike", "Spike Base Touch @ " + Price(spike));
				spike = NaN;
			}
			// All profile inputs are available sub-bars only. Source's upper-exclusive, 200-row cap is retained.
			const std::vector<Bar>& raw = ones;
			const int shared = 1;
			int precision = 1;
			if (!TryParseNetInt(S->mvp_calc_tf, precision) || precision < 1)
				precision = 1;
			const int calc = precision != shared && Minutes > precision ? precision : shared;
			const int pk = ProfileKey(b);
			const bool mainWindow = S->mvp_tf_mode != "Session" || InSession(b.Start, sess.mvp_sess_time);
			if (mainWindow && mainKey != pk)
			{
				if (!main->Rows.empty())
				{
					auto past		= std::make_shared<PastProfile>();
					past->Data		= main;
					past->Stats		= main->Stats(S->mvp_val_pct);
					past->Start		= mainStart;
					past->End		= b.Start;
					past->EndIndex	= b.Index;
					past->EndSeq	= b.Seq;
					profiles.push_back(past);
					if (profiles.size() > 12)
						profiles.erase(profiles.begin());
				}
				main = std::make_shared<Profile>(RowStep(rowMult), S->MaxProfileRows);
				mainKey = pk;
				mainStart = b.Start;
			}
			// Prior-day value is built from the RTH Session for VA only (08:30-15:00 CT by default), the Dalton convention.
			for (const Bar& q : Aggregate(raw, calc))
			{
				if (mainWindow)
					main->Add(q, true);
				if (S->cc_enable && InSession(q.Start, sess.cc_sess_def))
					day.Add(q, true);
			}
			const ProfileStats dev = main->Stats(S->mvp_val_pct);
			UpdateTpo(b, spSession);
			// The trading day's VWAP (from 17:00, hlc3 of the chart bars) for the day type (NT:735-736).
			contextHlc += (b.High + b.Low + b.Close) / 3 * b.Volume;
			contextVol += b.Volume;
			const double dailyVwap = contextVol > 0 ? contextHlc / contextVol : NaN;
			const int minute = MinuteOfDay(b.Start);
			const bool vwin = minute >= S->vwap_start_h * 60 + S->vwap_start_m && minute < S->vwap_end_h * 60 + S->vwap_end_m;
			const int pm = !hasPrevious ? -1 : MinuteOfDay(previous.Start);
			const bool pvwin = pm >= S->vwap_start_h * 60 + S->vwap_start_m && pm < S->vwap_end_h * 60 + S->vwap_end_m;
			if (vwin)
			{
				if (!pvwin || newDay)
					vSrc = vVol = 0;
				vSrc += (b.High + b.Low + b.Close) / 3 * b.Volume;
				vVol += b.Volume;
			}
			else
				vSrc = vVol = 0;
			f.RthVwap = S->vwap_enable && vwin && vVol > 0 ? vSrc / vVol : NaN;
			const double dtr = daily == nullptr ? NaN : MaxNet(tradeH - tradeL, MaxNet(std::fabs(tradeH - daily->Close), std::fabs(tradeL - daily->Close)));
			f.DailyAtr = daily != nullptr && Valid(daily->Atr) ? (daily->Atr * (S->daily_atr_length - 1) + dtr) / S->daily_atr_length : NaN;
			const double zoneAtr = daily != nullptr && Valid(daily->Atr14) ? (daily->Atr14 * 13 + dtr) / 14 : NaN;
			lastZoneAtr = zoneAtr;
			if (rth)
				Classify(b, dailyVwap, f.DailyAtr);
			// The pivot bias during the Context Tracking Session, kept until changed (NT:746-750).
			if (track)
				for (const Level& l : Levels)
					if (l.Kind == 0)
					{
						const double z = (Valid(f.DailyAtr) ? f.DailyAtr : 1) * .005;
						pivotBias = b.Close > l.Price + z ? "BULLISH" : b.Close < l.Price - z ? "BEARISH" : "AT PIVOT";
						break;
					}
			// The 80% Rule (NT:751-762): the RTH open outside the prior day's value, then 60 minutes of
			// closes inside it within the Prev Day Custom Session; confirmed once per trading date.
			f.RuleActive = S->cc_enable && Valid(rthO) && (rthO > prevDay.Vah || rthO < prevDay.Val);
			if (f.RuleActive && pdSession)
			{
				if (b.Close < prevDay.Vah && b.Close > prevDay.Val)
				{
					if (!hasVaEntry)
					{
						hasVaEntry = true;
						vaEntry = b.Start;
					}
					if (!rule && TimeSpanNet::TotalMinutes(b.Start - vaEntry) >= 60)
					{
						rule = true;
						if (S->cc_alert_80)
							Event(f, "Rule80", "80% Rule Confirmed");
					}
				}
				else if (!rule)
					hasVaEntry = false;
			}
			if (!pdSession && !rule)
				hasVaEntry = false;
			f.RuleConfirmed	= rule;
			f.VaHigh		= prevDay.Vah;
			f.VaLow			= prevDay.Val;
			// The daily levels flip once price passes them by the Flip ATR Buffer (14-day zone ATR), and alert
			// with the zone's half-width as their band (NT:763-772).
			const double flip = Valid(zoneAtr) ? zoneAtr * S->lvl_flip_atr : 0;
			for (Level& l : Levels)
			{
				if (S->lvl_color_flip && l.Kind != 0)
				{
					if (l.Kind == -1)
					{
						if (!l.Flipped && b.Close > l.Price + flip)
							l.Flipped = true;
						else if (l.Flipped && b.Close < l.Price - flip)
							l.Flipped = false;
					}
					else
					{
						if (!l.Flipped && b.Close < l.Price - flip)
							l.Flipped = true;
						else if (l.Flipped && b.Close > l.Price + flip)
							l.Flipped = false;
					}
				}
				Cross(f, l.Name.c_str(), l.Price, S->lvl_alerts && (l.Kind == 0 ? S->lvl_alert_ip : l.Kind == -1 ? S->lvl_alert_bull : S->lvl_alert_bear), false,
					LevelZoneHalfWidth(zoneAtr));
			}
			Cross(f, "IBH", ibH, S->ib_enable && S->ib_alert_ibh && !ib && InSession(b.Start, sess.ib_alert_time), false);
			Cross(f, "IBL", ibL, S->ib_enable && S->ib_alert_ibl && !ib && InSession(b.Start, sess.ib_alert_time), false);
			Cross(f, "OVN High", ovnH, S->amt_enable && S->amt_alert_ovn && !ovn, false);
			Cross(f, "OVN Low", ovnL, S->amt_enable && S->amt_alert_ovn && !ovn, false);
			Cross(f, "RTH VWAP", f.RthVwap, S->vwap_alert && vwin && pvwin, true);
			Cross(f, "PDH", pdH, S->pd_alert_hl, false);
			Cross(f, "PDL", pdL, S->pd_alert_hl, false);
			Cross(f, "pwHigh", pwH, S->pw_alert_hl, false);
			Cross(f, "pwLow", pwL, S->pw_alert_hl, false);
			Cross(f, "Weekly Open", weekOpen, S->wk_alert_open, false);
			Cross(f, "pdPOC", prevDay.Poc, S->cc_alert_va, false);
			Cross(f, "pdVAH", prevDay.Vah, S->cc_alert_va, false);
			Cross(f, "pdVAL", prevDay.Val, S->cc_alert_va, false);
			const bool da = S->mvp_use_cur_alerts && InSession(b.Start, sess.mvp_alert_time);
			Cross(f, "Developing POC", dev.Poc, da, true);
			Cross(f, "Developing VAH", dev.Vah, da, true);
			Cross(f, "Developing VAL", dev.Val, da, true);
			Cross(f, "pmPOC", prevMonth.Poc, S->macro_alert_lvl, false);
			Cross(f, "pmVAH", prevMonth.Vah, S->macro_alert_lvl, false);
			Cross(f, "pmVAL", prevMonth.Val, S->macro_alert_lvl, false);
			Cross(f, "pmHigh", pmH, S->macro_alert_lvl, false);
			Cross(f, "pmLow", pmL, S->macro_alert_lvl, false);
			if (table && !Was(sess.tbl_session))
			{
				tableH = b.High;
				tableL = b.Low;
			}
			else if (table)
			{
				tableH = MaxNet(tableH, b.High);
				tableL = MinNet(tableL, b.Low);
			}
			PruneStructures();
			rowsPruned = rowsPruned || day.PrunedRows > 0 || main->PrunedRows > 0 || macro.PrunedRows > 0 || nd.PrunedRows > 0 || nw.PrunedRows > 0
				|| nm.PrunedRows > 0;
			BuildVisuals(f, dev, zoneAtr, table, ovn, full);
			if (rowsPruned)
				f.Warning += " Row limit reached: oldest rows pruned; profile/TPO values use retained rows.";
			if (structuresPruned)
				f.Warning += " Structure limit reached: oldest structures pruned.";
			previous = b;
			hasPrevious = true;
			return f;
		}

	private:
		// The TPO session's single prints and poor highs/lows (NT:793-835). Rows are blocks of spStep
		// (keys = floor(price / spStep)); a row counts each clock-aligned TPO period of the CT day once.
		// At each new period (and when the session ends) the single-print runs are found again: keys
		// with one period, runs allowed one-block gaps, kept when tall enough and (Filter Tails) not a
		// short tail at the session's edge. A poor high/low: two or more periods at the session's
		// extreme. Both go when traded through or older than Max History Days.
		void UpdateTpo(const Bar& b, bool active)
		{
			const bool was = Was(sess.sp_rth_session), ended = !active && was;
			auto removeLive = [this]() { single.erase(std::remove_if(single.begin(), single.end(), [](const ZoneItem& x) { return x.Live; }), single.end()); };
			if (active && !was)
			{
				tpo.clear();
				tpoOrder.clear();
				removeLive();
				tpoPeriod = -1;
				spStep = BlockStep(rowMult);
			}
			const int pid = MinuteOfDay(b.Start) / (std::max)(1, S->sp_tpo_minutes);
			const bool newPeriod = active && pid != tpoPeriod;
			if (active)
			{
				int64_t lo = (int64_t)std::floor(b.Low / spStep), hi = (int64_t)std::floor(b.High / spStep);
				if (hi - lo + 1 > S->MaxProfileRows)
				{
					lo = hi - S->MaxProfileRows + 1;
					rowsPruned = true;
				}
				for (int64_t k = lo; k <= hi; k++)
				{
					auto found = tpo.find(k);
					if (found == tpo.end())
					{
						while ((int64_t)tpo.size() >= S->MaxProfileRows)
						{
							tpo.erase(tpoOrder.front());
							tpoOrder.pop_front();
							rowsPruned = true;
						}
						TpoRow row;
						row.Last	= -1;
						row.First	= b.Start;
						found = tpo.emplace(k, row).first;
						tpoOrder.push_back(k);
					}
					if (found->second.Last != pid)
					{
						found->second.Hits++;
						found->second.Last = pid;
					}
				}
				tpoPeriod = pid;
			}
			if ((newPeriod || ended) && !tpo.empty())
			{
				removeLive();
				const int64_t high = tpo.rbegin()->first, low = tpo.begin()->first;
				std::vector<int64_t> candidates;
				for (const auto& row : tpo)
					if (row.second.Hits == 1)
						candidates.push_back(row.first);
				size_t start = 0;
				for (size_t i = 0; i < candidates.size(); i++)
				{
					if (i + 1 < candidates.size() && candidates[i + 1] <= candidates[i] + 2)
						continue;
					const int64_t a = candidates[start], z = candidates[i];
					const double ht = (double)(z - a) * spStep / Step;
					const bool tail = a <= low || z >= high;
					if (ht + 1e-8 >= S->sp_min_ticks && !(S->sp_filter_tails && tail && ht < S->sp_tail_max))
						for (size_t j = start; j <= i; j++)
						{
							ZoneItem zone;
							zone.Bottom			= (double)candidates[j] * spStep;
							zone.Top			= (double)(candidates[j] + 1) * spStep;
							zone.Start			= tpo.at(candidates[j]).First;
							zone.Created		= b.Start;
							zone.Color			= S->sp_color_hist;
							zone.BorderColor	= S->sp_border_c;
							zone.BorderWidth	= S->sp_border_w;
							zone.BorderStyle	= S->sp_border_style;
							zone.Live			= !ended;
							single.push_back(zone);
						}
					start = i + 1;
				}
				if (S->sp_show_poor)
				{
					const double hp = (double)(high + 1) * spStep, lp = (double)low * spStep;
					// One poor high (low) per price within two effective ticks.
					auto known = [this](bool isHigh, double price)
					{
						for (const Poor& x : poor)
							if (x.High == isHigh && std::fabs(x.Price - price) < Step * 2)
								return true;
						return false;
					};
					if (tpo.at(high).Hits >= 2 && !known(true, hp))
					{
						Poor p;
						p.High		= true;
						p.Price		= hp;
						p.Start		= tpo.at(high).First;
						p.Created	= b.Start;
						poor.push_back(p);
					}
					if (tpo.at(low).Hits >= 2 && !known(false, lp))
					{
						Poor p;
						p.High		= false;
						p.Price		= lp;
						p.Start		= tpo.at(low).First;
						p.Created	= b.Start;
						poor.push_back(p);
					}
				}
			}
			const int64_t now = b.Start;
			single.erase(std::remove_if(single.begin(), single.end(), [&](const ZoneItem& x)
				{ return (!x.Live && TotalDays(now - x.Created) > S->sp_max_days) || (x.Top > b.Low && x.Bottom < b.High); }), single.end());
			poor.erase(std::remove_if(poor.begin(), poor.end(), [&](const Poor& x)
				{ return TotalDays(now - x.Created) > S->sp_max_days || (x.High ? b.High > x.Price : b.Low < x.Price); }), poor.end());
		}

		// Dalton's day type, on every bar of 08:30-15:00 (NT:836-863): the IB is the reference range
		// (the overnight range until it is set); a type once real holds for the day (auction).
		void Classify(const Bar& b, double vwap, double dailyAtr)
		{
			const double h = Valid(ibH) ? ibH : ovnH, l = Valid(ibL) ? ibL : ovnL;
			dayH = Max(dayH, b.High);
			dayL = Min(dayL, b.Low);
			if (hasPrevious)
			{
				otfUp = b.Low > previous.Low ? otfUp + 1 : 0;
				otfDn = b.High < previous.High ? otfDn + 1 : 0;
			}
			std::string candidate = "DEVELOPING";
			uint32_t color = PAL_GRAY;
			bool real = false;
			if (isTrapDay)
			{
				candidate = "TRAP";
				color = PAL_ORANGE;
				real = true;
			}
			else if (Valid(h) && Valid(l))
			{
				const double range = dayH - dayL, ibRange = h - l, ext = ibRange > 0 ? range / ibRange : 0, pos = range > 0 ? (b.Close - dayL) / range : .5;
				const bool bu = dayH > h, bd = dayL < l, cvh = b.Close > prevDay.Vah, cvl = b.Close < prevDay.Val;
				const bool iu = dayH > pdH || (dayH > ovnH && cvh), id = dayL < pdL || (dayL < ovnL && cvl);
				bool tu = bu && pos > .75 && vwap > (h + l) / 2 && (otfUp >= 5 || iu) && ext > 1.5;
				bool tl = bd && pos < .25 && vwap < (h + l) / 2 && (otfDn >= 5 || id) && ext > 1.5;
				tu = tu || (iu && pos > .8 && ext > 2);
				tl = tl || (id && pos < .2 && ext > 2);
				real = true;
				if (tl)
				{
					candidate = "Trend Day (Down)";
					color = PAL_RED;
				}
				else if (tu)
				{
					candidate = "Trend Day (Up)";
					color = PAL_GREEN;
				}
				else if (bu && bd)
				{
					candidate = pos >= .65 ? "Neutral Extreme (Up)" : pos <= .35 ? "Neutral Extreme (Down)" : "Neutral Day (Center)";
					color = pos >= .65 ? PAL_GREEN_SOFT : pos <= .35 ? PAL_RED_SOFT : PAL_GRAY;
				}
				else if (dailyAtr > 0 && ibRange / dailyAtr > .5 && !bu && !bd)
					candidate = "Normal Day";
				else if (bu)
				{
					candidate = iu || ext > 1.2 || cvh ? "Normal Variation (Up)" : "Normal Day (Balance)";
					color = candidate.find("Up") != std::string::npos ? PAL_LIME : PAL_GRAY;
				}
				else if (bd)
				{
					candidate = id || ext > 1.2 || cvl ? "Normal Variation (Down)" : "Normal Day (Balance)";
					color = candidate.find("Down") != std::string::npos ? PAL_MAROON : PAL_GRAY;
				}
				else if (!InSession(b.Start, sess.ibWindow) || Valid(ibH))
					candidate = "Non-Trend Day";
				else
					real = false;
			}
			if (real)
			{
				auction = true;
				dayType = candidate;
				dayColor = color;
			}
			else if (!auction)
			{
				dayType = gapUp ? "GAP UP" : gapDown ? "GAP DOWN" : "DEVELOPING";
				dayColor = gapUp ? PAL_LIME : gapDown ? PAL_ALERT_RED : PAL_GRAY;
			}
		}

		// text: label text color; fully transparent (the default) means "use the line color" (NT:865-868).
		void Line(Frame& f, const std::string& name, double price, CtTime start, uint32_t color, int width, const std::string& style, int offset,
			const std::string& size, bool label, const std::string& extend, uint32_t text = 0) const
		{
			if (!Valid(price))
				return;
			LineItem l;
			l.Name		= name;
			l.Group		= LabelGroup(name, extend);
			l.Price		= price;
			l.Start		= start;
			l.End		= f.Bar.End;
			l.Color		= color;
			l.TextColor	= (text >> 24) == 0 ? color : text;
			l.Width		= width;
			l.Style		= style;
			l.Offset	= offset;
			l.Size		= size;
			l.Label		= label && ShowGroupLabel(l.Group);
			l.Extend	= extend;
			f.Lines.push_back(l);
		}

		// The daily levels' zone half-width (NT:869): a share of the 14-day ATR, or ticks of the effective tick.
		double LevelZoneHalfWidth(double zoneAtr) const
		{
			return S->lvl_zone_mode == "ATR %" && Valid(zoneAtr) ? zoneAtr * S->lvl_zone_atr_pct : S->lvl_zoneWidthTicks * Step;
		}

		// The structure limit (NT:870-881): past Maximum Retained Structures the oldest naked POCs (by
		// Start), poor highs/lows and single prints (by Created) go, across the three lists. LINQ's
		// OrderBy is a stable sort over naked, then poor, then single: equal times keep that order.
		void PruneStructures()
		{
			const int64_t excess = (int64_t)naked.size() + (int64_t)poor.size() + (int64_t)single.size() - S->MaxStructures;
			if (excess <= 0)
				return;
			structuresPruned = true;
			struct Aged
			{
				CtTime	Time	= 0;
				int		List	= 0;
				size_t	Index	= 0;
			};
			std::vector<Aged> all;
			all.reserve(naked.size() + poor.size() + single.size());
			for (size_t i = 0; i < naked.size(); i++)
				all.push_back({naked[i].Start, 0, i});
			for (size_t i = 0; i < poor.size(); i++)
				all.push_back({poor[i].Created, 1, i});
			for (size_t i = 0; i < single.size(); i++)
				all.push_back({single[i].Created, 2, i});
			std::stable_sort(all.begin(), all.end(), [](const Aged& a, const Aged& b) { return a.Time < b.Time; });
			std::vector<char> drop[3] = {std::vector<char>(naked.size(), 0), std::vector<char>(poor.size(), 0), std::vector<char>(single.size(), 0)};
			for (int64_t k = 0; k < excess; k++)
				drop[all[(size_t)k].List][all[(size_t)k].Index] = 1;
			auto prune = [&drop](auto& list, int which)
			{
				size_t kept = 0;
				for (size_t i = 0; i < list.size(); i++)
					if (drop[which][i] == 0)
						list[kept++] = list[i];
				list.resize(kept);
			};
			prune(naked, 0);
			prune(poor, 1);
			prune(single, 2);
		}

	public:
		// The label group of a line (NT:882-897), which picks its Show Labels switch. FIX G13: NinjaTrader
		// tests Extend == "Both" first, so IB lines extended both ways join the daily levels' group (their
		// labels follow the levels' switch, Force on Top's Daily Levels (All) lifts them). Here the line's
		// name decides first; only the lines no name rule claims and that extend both ways (the daily
		// levels and their zone borders, Stage 4) are "Levels". Identical for every other line.
		static std::string LabelGroup(const std::string& name, const std::string& extend)
		{
			if (StartsWith(name, "IB "))
				return "IB";
			if (StartsWith(name, "OVN "))
				return "OVN";
			if (name == "pdHigh" || name == "pdLow" || name == "pdOpen")
				return "PriorDay";
			if (StartsWith(name, "pd"))
				return "PriorValue";
			if (name == "dOpen" || name == "wkOpen")
				return "Opens";
			if (StartsWith(name, "pw"))
				return "PriorWeek";
			if (StartsWith(name, "pm"))
				return "PriorMonth";
			if (StartsWith(name, "Spike"))
				return "Spike";
			if (name.find("nPOC") != std::string::npos)
				return "NakedPoc";
			if (StartsWith(name, "Poor"))
				return "Poor";
			if (StartsWith(name, "Developing") || name == "HVN")
				return "Profiles";
			if (extend == "Both")
				return "Levels";
			return "Inventory";
		}

		bool ShowGroupLabel(const std::string& group) const
		{
			if (S->HideAllLabels)
				return false;
			if (group == "Levels")		return S->LabelsLevels;
			if (group == "Profiles")	return S->LabelsProfiles;
			if (group == "PriorDay")	return S->LabelsPriorDay;
			if (group == "PriorValue")	return S->LabelsPriorValue;
			if (group == "Opens")		return S->LabelsOpens;
			if (group == "PriorWeek")	return S->LabelsPriorWeek;
			if (group == "PriorMonth")	return S->LabelsPriorMonth;
			if (group == "Inventory")	return S->LabelsInventory;
			if (group == "Spike")		return S->LabelsSpike;
			if (group == "NakedPoc")	return S->LabelsNakedPoc;
			if (group == "Poor")		return S->LabelsPoor;
			if (group == "IB")			return S->ib_show_labels;
			if (group == "OVN")			return S->amt_showLb;
			return true;
		}

		// Inventory and open-location colors, matching the TradingView dashboard (NT:920-927).
		static uint32_t StatusColor(const std::string& s)
		{
			if (StartsWith(s, "TRAP LONG") || s == "Below pdLow")
				return PAL_ALERT_RED;
			if (StartsWith(s, "TRAP SHORT") || s == "Above pdHigh")
				return PAL_LIME;
			if (StartsWith(s, "LONG") || s == "Above pdVAH")
				return PAL_GREEN_SOFT;
			if (StartsWith(s, "SHORT") || s == "Below pdVAL")
				return PAL_RED_SOFT;
			return PAL_GRAY;
		}

	private:
		std::string OpenLocation() const
		{
			if (!Valid(rthO) || !Valid(pdH) || !Valid(pdL))
				return "---";
			return rthO > pdH ? "Above pdHigh" : rthO < pdL ? "Below pdLow" : rthO > prevDay.Vah ? "Above pdVAH" : rthO < prevDay.Val ? "Below pdVAL"
				: Valid(prevDay.Vah) ? "Inside Value" : "---";
		}

		// The frame's lines, zones, profiles and dashboard (NT:933-1035), in NinjaTrader's order, which
		// is also the lines' draw order (spec B.0.9). NinjaTrader's `ib` argument is unused there.
		void BuildVisuals(Frame& f, const ProfileStats& dev, double zoneAtr, bool table, bool ovn, bool full)
		{
			const CtTime now = f.Bar.Start;
			// A committed frame (full = false) keeps the day lines whatever their visibility: the archive
			// applies it when drawn (spec C.4), so showing a line later needs no rebuild.
			// The initial balance from its start to the Stop Time (NT:936-948).
			if (S->ib_enable && Valid(ibH))
			{
				CtTime end = f.Bar.End;
				if (S->ib_limit_ext && !InSession(now, sess.ib_stop_time))
					end = CtAt(DateOfCt(ibStart), sess.ib_stop_time.B * 60);	// ibStart.Date + the Stop Time's end (HHmm)
				const size_t n = f.Lines.size();
				Line(f, "IB High", ibH, ibStart, S->ib_col_hi, S->ib_lvl_width, S->ib_style_main, S->ib_lbl_offset, S->ib_label_size, S->ib_show_labels,
					S->ib_extend, S->ib_txt_c);
				Line(f, "IB Low", ibL, ibStart, S->ib_col_lo, S->ib_lvl_width, S->ib_style_main, S->ib_lbl_offset, S->ib_label_size, S->ib_show_labels,
					S->ib_extend, S->ib_txt_c);
				if (!full || S->ib_show_mid)
					Line(f, "IB Midpoint", (ibH + ibL) / 2, ibStart, S->ib_col_mid, S->ib_lvl_width, S->ib_style_int, S->ib_lbl_offset, S->ib_label_size,
						S->ib_show_labels, S->ib_extend, S->ib_txt_c);
				for (size_t i = n; i < f.Lines.size(); i++)
					f.Lines[i].End = end;
			}
			// The overnight high and low from the RTH start until the Delete OVN Lines At time (NT:949-954).
			// Not archived: a committed frame leaves them out.
			if (full && S->amt_enable && !ovn && MinuteOfDay(now) < sess.amt_del_sess.A)
			{
				const size_t n = f.Lines.size();
				Line(f, "OVN High", ovnH, rthStart, S->amt_c_hi, S->amt_width, S->amt_style_in, S->amt_offset, S->amt_lb_size_in, S->amt_showLb, "None");
				Line(f, "OVN Low", ovnL, rthStart, S->amt_c_lo, S->amt_width, S->amt_style_in, S->amt_offset, S->amt_lb_size_in, S->amt_showLb, "None");
				for (size_t i = n; i < f.Lines.size(); i++)
					f.Lines[i].TextColor = f.Lines[i].Name == "OVN High" ? S->amt_c_txt_hi : S->amt_c_txt_lo;
			}
			// The prior day's high, low and open from the trading day's start (NT:955-960).
			if (!full || S->pd_enable)
			{
				if (!full || S->pd_showH)
					Line(f, "pdHigh", pdH, dayStart, S->pd_high_c, S->pd_high_width, S->pd_style_in, S->pd_offset_val, S->pd_lb_size_in, true, "None", S->pd_txt_c);
				if (!full || S->pd_showL)
					Line(f, "pdLow", pdL, dayStart, S->pd_low_c, S->pd_low_width, S->pd_style_in, S->pd_offset_val, S->pd_lb_size_in, true, "None", S->pd_txt_c);
				if (!full || S->pd_showOpen)
					Line(f, "pdOpen", pdO, dayStart, S->pd_open_c, S->pd_open_width, S->pd_style_in, S->pd_offset_val, S->pd_lb_size_in, true, "None",
						S->pd_txt_c);
			}
			if (S->cc_enable)
			{
				if (!full || S->cc_show_poc)
					Line(f, "pdPOC", prevDay.Poc, dayStart, S->pd_poc_c, S->cc_poc_width, S->cc_poc_style_in, S->cc_lb_offset, S->cc_lb_size_in, true,
						"None", S->cc_txt_c);
				if (!full || S->cc_show_vah)
					Line(f, "pdVAH", prevDay.Vah, dayStart, S->pd_vah_c, S->cc_vah_width, S->cc_poc_style_in, S->cc_lb_offset, S->cc_lb_size_in, true,
						"None", S->cc_txt_c);
				if (!full || S->cc_show_val)
					Line(f, "pdVAL", prevDay.Val, dayStart, S->pd_val_c, S->cc_val_width, S->cc_poc_style_in, S->cc_lb_offset, S->cc_lb_size_in, true,
						"None", S->cc_txt_c);
			}
			// The RTH open from the RTH start (NT:967); archived with the day's lines.
			if (!full || S->cc_showOpen)
				Line(f, "dOpen", rthO, rthStart, S->cc_c_open, S->cc_open_width, S->cc_open_style, S->cc_open_offset, S->cc_open_lb_size, true, "None",
					S->opens_txt_c);
			if (!full)
				return;		// a committed frame: only what the archive and PdRolled read (spec C.4)
			// The weekly open from the week's start (NT:968).
			if (S->wk_showOpen)
				Line(f, "wkOpen", weekOpen, weekStart, S->wk_c_open, S->wk_open_width, S->wk_open_style, S->wk_open_offset, S->wk_open_lb_size, true, "None",
					S->opens_txt_c);
			// The prior week's high and low from the week's start, labeled in their own text color (NT:969-974).
			if (S->pw_enable)
			{
				if (S->pw_showH)
					Line(f, "pwHigh", pwH, weekStart, S->pw_col, S->pw_width, S->pw_style_in, S->pw_offset, S->pw_lb_size_in, true, "None");
				if (S->pw_showL)
					Line(f, "pwLow", pwL, weekStart, S->pw_col, S->pw_width, S->pw_style_in, S->pw_offset, S->pw_lb_size_in, true, "None");
				for (LineItem& l : f.Lines)
					if (StartsWith(l.Name, "pw"))
						l.TextColor = S->pw_c_txt;
			}
			if (S->macro_show_month)
			{
				Line(f, "pmVAH", prevMonth.Vah, monthStart, S->macro_color, S->macro_width, S->macro_style, S->macro_offset, S->macro_text_size, true, "None",
					S->macro_txt_c);
				Line(f, "pmVAL", prevMonth.Val, monthStart, S->macro_color, S->macro_width, S->macro_style, S->macro_offset, S->macro_text_size, true, "None",
					S->macro_txt_c);
			}
			if (S->macro_show_poc)
				Line(f, "pmPOC", prevMonth.Poc, monthStart, S->macro_poc_color, S->macro_poc_width, S->macro_poc_style, S->macro_offset, S->macro_text_size,
					true, "None", S->macro_txt_c);
			// The prior month's high and low in the pmVAH/pmVAL style (NT:977).
			if (S->macro_show_hl)
			{
				Line(f, "pmHigh", pmH, monthStart, S->macro_color, S->macro_width, S->macro_style, S->macro_offset, S->macro_text_size, true, "None",
					S->macro_txt_c);
				Line(f, "pmLow", pmL, monthStart, S->macro_color, S->macro_width, S->macro_style, S->macro_offset, S->macro_text_size, true, "None",
					S->macro_txt_c);
			}
			// The settlement, extended right; named with the Trap Text while the trap is on (NT:978).
			if (S->inv_enable && S->inv_show_line)
				Line(f, trap ? S->inv_txt_trap : "SETTLE", settle, settleStart, trap ? S->inv_c_trap : S->inv_c_settle, trap ? S->inv_width : S->inv_settle_width,
					trap ? S->inv_style_in : S->inv_settle_style, S->inv_offset, S->inv_lb_size_in, true, "Right", S->inv_txt_c);
			// The late spike's base (NT:979).
			if (S->showSpike)
				Line(f, bullSpike ? "Spike Base (Supp)" : "Spike Base (Res)", spike, spikeStart, bullSpike ? S->spike_c_sup : S->spike_c_res, S->spike_width,
					S->spike_style, S->spike_offset, S->spike_lbl_size, true, "None", S->spike_txt_c);
			// The naked POCs, extended right, in list order (NT:980).
			for (const Naked& n : naked)
				Line(f, n.Kind + " nPOC", n.Price, n.Start, n.Kind == "Weekly" ? S->npoc_c_w : n.Kind == "Monthly" ? S->npoc_c_m : S->npoc_c, n.Width,
					S->npoc_style_in, S->npoc_lb_offset, S->npoc_lb_size, true, "Right", S->npoc_txt_c);
			// The poor highs and lows, two bars past the current bar (NT:981).
			for (const Poor& p : poor)
				Line(f, p.High ? "Poor High" : "Poor Low", p.Price, p.Start, p.High ? S->sp_col_poor_h : S->sp_col_poor_l, S->sp_poor_width, S->sp_poor_style_in,
					2, S->sp_poor_lb_size, true, "None", S->sp_poor_txt_c);
			// The single prints (NT:982).
			f.Zones.insert(f.Zones.end(), single.begin(), single.end());
			// The daily levels (NT:983-995), across the panel: the line (width 0 when Show Level Lines is off: its
			// label stays) in the pivot, support or resistance color (a flipped level in the other side's, its
			// name prefixed FLIPPED), the zone and its two borders.
			const double hz = LevelZoneHalfWidth(zoneAtr);
			for (const Level& l : Levels)
			{
				const uint32_t color = l.Kind == 0 ? S->lvl_ip_color : ((l.Kind == 1) != (S->lvl_color_flip && l.Flipped)) ? S->lvl_bear_color : S->lvl_bull_color;
				const std::string name = (S->lvl_color_flip && l.Flipped ? "FLIPPED " : "") + l.Name;
				Line(f, name, l.Price, CT_MIN, color, S->lvl_showLine ? S->lvl_thickness : 0, S->lvl_style_in, S->lvl_x_offset, S->lvl_text_size_opt, true, "Both",
					S->lvl_txt_c);
				if (S->lvl_showZones)
				{
					ZoneItem zone;
					zone.Top	= l.Price + hz;
					zone.Bottom	= l.Price - hz;
					zone.Start	= CT_MIN;
					zone.Created = CT_MIN;
					zone.Color	= (color & 0xffffffu) | ((uint32_t)(255 * (100 - S->lvl_zoneOpacity) / 100) << 24);
					f.Zones.push_back(zone);
					Line(f, "", l.Price + hz, CT_MIN, color, 1, S->lvl_zone_style_in, 0, "Small", false, "Both");
					Line(f, "", l.Price - hz, CT_MIN, color, 1, S->lvl_zone_style_in, 0, "Small", false, "Both");
				}
			}
			if (S->mvp_master)
			{
				// NinjaTrader's bars: the window counts the bars holding trades (Bar.Seq), not empty columns.
				for (const auto& p : profiles)
					if (f.Bar.Seq - p->EndSeq < 4500)
					{
						FrameProfile h;
						h.Data		= p->Data;
						h.Stats		= p->Stats;
						h.Start		= p->Start;
						h.End		= p->End;
						h.EndIndex	= p->EndIndex;
						h.EndSeq	= p->EndSeq;
						f.Profiles.push_back(h);
					}
				FrameProfile current;
				current.Data		= main;
				current.Stats		= dev;
				current.Start		= mainStart;
				current.End			= f.Bar.End;
				current.EndIndex	= f.Bar.Index;
				current.EndSeq		= f.Bar.Seq;
				current.Current		= true;
				f.Profiles.push_back(current);
				if (S->mvp_show_poc)
					Line(f, "Developing POC", dev.Poc, mainStart, S->mvp_c_poc, S->mvp_poc_width, S->mvp_poc_style, S->mvp_offset, S->mvp_lb_size, true, "None",
						S->mvp_txt_c);
				if (S->mvp_show_vah)
					Line(f, "Developing VAH", dev.Vah, mainStart, S->mvp_c_levels, S->mvp_lvl_width, S->mvp_lvl_style, S->mvp_offset, S->mvp_lb_size, true,
						"None", S->mvp_txt_c);
				if (S->mvp_show_val)
					Line(f, "Developing VAL", dev.Val, mainStart, S->mvp_c_levels, S->mvp_lvl_width, S->mvp_lvl_style, S->mvp_offset, S->mvp_lb_size, true,
						"None", S->mvp_txt_c);
				if (S->mvp_show_walls && (int64_t)main->Rows.size() > (int64_t)S->mvp_smooth_len + 1)
					BuildWalls(f, now);
			}
			const std::string loc = OpenLocation();
			const double range = table ? tableH - tableL : 0, used = f.DailyAtr > 0 ? range / f.DailyAtr * 100 : 0;
			f.Labels = {"SESSION", "DAY TYPE", "PIVOT", "OVN INVENTORY", "OPEN", "ATR(" + std::to_string(S->daily_atr_length) + ")", "ATR USED", "80% RULE"};
			f.Values = {table ? "RTH" : ovn ? "OVN" : "CLOSED", table ? dayType : "---", table ? pivotBias : "---", table ? inventoryFrozen : Inventory(), table ? loc : "---",
				table && Valid(f.DailyAtr) ? FormatNet(f.DailyAtr, 2, true) : "---",
				table ? FormatNet(range, 2, true) + " (" + FormatNet(used, 0, false) + "%)" : "---",
				table && S->cc_enable && (outsideAbove || outsideBelow) ? rule ? "CONFIRMED" : f.RuleActive ? "ACTIVE" : "SETUP" : "---"};
			// Text colors mirror the TradingView dashboard cell by cell.
			f.Colors = {table ? PAL_LIME : ovn ? PAL_AQUA : PAL_GRAY, table ? dayColor : PAL_GRAY,
				f.Values[2] == "BULLISH" ? PAL_GREEN : f.Values[2] == "BEARISH" ? PAL_RED : f.Values[2] == "AT PIVOT" ? PAL_YELLOW : PAL_GRAY,
				StatusColor(f.Values[3]), StatusColor(f.Values[4]), PAL_GRAY,
				!table ? PAL_GRAY : used >= 100 ? PAL_ALERT_RED : used >= 75 ? PAL_ORANGE : PAL_GRAY,
				f.Values[7] == "CONFIRMED" ? PAL_PINK : f.Values[7] == "ACTIVE" ? PAL_ORANGE : f.Values[7] == "SETUP" ? PAL_YELLOW : PAL_GRAY};
			if (!Valid(f.DailyAtr))
				f.Warning = "Loading daily ATR: load at least 30 trading days.";
			if (!dayFull || !weekFull || !monthFull || !macroFull)
				f.Warning += " First partial profile period is warming up.";
		}

		// Volume profile walls (NT:1003-1022): where the smoothed row volume crosses the average times a
		// threshold that eases from Start Mult to End Mult over the period.
		void BuildWalls(Frame& f, CtTime now) const
		{
			std::vector<int64_t> keys;
			keys.reserve(main->Rows.size());
			for (const auto& row : main->Rows)
				keys.push_back(row.first);
			// Rows.Values.Average(): the dictionary's order, which is first-insertion order (no row is
			// evicted below the row limit).
			double sum0 = 0;
			for (int64_t k : main->Insertion)
				sum0 += main->Rows.at(k);
			const double avg = sum0 / (double)(int64_t)main->Insertion.size();
			const double duration = S->mvp_tf_mode == "Session" ? S->mvp_sess_dur / 24 : S->mvp_tf_mode == "Weekly" ? 7 : S->mvp_tf_mode == "Yearly"
				? 365.25 : 30.44;
			const double elapsed = mainStart == CT_MIN ? 1e9 : TotalDays(now - mainStart);
			const double progress = MinNet(1, MaxNet(0, elapsed / MaxNet(duration, .001)));
			const double mult = S->mvp_use_auto_scale ? S->mvp_scale_start + progress * (S->mvp_scale_end - S->mvp_scale_start) : S->mvp_vol_mult;
			bool inside = false;
			std::vector<double> walls;
			const int n = (int)keys.size();
			for (int i = 0; i < n; i++)
			{
				double sum = 0;
				int count = 0;
				const int half = S->mvp_smooth_len / 2;
				for (int j = (std::max)(0, i - half); j <= (std::min)(n - 1, i + half); j++)
				{
					sum += main->Rows.at(keys[(size_t)j]);
					count++;
				}
				const bool structure = sum / count > avg * mult;
				if (structure != inside)
				{
					const double p = (double)keys[(size_t)(structure ? i : (std::max)(0, i - 1))] * main->Step;
					bool close = false;
					for (double x : walls)
						close = close || std::fabs(x - p) < S->mvp_min_wall_dist * main->Step;
					if (!close)
					{
						walls.push_back(p);
						const uint32_t color = (S->mvp_c_wall_base & 0xffffffu) | ((uint32_t)(255 * (100 - S->mvp_wall_transp) / 100) << 24);
						Line(f, "HVN", p, mainStart, color, S->mvp_w_wall, S->mvp_wall_style, 0, "Small", false, S->mvp_extend_walls ? "Right" : "None");
					}
					inside = structure;
				}
			}
		}
	};

	// Live observations, independent of the engine's speculative copies (NT:1372-1400).
	struct LevelAlertTracker
	{
		struct Point
		{
			double	Close	= 0;
			double	Center	= 0;
			double	Width	= 0;
			bool	Enabled	= false;
		};

		std::map<std::string, Point> Points;

		void Reset() { Points.clear(); }

		std::vector<Notice> Observe(const std::vector<LevelWatch>& levels, double close, const std::string& mode, const PriceFormatter& price, double tick)
		{
			std::vector<Notice> result;
			std::set<std::string> present;
			auto text = [&price](double v) { return price ? price(v) : std::string(); };
			for (const LevelWatch& l : levels)
			{
				present.insert(l.Name);
				const auto found = Points.find(l.Name);
				if (found != Points.end() && found->second.Enabled && l.Enabled && (l.Moving || std::fabs(found->second.Center - l.Price) < tick * .001))
				{
					const Point& p = found->second;
					if (mode == "Cross" || mode == "Both")
					{
						if (p.Close <= p.Center && close > l.Price)
							result.push_back({l.Name + "Up", l.Name + " Cross Up @ " + text(l.Price)});
						if (p.Close >= p.Center && close < l.Price)
							result.push_back({l.Name + "Down", l.Name + " Cross Down @ " + text(l.Price)});
					}
					const bool wasInside = std::fabs(p.Close - p.Center) <= p.Width;
					const bool inside = std::fabs(close - l.Price) <= l.HalfWidth;
					if ((mode == "Zone Entry" || mode == "Both") && !wasInside && inside)
						result.push_back({l.Name + "Zone", l.Name + " Zone Entry @ " + text(l.Price) + " (\xC2\xB1" + text(l.HalfWidth) + ")"});
				}
				Point next;
				next.Close		= close;
				next.Center		= l.Price;
				next.Width		= l.HalfWidth;
				next.Enabled	= l.Enabled;
				Points[l.Name] = next;
			}
			for (auto it = Points.begin(); it != Points.end();)
				it = present.count(it->first) ? std::next(it) : Points.erase(it);
			return result;
		}
	};

	// ---- Driver (NinjaTrader's indicator, NT:1756-1912), platform-free ----

	// What the RTH VWAP and the 80% Rule fill draw per bar (NT:1646-1649, NT:1859).
	struct Sample
	{
		int		Index		= 0;
		CtTime	Start		= 0;
		double	Vwap		= NaN;
		double	VaHigh		= 0;
		double	VaLow		= 0;
		bool	Fill		= false;
		bool	Confirmed	= false;
	};

	Sample ToSample(const Frame& f)
	{
		Sample s;
		s.Index		= f.Bar.Index;
		s.Start		= f.Bar.Start;
		s.Vwap		= f.RthVwap;
		s.VaHigh	= f.VaHigh;
		s.VaLow		= f.VaLow;
		s.Fill		= f.RuleActive || f.RuleConfirmed;
		s.Confirmed	= f.RuleConfirmed;
		return s;
	}

	// pdHigh, pdLow and pdOpen: the lines that roll at 15:00 (NinjaTrader's IsRollingPd, NT:1634).
	const char* const ROLLING_PD[3] = {"pdHigh", "pdLow", "pdOpen"};

	int RollingPdIndex(const std::string& name)
	{
		for (int k = 0; k < 3; k++)
			if (name == ROLLING_PD[k])
				return k;
		return -1;
	}

	bool IsRollingPd(const LineItem& x)
	{
		return RollingPdIndex(x.Name) >= 0;
	}

	// Which of pdHigh, pdLow and pdOpen are shown (bits 0, 1, 2): NinjaTrader's frames hold only the
	// shown ones, and its PdRolled (NT:1635-1643) compares only those, so its archive depends on them.
	int PdCombination(bool high, bool low, bool open)
	{
		return (high ? 1 : 0) | (low ? 2 : 0) | (open ? 4 : 0);
	}

	// Whether one rolling line changed price between two frames (NinjaTrader's PdRolled, line by line).
	bool PdLineRolled(const Frame& a, const Frame& b, const char* name)
	{
		for (const LineItem& x : a.Lines)
			if (x.Name == name)
			{
				for (const LineItem& y : b.Lines)
					if (y.Name == name)
						return std::fabs(y.Price - x.Price) > 1e-9;
				return false;
			}
		return false;
	}

	// An archived day line (NT:1843) and the pdHigh/pdLow/pdOpen combinations (PdCombination) whose
	// NinjaTrader archive holds it: the drawing shows it under the combination shown now (spec C.4).
	struct ArchivedLine
	{
		LineItem	Line;
		uint8_t		Sets	= 0xFF;

		bool In(int combination) const { return ((Sets >> combination) & 1) != 0; }
	};

	// One minute as a source gives it: its START in chart time (microseconds) and its tick-snapped
	// prices. Empty: a column with no data (not a minute at all).
	struct MinuteRec
	{
		int64_t	M		= 0;
		double	Open	= 0;
		double	High	= 0;
		double	Low		= 0;
		double	Close	= 0;
		double	Volume	= 0;
		bool	Empty	= false;
	};

	// Minutes in ascending start order, by index: the hidden 1-minute chart's arrays, this chart's
	// own 1-minute bars, or (for the 30-minute buckets only, when no 1-minute chart exists) this
	// chart's bars; vectors in the tests.
	struct MinuteSource
	{
		virtual int64_t Count() const = 0;
		virtual MinuteRec At(int64_t k) const = 0;

	protected:
		~MinuteSource() = default;
	};

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

	// Chart time -> CT (spec C.3): Sierra Chart's conversion, cached per chart-time hour (the
	// offset changes only at daylight-saving hours). No converter: the chart is in CT.
	struct CtClock
	{
		std::function<int64_t(int64_t)>				Convert;	// chart-time microseconds -> CT microseconds
		mutable std::unordered_map<int64_t, int64_t>	Offsets;

		CtTime Of(int64_t chartUs) const
		{
			if (!Convert)
				return FloorDiv(chartUs, US_PER_SECOND);
			const int64_t hour = FloorDiv(chartUs, US_PER_HOUR);
			auto found = Offsets.find(hour);
			if (found == Offsets.end())
			{
				const int64_t start = hour * US_PER_HOUR;
				found = Offsets.emplace(hour, Convert(start) - start).first;
			}
			return FloorDiv(chartUs + found->second, US_PER_SECOND);
		}
	};

	// One chart bar (spec B.0.1, C.2.1): start and end in chart time (Sierra Chart's start stamp and
	// the end, NinjaTrader's close stamp) and in CT, prices snapped to the tick.
	struct ChartBar
	{
		int64_t	Su		= 0;
		int64_t	Eu		= 0;
		CtTime	S		= 0;
		CtTime	E		= 0;
		double	Open	= 0;
		double	High	= 0;
		double	Low		= 0;
		double	Close	= 0;
		double	Volume	= 0;
		bool	Empty	= false;

		bool SameAs(const ChartBar& o) const
		{
			return Su == o.Su && Eu == o.Eu && Open == o.Open && High == o.High && Low == o.Low && Close == o.Close && Volume == o.Volume && Empty == o.Empty;
		}
	};

	Bar EngineBar(const std::vector<ChartBar>& bars, int i, int seq)
	{
		const ChartBar& c = bars[(size_t)i];
		Bar b;
		b.Start		= c.S;
		b.End		= c.E;
		b.Index		= i;
		b.Seq		= seq;
		b.Open		= c.Open;
		b.High		= c.High;
		b.Low		= c.Low;
		b.Close		= c.Close;
		b.Volume	= c.Volume;
		return b;
	}

	Bar MinuteBar(const MinuteRec& r, CtTime start)
	{
		Bar b;
		b.Start		= start;
		b.End		= start + 60;
		b.Open		= r.Open;
		b.High		= r.High;
		b.Low		= r.Low;
		b.Close		= r.Close;
		b.Volume	= r.Volume;
		return b;
	}

	// The 1-minute bars inside a chart bar (NT:1816: start >= the bar's start, end <= its end), in
	// time order, none starting after `limitUs` (a replay's time, see ReplayReadLimit). `used`: the
	// highest minute index read + 1.
	std::vector<Bar> SubbarsOf(const MinuteSource* source, const ChartBar& bar, const CtClock& clock, int64_t& used, int64_t limitUs = INT64_MAX)
	{
		std::vector<Bar> result;
		if (source == nullptr)
			return result;
		const int64_t count = source->Count();
		for (int64_t k = FirstMinuteAtOrAfter(*source, bar.Su); k < count; k++)
		{
			const MinuteRec r = source->At(k);
			if (r.M + US_PER_MINUTE > bar.Eu || r.M > limitUs)
				break;
			used = (std::max)(used, k + 1);
			if (!r.Empty)
				result.push_back(MinuteBar(r, clock.Of(r.M)));
		}
		return result;
	}

	// The 30-minute bars of the prior-month profile (spec C.2.3), built from the minutes: CT date +
	// whole half hours (clock-aligned, as NinjaTrader's 30-minute bars on a 17:00 session), each
	// bucket once, in time order. NinjaTrader's DrainMacro (NT:1818-1822): every bucket ending at or
	// before `through` goes to the engine.
	struct MacroCursor
	{
		int64_t	Next	= 0;	// the first minute not yet in a drained bucket
	};

	CtTime BucketOf(CtTime t)
	{
		return CtAt(DateOfCt(t), (MinuteOfDay(t) / 30) * 1800);
	}

	void DrainMacro(Engine& engine, MacroCursor& cursor, const MinuteSource* source, int64_t clipUs, CtTime through, const CtClock& clock, int64_t& used)
	{
		if (source == nullptr)
			return;
		const int64_t count = source->Count();
		while (cursor.Next < count)
		{
			MinuteRec first = source->At(cursor.Next);
			if (first.Empty || first.M < clipUs)
			{
				cursor.Next++;
				used = (std::max)(used, cursor.Next);
				continue;
			}
			const CtTime key = BucketOf(clock.Of(first.M));
			if (key + 1800 > through)
				return;
			Bar bucket = MinuteBar(first, key);
			bucket.End = key + 1800;
			int64_t k = cursor.Next + 1;
			for (; k < count; k++)
			{
				const MinuteRec r = source->At(k);
				if (r.Empty)
					continue;
				if (BucketOf(clock.Of(r.M)) != key)
					break;
				bucket.High		= MaxNet(bucket.High, r.High);
				bucket.Low		= MinNet(bucket.Low, r.Low);
				bucket.Close	= r.Close;
				bucket.Volume	+= r.Volume;
			}
			engine.AddMacro(bucket);
			cursor.Next = k;
			used = (std::max)(used, k);
		}
	}

	// ---- Alerts (NT:1872-1891, spec C.6) ----

	// What the study delivers: an id (NinjaTrader's alert id) and the text without the symbol.
	using Deliver = std::function<void(const std::string& id, const std::string& text)>;

	struct AlertState
	{
		std::set<std::pair<int, std::string>>	Sent;			// (bar index, key) already fired or seeded
		std::deque<CtTime>						Times;			// the storm cap's window
		bool									CapWarned		= false;
		int										FirstLiveBar	= INT_MAX;
		LevelAlertTracker						Tracker;
		int										Delivered		= 0;

		void Reset()
		{
			Sent.clear();
			Times.clear();
			CapWarned		= false;
			FirstLiveBar	= INT_MAX;
			Tracker.Reset();
		}

		// NinjaTrader clears its sent set at each commit (NT:1796): ids of committed bars go.
		void DropThrough(int index)
		{
			while (!Sent.empty() && Sent.begin()->first <= index)
				Sent.erase(Sent.begin());
		}
	};

	// One frame's notices (NT:1872-1891). confirmed: a committed bar; else the preview, which also
	// observes the watches at its close. Not live (a full recalculation, a download, a bar before the
	// first live one): the notices are computed and their ids remembered, nothing is delivered, so a
	// recalculation never repeats what already fired (FIX G7).
	void EmitAlerts(AlertState& a, const Settings& cfg, Frame& f, bool confirmed, bool live, double tick, const PriceFormatter& price,
		const Deliver& deliver)
	{
		if (!confirmed)
		{
			const std::vector<Notice> observed = a.Tracker.Observe(f.Watches, f.Bar.Close, cfg.LevelAlertMode, price, tick);
			f.Notices.insert(f.Notices.end(), observed.begin(), observed.end());
		}
		const bool deliverNow = live && f.Bar.Index >= a.FirstLiveBar;
		for (const Notice& n : f.Notices)
		{
			if (n.Key == "Rule80" && !confirmed)
				continue;
			if (!a.Sent.insert(std::make_pair(f.Bar.Index, n.Key)).second)
				continue;
			if (!deliverNow)
				continue;
			const CtTime now = f.Bar.Start;
			while (!a.Times.empty() && a.Times.front() < now - (int64_t)cfg.alertcap_window_min * 60)
				a.Times.pop_front();
			if ((int)a.Times.size() < cfg.alertcap_max)
				a.CapWarned = false;
			const std::string index = std::to_string(f.Bar.Index);
			if (cfg.alertcap_enable && (int)a.Times.size() >= cfg.alertcap_max)
			{
				if (!a.CapWarned)
				{
					if (deliver)
						deliver("Cap:" + index, "Alert storm cap reached (" + std::to_string(cfg.alertcap_max) + "/" + std::to_string(cfg.alertcap_window_min)
							+ "m). Further alerts suppressed.");
					a.Delivered++;
					a.CapWarned = true;
				}
				continue;
			}
			if (cfg.alertcap_enable)
				a.Times.push_back(now);
			if (deliver)
				deliver(index + ":" + n.Key, n.Text + " | close " + (price ? price(f.Bar.Close) : std::string()));
			a.Delivered++;
		}
	}

	// ---- Commit / preview (NT:1790-1858, spec C.4) ----

	// What one study call gives the driver.
	struct CallInput
	{
		const std::vector<ChartBar>*	Bars			= nullptr;
		const MinuteSource*				Minutes			= nullptr;	// sub-bars (null: the chart-bar fallback)
		const MinuteSource*				MacroMinutes	= nullptr;	// the 30-minute buckets' input
		bool							Gate			= false;	// commit a bar only once a minute at/after its end exists
		int64_t							ClipUs			= INT64_MIN;	// no minute before this chart time (this chart's first bar)
		int64_t							ReadLimitUs		= INT64_MAX;	// no sub-bar after this chart time (a replay's, ReplayReadLimit)
		const CtClock*					Clock			= nullptr;
		bool							Live			= false;
		Deliver							Send;
		std::function<void()>			BeforePreview;	// after this call's commits (NinjaTrader's ReadLevelsFile spot, NT:1801)
	};

	struct AmtCore
	{
		Settings							Cfg;			// the engine reads these (display edits apply at once)
		std::string							Root;
		double								Tick		= 0.25;
		int									Minutes		= 5;
		PriceFormatter						PriceText;
		DailyHistory						Daily;
		std::unique_ptr<Engine>				Committed;
		int									CommittedIndex	= -1;
		int									NextBar		= 0;	// the first chart bar not yet committed (or skipped)
		MacroCursor							Macro;
		std::deque<Sample>					Samples;		// committed bars (NinjaTrader's RenderHistory, 50,000)
		std::vector<ArchivedLine>			History;		// archived day lines (NT:1835-1847)
		bool								HasPrevFrame	= false;
		Frame								PrevFrame;
		// NinjaTrader's pdBeforeRoll (NT:1838), per rolling line (ROLLING_PD): within the trading date,
		// the commit that first changed its price (Moment) and the frame before it's rolling lines.
		struct PdCapture
		{
			bool					Has		= false;
			int						Moment	= 0;
			std::vector<LineItem>	Lines;
		};
		std::array<PdCapture, 3>			PdRolls;
		std::vector<int>					Seqs;			// each chart bar's Seq (Bar.Seq), this call's
		AlertState							Alerts;
		// The newest preview: the frame drawn and the samples of the uncommitted bars.
		bool								HasView		= false;
		Frame								View;
		std::vector<Sample>					ViewSamples;
		int64_t								MinutesUsed	= 0;	// minutes read so far (a prefix of the source)
		// Tests: committed frames built in full and handed over.
		bool								CommitFull	= false;
		std::function<void(const Frame&)>	OnCommit;
		int									Commits		= 0;
		int									Previews	= 0;

		void Reset()
		{
			Committed.reset();
			CommittedIndex	= -1;
			NextBar			= 0;
			Macro			= MacroCursor();
			Samples.clear();
			History.clear();
			HasPrevFrame	= false;
			PrevFrame		= Frame();
			PdRolls			= std::array<PdCapture, 3>();
			Alerts.Reset();
			HasView			= false;
			View			= Frame();
			ViewSamples.clear();
			MinutesUsed		= 0;
		}

		// A levels file's new revision while live (NT:1905-1910): the committed engine takes the new levels
		// (unflipped, the pivot bias reset), the tracker forgets its points (replacing a level cannot
		// manufacture a crossing alert), and an engine built later reads the new text.
		void ReplaceLevels(const LevelsDocument& document)
		{
			Cfg.lvl_text = document.Serialize();
			if (Committed)
				Committed->ReplaceLevels(document.Levels);
			Alerts.Tracker.Reset();
		}

		Frame CalculateFrame(Engine& target, const Bar& b, const std::vector<Bar>& subs, bool full) const
		{
			Frame f = target.Process(b, subs, Daily.Before(TradingDate(b.Start)), full);
			if (subs.empty())
				f.Warning += TEXT_NO_MINUTES;
			return f;
		}

		// The ended trading date's lines into the archive (NT:1839-1847): the IB lines, dOpen and the pd
		// lines of its last frame, with pdHigh/pdLow/pdOpen as they stood before the 15:00 roll. For
		// each combination of shown rolling lines, NinjaTrader's roll is the earliest first change among
		// them; the rolled lines (their capture, after the others as NinjaTrader appends them) and the
		// unrolled ones (in frame order) carry the combinations they belong to. Then the 20-day cut.
		void ArchiveDay(CtTime newStart)
		{
			int roll[8];
			for (int set = 0; set < 8; set++)
			{
				roll[set] = -1;
				for (int k = 0; k < 3; k++)
					if (((set >> k) & 1) != 0 && PdRolls[(size_t)k].Has && (roll[set] < 0 || PdRolls[(size_t)k].Moment < PdRolls[(size_t)roll[set]].Moment))
						roll[set] = k;
			}
			// The combinations holding line k: unrolled (capture < 0), or rolled at that capture's moment.
			auto setsOf = [&](int k, int capture)
			{
				uint8_t sets = 0;
				for (int set = 0; set < 8; set++)
					if (((set >> k) & 1) != 0 && (capture < 0 ? roll[set] < 0
						: roll[set] >= 0 && PdRolls[(size_t)roll[set]].Moment == PdRolls[(size_t)capture].Moment))
						sets = (uint8_t)(sets | (1u << set));
				return sets;
			};
			auto archive = [this](const LineItem& x, uint8_t sets)
			{
				if (sets == 0)
					return;
				ArchivedLine a;
				a.Line.Name		= x.Name;
				a.Line.Price	= x.Price;
				a.Line.Start	= x.Start;
				a.Line.End		= x.End;
				a.Line.Color	= x.Color;
				a.Line.Width	= x.Width;
				a.Line.Style	= x.Style;
				a.Line.Label	= false;
				a.Sets			= sets;
				History.push_back(a);
			};
			for (const LineItem& x : PrevFrame.Lines)
			{
				const int k = RollingPdIndex(x.Name);
				if (k >= 0)
					archive(x, setsOf(k, -1));
				else if (StartsWith(x.Name, "IB ") || x.Name == "dOpen" || StartsWith(x.Name, "pd"))
					archive(x, 0xFF);
			}
			for (int c = 0; c < 3; c++)
			{
				bool repeated = false;
				for (int e = 0; e < c; e++)
					repeated = repeated || (PdRolls[(size_t)e].Has && PdRolls[(size_t)c].Has && PdRolls[(size_t)e].Moment == PdRolls[(size_t)c].Moment);
				if (!PdRolls[(size_t)c].Has || repeated)
					continue;
				for (const LineItem& x : PdRolls[(size_t)c].Lines)
					archive(x, setsOf(RollingPdIndex(x.Name), c));
			}
			PdRolls = std::array<PdCapture, 3>();
			History.erase(std::remove_if(History.begin(), History.end(), [newStart](const ArchivedLine& a) { return TotalDays(newStart - a.Line.End) > 20; }),
				History.end());
		}

		// NinjaTrader's Commit (NT:1830-1851): drain the 30-minute bars, process the bar once, archive
		// the day lines at a new trading date, keep the sample, emit the bar's notices.
		void Commit(const CallInput& in, int i)
		{
			const std::vector<ChartBar>& bars = *in.Bars;
			DrainMacro(*Committed, Macro, in.MacroMinutes, in.ClipUs, bars[(size_t)i].E, *in.Clock, MinutesUsed);
			const std::vector<Bar> subs = SubbarsOf(in.Minutes, bars[(size_t)i], *in.Clock, MinutesUsed, in.ReadLimitUs);
			Frame f = CalculateFrame(*Committed, EngineBar(bars, i, Seqs[(size_t)i]), subs, CommitFull);
			const bool sameDay = HasPrevFrame && TradingDate(PrevFrame.Bar.Start) == TradingDate(f.Bar.Start);
			// pdHigh, pdLow and pdOpen switch to the session that just closed at 15:00. Keep the lines as they
			// stood before that switch, so each day's history shows the values that were in force during that day.
			// NinjaTrader keeps them at the first change of a line it draws (PdRolled over its shown lines,
			// NT:1838); the committed frames here hold all three (spec C.4), so each line's first change is
			// kept and ArchiveDay writes the archive of every combination of shown lines.
			if (sameDay)
				for (int k = 0; k < 3; k++)
					if (!PdRolls[(size_t)k].Has && PdLineRolled(PrevFrame, f, ROLLING_PD[k]))
					{
						PdCapture& c = PdRolls[(size_t)k];
						c.Has		= true;
						c.Moment	= Commits;
						c.Lines.clear();
						for (const LineItem& x : PrevFrame.Lines)
							if (IsRollingPd(x))
								c.Lines.push_back(x);
					}
			if (HasPrevFrame && !sameDay)
				ArchiveDay(f.Bar.Start);
			Samples.push_back(ToSample(f));
			while (Samples.size() > MAX_SAMPLES)
				Samples.pop_front();
			CommittedIndex = i;
			Commits++;
			EmitAlerts(Alerts, Cfg, f, true, in.Live, Tick, PriceText, in.Send);
			Alerts.DropThrough(i);
			if (OnCommit)
				OnCommit(f);
			f.Profiles.clear();
			PrevFrame		= std::move(f);
			HasPrevFrame	= true;
		}

		// One study call: commit every completed bar the minutes have moved past, then preview the rest
		// on a copy of the engine (NinjaTrader's Preview, NT:1852-1858); the last bar's frame is drawn.
		void Run(const CallInput& in)
		{
			const std::vector<ChartBar>& bars = *in.Bars;
			int lastReal = (int)bars.size() - 1;
			while (lastReal >= 0 && bars[(size_t)lastReal].Empty)
				lastReal--;
			if (lastReal < 0)
			{
				HasView = false;
				ViewSamples.clear();
				return;
			}
			// NinjaTrader's bar numbers: the bars holding trades before each one.
			Seqs.resize(bars.size());
			int seq = 0;
			for (size_t i = 0; i < bars.size(); i++)
			{
				Seqs[i] = seq;
				seq += bars[i].Empty ? 0 : 1;
			}
			if (!Committed)
			{
				int first = 0;
				while (bars[(size_t)first].Empty)
					first++;
				Committed.reset(new Engine(&Cfg, Root, Tick, bars[(size_t)first].Close, Minutes));
				Committed->PriceText = PriceText;
			}
			if (in.Live && Alerts.FirstLiveBar == INT_MAX)
				Alerts.FirstLiveBar = lastReal;
			for (; NextBar < lastReal; NextBar++)
			{
				const ChartBar& b = bars[(size_t)NextBar];
				if (b.Empty)
					continue;
				if (in.Gate)
				{
					const int64_t count = in.Minutes != nullptr ? in.Minutes->Count() : 0;
					if (count == 0 || in.Minutes->At(count - 1).M < b.Eu)
						break;
				}
				Commit(in, NextBar);
			}
			if (in.BeforePreview)
				in.BeforePreview();
			int j0 = NextBar;
			while (j0 < lastReal && bars[(size_t)j0].Empty)
				j0++;
			DrainMacro(*Committed, Macro, in.MacroMinutes, in.ClipUs, bars[(size_t)j0].S, *in.Clock, MinutesUsed);
			std::unique_ptr<Engine> preview = Committed->Clone();
			MacroCursor cursor = Macro;
			int64_t unusedCount = 0;
			ViewSamples.clear();
			for (int j = j0; j <= lastReal; j++)
			{
				if (bars[(size_t)j].Empty)
					continue;
				const bool last = j == lastReal;
				DrainMacro(*preview, cursor, in.MacroMinutes, in.ClipUs, last ? bars[(size_t)j].S : bars[(size_t)j].E, *in.Clock, unusedCount);
				const std::vector<Bar> subs = SubbarsOf(in.Minutes, bars[(size_t)j], *in.Clock, unusedCount, in.ReadLimitUs);
				Frame f = CalculateFrame(*preview, EngineBar(bars, j, Seqs[(size_t)j]), subs, last);
				ViewSamples.push_back(ToSample(f));
				if (last)
					View = std::move(f);
			}
			HasView = true;
			Previews++;
			EmitAlerts(Alerts, Cfg, View, false, in.Live, Tick, PriceText, in.Send);
		}
	};

	// ---- Settings checks (pure) ----

	// NinjaTrader's ValidateSettings (NT:2681-2800) in its order: the first failure is the study's
	// configuration error. The choice lists cannot hold another value here, so their checks are
	// gone; Sierra Chart's input limits hold most of the rest (kept for settings saved before them).
	// warning: the session-time notice (NT:2799; Time inputs compared to the minute, spec A.5).
	std::string ValidateSettings(const Settings& s, std::string& warning)
	{
		warning.clear();
		auto session = [](const std::string& text) { SessionSpec spec; return ParseSession(text, spec); };
		auto invalid = [](const std::string& text) { return "Invalid CT session: " + text; };
		if (s.tick_manual_val < 0.001) return "Manual Tick Size is below its minimum.";
		if (!Valid(s.tick_manual_val)) return "Manual Tick Size must be finite.";
		if (s.alertcap_max < 5) return "Max Alerts per Window is below its minimum.";
		if (s.alertcap_max > 200) return "Max Alerts per Window exceeds its maximum.";
		if (s.alertcap_window_min < 5) return "Window (minutes) is below its minimum.";
		if (s.alertcap_window_min > 1440) return "Window (minutes) exceeds its maximum.";
		if (s.lvl_zone_atr_pct < 0.01) return "Zone Width (ATR %) is below its minimum.";
		if (s.lvl_zone_atr_pct > 0.50) return "Zone Width (ATR %) exceeds its maximum.";
		if (!Valid(s.lvl_zone_atr_pct)) return "Zone Width (ATR %) must be finite.";
		if (s.lvl_zoneWidthTicks < 1) return "Zone Width (ticks above & below) is below its minimum.";
		if (s.lvl_zoneWidthTicks > 200) return "Zone Width (ticks above & below) exceeds its maximum.";
		if (s.lvl_zoneOpacity < 0) return "Zone Transparency (0=solid, 100=transp) is below its minimum.";
		if (s.lvl_zoneOpacity > 100) return "Zone Transparency (0=solid, 100=transp) exceeds its maximum.";
		if (!Valid(s.lvl_flip_atr)) return "Flip ATR Buffer must be finite.";
		if (!session(s.mvp_sess_time)) return invalid(s.mvp_sess_time);
		if (!Valid(s.mvp_sess_dur)) return "Session Duration (Hours) must be finite.";
		if (s.mvp_row_size < 0.25) return "Row Size is below its minimum.";
		if (!Valid(s.mvp_row_size)) return "Row Size must be finite.";
		if (!Valid(s.mvp_val_pct)) return "Value Area % must be finite.";
		if (s.mvp_profile_width < 10) return "Profile Width (Bars) is below its minimum.";
		if (s.mvp_profile_width > 500) return "Profile Width (Bars) exceeds its maximum.";
		if (s.mvp_offset < -200) return "Profile Offset (Bars) is below its minimum.";
		if (s.mvp_offset > 200) return "Profile Offset (Bars) exceeds its maximum.";
		if (!Valid(s.mvp_scale_start)) return "Start Mult must be finite.";
		if (!Valid(s.mvp_scale_end)) return "End Mult must be finite.";
		if (!Valid(s.mvp_vol_mult)) return "Fixed Mult must be finite.";
		if (!session(s.mvp_alert_time)) return invalid(s.mvp_alert_time);
		if (!session(s.ib_session)) return invalid(s.ib_session);
		if (!session(s.ib_alert_time)) return invalid(s.ib_alert_time);
		if (!session(s.ib_stop_time)) return invalid(s.ib_stop_time);
		if (s.vwap_start_h < 0) return "VWAP Start H (CT) is below its minimum.";
		if (s.vwap_start_h > 23) return "VWAP Start H (CT) exceeds its maximum.";
		if (s.vwap_start_m < 0) return "VWAP Start M (CT) is below its minimum.";
		if (s.vwap_start_m > 59) return "VWAP Start M (CT) exceeds its maximum.";
		if (s.vwap_end_h < 0) return "VWAP End H (CT) is below its minimum.";
		if (s.vwap_end_h > 23) return "VWAP End H (CT) exceeds its maximum.";
		if (s.vwap_end_m < 0) return "VWAP End M (CT) is below its minimum.";
		if (s.vwap_end_m > 59) return "VWAP End M (CT) exceeds its maximum.";
		if (!session(s.amt_sess)) return invalid(s.amt_sess);
		if (!session(s.amt_del_sess)) return invalid(s.amt_del_sess);
		if (s.amt_width < 1) return "OVN Width is below its minimum.";
		if (s.amt_res_val < 0.0001) return "OVN Manual Res Value is below its minimum.";
		if (!Valid(s.amt_res_val)) return "OVN Manual Res Value must be finite.";
		if (!session(s.pd_sess_time)) return invalid(s.pd_sess_time);
		if (s.sp_border_w < 0 || s.sp_border_w > 4) return "Single Print Border Width must be from 0 to 4.";
		if (s.inv_settle_width < 1 || s.inv_settle_width > 10) return "Settle Line Width must be from 1 to 10.";
		if (s.npoc_lb_offset < -50 || s.npoc_lb_offset > 200) return "nPOC Label Offset must be from -50 to 200.";
		if (s.cc_va_pct < 0.01) return "Value Area % is below its minimum.";
		if (s.cc_va_pct > 1.0) return "Value Area % exceeds its maximum.";
		if (!Valid(s.cc_va_pct)) return "Value Area % must be finite.";
		if (!session(s.cc_sess_def)) return invalid(s.cc_sess_def);
		if (!session(s.sp_rth_session)) return invalid(s.sp_rth_session);
		if (s.sp_tpo_minutes < 1) return "TPO Period is below its minimum.";
		if (s.sp_ticks_per_block < 1) return "Ticks per Block is below its minimum.";
		if (!session(s.spikeTimeRange)) return invalid(s.spikeTimeRange);
		if (s.inv_start_h < 0) return "Globex Start H (CT) is below its minimum.";
		if (s.inv_start_h > 23) return "Globex Start H (CT) exceeds its maximum.";
		if (s.inv_end_h < 0) return "RTH Open H (CT) is below its minimum.";
		if (s.inv_end_h > 23) return "RTH Open H (CT) exceeds its maximum.";
		if (s.inv_end_m < 0) return "RTH Open M (CT) is below its minimum.";
		if (s.inv_end_m > 59) return "RTH Open M (CT) exceeds its maximum.";
		if (!session(s.context_session)) return invalid(s.context_session);
		if (!session(s.tbl_session)) return invalid(s.tbl_session);
		if (s.AlertZoneTicks < 1) return "Structure alert zone half-width (ticks) is below its minimum.";
		if (s.AlertZoneTicks > 1000) return "Structure alert zone half-width (ticks) exceeds its maximum.";
		if (s.daily_atr_length < 1 || s.sp_tpo_minutes < 1 || s.mvp_sess_dur <= 0 || s.mvp_smooth_len < 1 || s.sp_max_days < 1)
			return "Periods and history lengths must be positive.";
		if (s.mvp_val_pct <= 0 || s.mvp_val_pct > 100) return "Profile value area must be between 0 and 100 percent.";
		int precision = 0;
		if (!TryParseNetInt(s.mvp_calc_tf, precision) || precision < 1 || precision > 30)
			return "Calc Precision must be a whole number of minutes from 1 to 30.";
		if (s.tzguard_enable && (s.mvp_sess_time != "0830-1500" || s.mvp_alert_time != "0830-1500" || s.ib_session != "0830-0930"
			|| s.ib_alert_time != "0830-1500" || s.ib_stop_time != "0830-1515" || s.amt_sess != "1700-0830:123456" || s.amt_del_sess != "1500-1505"
			|| s.pd_sess_time != "0830-1500" || s.cc_sess_def != "0830-1500:23456" || s.sp_rth_session != "0830-1500" || s.spikeTimeRange != "1430-1500"
			|| s.context_session != "0815-1500" || s.tbl_session != "0830-1500" || s.vwap_start_h != 8 || s.vwap_start_m != 30 || s.vwap_end_h != 15
			|| s.vwap_end_m != 0 || s.inv_start_minute != 17 * 60 || s.inv_end_h != 8 || s.inv_end_m != 30))
			warning = TEXT_SESSION_WARNING;
		return std::string();
	}

	// NinjaTrader accepts 1-30 minute bars only (NT:1704-1705, G11).
	std::string ChartError(int chartDataType, int barPeriodType, int secondsPerBar)
	{
		if (chartDataType != INTRADAY_DATA || barPeriodType != IBPT_DAYS_MINS_SECS || secondsPerBar < 60 || secondsPerBar > 1800 || secondsPerBar % 60 != 0)
			return TEXT_NOT_MINUTES;
		return std::string();
	}

	// start..end inclusive (seconds of the day); a range may cross midnight.
	bool InClockRange(int clock, int start, int end)
	{
		return start <= end ? clock >= start && clock <= end : clock >= start || clock <= end;
	}

	// NinjaTrader refuses an RTH-only trading-hours template (NT:1707). Sierra Chart has no template
	// names (SIERRA): the chart's Session Times, in CT, must hold both 03:00 and 12:00.
	bool CoversGlobex(const int* starts, const int* ends, int ranges)
	{
		for (int probe : {3 * 3600, 12 * 3600})
		{
			bool covered = false;
			for (int k = 0; k < ranges; k++)
				covered = covered || InClockRange(probe, starts[k], ends[k]);
			if (!covered)
				return false;
		}
		return true;
	}

	// What the engine is built from (spec C.4): every setting except the display-only ones (inputs
	// 2-5, 14-16, 23-24, 29-32, 38-39, 46-48, 55-58, 60-61, 63-64, 73-78, 81-82, 96-97, 100-101,
	// 106-107, 110-111, 113-115, 119-126 and the subgraphs' colors, widths, styles, label colors and
	// names), plus the visibility of subgraphs 16, 34-38, 41-42, which gates calculations. The levels
	// enter as typed (the paste box, the file template): a levels file's new revision replaces the
	// engine's levels without a rebuild, as NinjaTrader's (NT:1905-1909).
	uint64_t SettingsKey(const Settings& s)
	{
		uint64_t h = FNV64_BASIS;
		auto text = [&h](const std::string& v) { h = Fnv1a64Text(h, v); };
		auto number = [&h](double v) { h = Fnv1a64(h, &v, sizeof(v)); };
		auto flag = [&h](bool v) { const uint8_t b = v ? 1 : 0; h = Fnv1a64(h, &b, 1); };
		text(s.row_scale); flag(s.tick_auto); number(s.tick_manual_val);
		text(s.lvl_paste); text(s.levels_file); flag(s.lvl_color_flip); number(s.lvl_flip_atr); flag(s.lvl_showZones); text(s.lvl_zone_mode); number(s.lvl_zone_atr_pct);
		number(s.lvl_zoneWidthTicks); flag(s.lvl_alerts); flag(s.lvl_alert_ip); flag(s.lvl_alert_bull); flag(s.lvl_alert_bear);
		flag(s.pd_use_rth); text(s.pd_sess_time); flag(s.pd_alert_hl);
		flag(s.cc_enable); number(s.cc_va_pct); text(s.cc_sess_def); flag(s.cc_alert_va); flag(s.cc_alert_80);
		flag(s.amt_enable); text(s.amt_sess); text(s.amt_del_sess); flag(s.amt_alert_ovn);
		flag(s.ib_enable); text(s.ib_session); text(s.ib_extend); flag(s.ib_limit_ext); text(s.ib_stop_time); flag(s.ib_alert_ibh); flag(s.ib_alert_ibl);
		text(s.ib_alert_time);
		number(s.vwap_start_h); number(s.vwap_start_m); number(s.vwap_end_h); number(s.vwap_end_m); flag(s.vwap_alert); flag(s.vwap_enable);
		flag(s.wk_alert_open); flag(s.pw_alert_hl); flag(s.macro_alert_lvl);
		flag(s.mvp_master); text(s.mvp_tf_mode); text(s.mvp_sess_time); number(s.mvp_sess_dur); text(s.mvp_calc_tf); number(s.mvp_row_size);
		number(s.mvp_val_pct); flag(s.mvp_use_cur_alerts); text(s.mvp_alert_time);
		number(s.mvp_smooth_len); number(s.mvp_min_wall_dist); flag(s.mvp_use_auto_scale); number(s.mvp_scale_start); number(s.mvp_scale_end);
		number(s.mvp_vol_mult);
		text(s.sp_rth_session); number(s.sp_tpo_minutes); number(s.sp_ticks_per_block); number(s.sp_min_ticks); flag(s.sp_filter_tails);
		number(s.sp_tail_max); number(s.sp_max_days); flag(s.sp_show_poor);
		flag(s.npoc_enable); flag(s.amt_vauto); flag(s.amt_vres); number(s.amt_res_val); flag(s.npoc_alert); flag(s.npoc_d_show); flag(s.npoc_w_show);
		flag(s.npoc_m_show);
		flag(s.inv_enable); number(s.inv_start_h); number(s.inv_start_minute); number(s.inv_end_h); number(s.inv_end_m); flag(s.inv_alert);
		text(s.spikeTimeRange); flag(s.spike_alert); flag(s.showSpike); flag(s.spike_show_sup); flag(s.spike_show_res);
		text(s.tbl_session); text(s.context_session); number(s.daily_atr_length);
		return h;
	}

	// ---- Sierra Chart glue ----

	enum SourceKind { SRC_NONE, SRC_OWN, SRC_HIDDEN };

	// The hidden 1-minute chart's arrays read in place (Periodic VP's ArrayMinutes), prices snapped.
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

		MinuteRec At(int64_t k) const override
		{
			const int i = (int)k;
			MinuteRec r;
			r.M			= Micros((*Times)[i]);
			r.Open		= SnapToTick((double)(*Open)[i], Tick);
			r.High		= SnapToTick((double)(*High)[i], Tick);
			r.Low		= SnapToTick((double)(*Low)[i], Tick);
			r.Close		= SnapToTick((double)(*Close)[i], Tick);
			r.Volume	= (double)(*Volume)[i];
			const double trades = Trades != nullptr ? (double)(*Trades)[i] : 0;
			r.Empty = IsEmptyColumn((double)(*Volume)[i], trades, (double)(*Open)[i], (double)(*High)[i], (double)(*Low)[i], (double)(*Close)[i], i > 0,
				i > 0 ? (double)(*Close)[i - 1] : 0);
			return r;
		}

		static bool IsEmptyColumn(double volume, double trades, double open, double high, double low, double close, bool hasPrevious, double previousClose)
		{
			if (volume != 0 || trades != 0)
				return false;
			if (open == 0 && high == 0 && low == 0 && close == 0)
				return true;
			return hasPrevious && open == previousClose && high == previousClose && low == previousClose && close == previousClose;
		}

		static int64_t Micros(int64_t t) { return t; }
		static int64_t Micros(const SCDateTime& t) { return t.AsMicrosecondsSinceBaseDate(); }
	};

	// A column Sierra Chart adds with Include Columns With No Data: no volume, no trades, and either
	// all zero or flat at the previous close (Gap Analysis's rule). Never given to the engine.
	bool IsEmptyColumn(double volume, double trades, double open, double high, double low, double close, bool hasPrevious, double previousClose)
	{
		return ArrayMinutes<std::vector<int64_t>, std::vector<float>>::IsEmptyColumn(volume, trades, open, high, low, close, hasPrevious, previousClose);
	}

	// This chart's bars as minutes: on a 1-minute chart the minutes themselves (spec C.2.2 OWN); with
	// no 1-minute chart, the input of the 30-minute buckets only.
	struct BarMinutes final : MinuteSource
	{
		const std::vector<ChartBar>* Bars = nullptr;

		int64_t Count() const override { return Bars != nullptr ? (int64_t)Bars->size() : 0; }

		MinuteRec At(int64_t k) const override
		{
			const ChartBar& b = (*Bars)[(size_t)k];
			MinuteRec r;
			r.M			= b.Su;
			r.Open		= b.Open;
			r.High		= b.High;
			r.Low		= b.Low;
			r.Close		= b.Close;
			r.Volume	= b.Volume;
			r.Empty		= b.Empty;
			return r;
		}
	};

	// Sierra Chart's Session Times in the chart's time zone (seconds since midnight, each end the
	// session's last second) and where they cut a time bar (Periodic VP's SessionCutAfter).
	struct ChartSessions
	{
		int		DayStart				= 0;
		int		DayEnd					= 0;
		int		EveningStart			= 0;
		int		EveningEnd				= 0;
		bool	UseEvening				= false;
		bool	NewBarAtSessionStart	= false;
	};

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

	// A time bar's end (NinjaTrader's close stamp): start + the bar length, cut where the next bar
	// starts inside it or where the Session Times end. Microseconds.
	int64_t TimeBarEnd(int64_t startUs, int secondsPerBar, bool hasNext, int64_t nextStartUs, int64_t cutSeconds)
	{
		int64_t end = startUs + (int64_t)secondsPerBar * US_PER_SECOND;
		if (hasNext && startUs < nextStartUs && nextStartUs < end)
			end = nextStartUs;
		if (cutSeconds != INT64_MAX && cutSeconds * US_PER_SECOND < end)
			end = cutSeconds * US_PER_SECOND;
		return end;
	}

	// Where a CT time falls on the chart's bars (spec C.5.2, Periodic VP's PvpPosition on CT): the
	// end of bar i -> its center; inside bar i -> between the centers of bars i - 1 and i; in a gap
	// before bar i -> bar i - 1's center (so a line starting at a bar's start starts at the previous
	// bar's center, NinjaTrader's GetXByTime on close stamps); past the last bar, by its length.
	double BarPosition(const std::vector<ChartBar>& bars, CtTime t)
	{
		const int n = (int)bars.size();
		if (n == 0)
			return 0;
		size_t lo = 0, hi = (size_t)n;
		while (lo < hi)
		{
			const size_t mid = (lo + hi) / 2;
			if (bars[mid].E < t)
				lo = mid + 1;
			else
				hi = mid;
		}
		const size_t i = lo;
		double f;
		if (i == (size_t)n)
		{
			const size_t last		= (size_t)n - 1;
			const int64_t length	= bars[last].E - bars[last].S;
			f = (double)last + (length > 0 ? (double)(t - bars[last].E) / (double)length : 0.0);
		}
		else
		{
			const int64_t length	= bars[i].E - bars[i].S;
			const double inside		= length > 0 ? (double)(t - bars[i].S) / (double)length : (t >= bars[i].S ? 1.0 : 0.0);
			f = (double)i - 1 + (std::max)(0.0, (std::min)(1.0, inside));
		}
		return (std::max)(-1e7, (std::min)(1e7, f));
	}

	// A fractional bar position in pixels between the centers around it (whole pixels, as
	// NinjaTrader's GetXByTime). center(i): bar i's center, also past the loaded bars.
	template <typename BarCenter>
	int PositionX(double position, BarCenter center)
	{
		const double whole	= std::floor(position);
		const int i			= (int)whole;
		const double x0		= (double)center(i);
		const double x1		= (double)center(i + 1);
		return (int)RoundHalfUp(x0 + (position - whole) * (x1 - x0));
	}

	int NearestBar(double position, int count)
	{
		return (int)(std::max)(0.0, (std::min)((double)(count - 1), std::floor(position + 0.5)));
	}

	// ---- Translucent ranges (spec C.5.5; TPO Profile's study-owned ranges) ----

	enum RangeKind { RK_PROFILE = 0, RK_FILL80 = 1, RK_ZONE = 2, RK_SP = 3 };

	struct RangePiece
	{
		int			StartBar		= 0;
		int			EndBar			= 0;
		int			Id				= 0;
		double		Top				= 0;
		double		Bottom			= 0;
		uint32_t	Color			= 0;	// COLORREF
		int			Transparency	= 0;	// Sierra Chart TransparencyLevel: 0 opaque .. 100 invisible
		bool		ExtendToEnd		= false;
	};

	// LineIDForBar = 1 + rel + 65536 x (4 x (ordinal % 4096) + kind): unique per start bar within a
	// piece's owner (rel: its bottom key above the owner's lowest), owners by ordinal. At most 2^30.
	int RangeId(int kind, int ordinal, int64_t rel)
	{
		const int r = (int)(std::max)((int64_t)0, (std::min)((int64_t)65535, rel));
		return 1 + r + 65536 * (4 * (((ordinal % 4096) + 4096) % 4096) + kind);
	}

	uint64_t RangeKey(int startBar, int id)
	{
		return ((uint64_t)(uint32_t)startBar << 32) | (uint64_t)(uint32_t)id;
	}

	uint32_t RangeSignature(const RangePiece& r)
	{
		uint32_t hash = 2166136261u;
		const float prices[2] = {(float)r.Top, (float)r.Bottom};
		const int numbers[3] = {r.EndBar, r.Transparency, r.ExtendToEnd ? 1 : 0};
		hash = Fnv1a(hash, numbers, sizeof(numbers));
		hash = Fnv1a(hash, prices, sizeof(prices));
		hash = Fnv1a(hash, &r.Color, sizeof(r.Color));
		return hash == 0 ? 1 : hash;
	}

	// One profile class's look: shown (its subgraph visible), color, transparency.
	struct HistogramLook
	{
		bool		Show			= true;
		uint32_t	Color			= 0;
		int			Transparency	= 0;
	};

	// A completed profile as ranges (spec C.5.5 PROFILE): each row is round(volume / max x Profile Width)
	// whole bars wide (TradingView's rounding, F9; rows of width 0 are left out), right-aligned rows
	// ending at the anchor (the period's last bar), left-aligned ones starting there. The same cells
	// are cut into pieces two ways, and the one with fewer ranges is sent (the picture is the same):
	// rows: runs of adjacent rows with the same class (value area or outer) and width (the spec's
	// pieces); columns: in each one-bar column, runs of adjacent rows of one class reaching it (fewer
	// for tall, smooth profiles).
	std::vector<RangePiece> ProfilePieces(const FrameProfile& h, int anchor, int widthBars, bool alignRight, const HistogramLook& va, const HistogramLook& out)
	{
		std::vector<RangePiece> rows, columns;
		if (!h.Data || h.Data->Rows.empty())
			return rows;
		const Profile& p = *h.Data;
		double max = 0;
		for (const auto& row : p.Rows)
			max = (std::max)(max, row.second);
		if (!(max > 0))
			return rows;
		struct Cell
		{
			int64_t	Key		= 0;
			int		Width	= 0;
			bool	Va		= false;
		};
		std::vector<Cell> cells;
		int widest = 0;
		for (const auto& row : p.Rows)
		{
			Cell c;
			c.Key	= row.first;
			c.Va	= (double)row.first * p.Step >= h.Stats.Val && (double)row.first * p.Step <= h.Stats.Vah;
			c.Width	= (c.Va ? va : out).Show ? (int)RoundHalfUp(row.second / max * widthBars) : 0;
			widest	= (std::max)(widest, c.Width);
			cells.push_back(c);
		}
		const int64_t lowest = cells.front().Key;
		// Runs of cells [a, b) with the same class, adjacent keys and `same(cell)`; each becomes a piece.
		auto runs = [&](std::vector<RangePiece>& pieces, const std::function<bool(const Cell&)>& takes, const std::function<bool(const Cell&, const Cell&)>& same,
			const std::function<void(RangePiece&, const Cell&)>& span)
		{
			size_t a = 0;
			while (a < cells.size())
			{
				if (!takes(cells[a]))
				{
					a++;
					continue;
				}
				size_t b = a + 1;
				while (b < cells.size() && takes(cells[b]) && cells[b].Key == cells[b - 1].Key + 1 && cells[b].Va == cells[a].Va && same(cells[a], cells[b]))
					b++;
				const HistogramLook& look = cells[a].Va ? va : out;
				RangePiece r;
				r.Bottom		= (double)cells[a].Key * p.Step - p.Step / 2;
				r.Top			= (double)cells[b - 1].Key * p.Step + p.Step / 2;
				r.Color			= look.Color;
				r.Transparency	= look.Transparency;
				r.Id			= RangeId(RK_PROFILE, h.EndIndex, cells[a].Key - lowest);
				span(r, cells[a]);
				// No range starts before bar 0.
				r.StartBar = (std::max)(0, r.StartBar);
				if (r.EndBar > r.StartBar)
					pieces.push_back(r);
				a = b;
			}
		};
		runs(rows, [](const Cell& c) { return c.Width > 0; }, [](const Cell& x, const Cell& y) { return x.Width == y.Width; },
			[&](RangePiece& r, const Cell& c)
			{
				r.StartBar	= alignRight ? anchor - c.Width : anchor;
				r.EndBar	= alignRight ? anchor : anchor + c.Width;
			});
		for (int j = 0; j < widest && columns.size() < rows.size(); j++)
			runs(columns, [j](const Cell& c) { return c.Width > j; }, [](const Cell&, const Cell&) { return true; },
				[&](RangePiece& r, const Cell&)
				{
					r.StartBar	= alignRight ? anchor - j - 1 : anchor + j;
					r.EndBar	= r.StartBar + 1;
				});
		return columns.size() < rows.size() ? columns : rows;
	}

	// The 80% Rule fill as ranges (spec C.5.5 FILL80; NinjaTrader shades each sample with Fill and both
	// value edges from x - spacing/2 to x + spacing/2, NT:2009-2019): runs of samples of adjacent bars
	// with the same Confirmed, VaHigh and VaLow, from the first one's bar to the bar after the last one
	// (the same width, half a bar to the right). Adjacent: SamplesJoin, so an empty column (no bar to
	// NinjaTrader) does not break a run. Active runs in the subgraph's primary color, confirmed ones in
	// its secondary color.
	//
	// Whether two samples are of adjacent bars (NinjaTrader's prev.Bar.Index == sm.Bar.Index - 1,
	// NT:2015, NT:2056). NinjaTrader has no bars without trades: Sierra Chart's empty columns (Include
	// Columns With No Data, never given to the engine) between two samples do not separate them.
	bool SamplesJoin(const std::vector<ChartBar>& bars, int previous, int index)
	{
		if (previous < 0 || previous >= index || index >= (int)bars.size())
			return false;
		for (int i = previous + 1; i < index; i++)
			if (!bars[(size_t)i].Empty)
				return false;
		return true;
	}

	template <typename Committed>
	std::vector<RangePiece> Fill80Pieces(const Committed& committed, const std::vector<Sample>& view, const std::vector<ChartBar>& bars, uint32_t activeColor,
		uint32_t confirmedColor, int transparency)
	{
		std::vector<RangePiece> pieces;
		bool open = false;
		Sample first, last;
		auto close = [&]()
		{
			if (!open)
				return;
			RangePiece r;
			r.StartBar		= (std::max)(0, first.Index);
			r.EndBar		= last.Index + 1;
			r.Id			= RangeId(RK_FILL80, 0, 0);
			r.Top			= first.VaHigh;
			r.Bottom		= first.VaLow;
			r.Color			= first.Confirmed ? confirmedColor : activeColor;
			r.Transparency	= transparency;
			if (r.EndBar > r.StartBar)
				pieces.push_back(r);
			open = false;
		};
		auto visit = [&](const Sample& s)
		{
			const bool fills = s.Fill && Valid(s.VaHigh) && Valid(s.VaLow);
			if (open && fills && SamplesJoin(bars, last.Index, s.Index) && s.Confirmed == first.Confirmed && s.VaHigh == first.VaHigh && s.VaLow == first.VaLow)
			{
				last = s;
				return;
			}
			close();
			if (fills)
			{
				open	= true;
				first	= s;
				last	= s;
			}
		};
		for (const Sample& s : committed)
			visit(s);
		for (const Sample& s : view)
			visit(s);
		close();
		return pieces;
	}

	// T1 (TPO Profile's): whether Sierra Chart draws a range that ends past the last loaded bar, in the
	// chart's right-side fill space (a single print reaches 30 minutes past the current bar). If a tester
	// finds it does not, set this to false: those parts go to the callback.
	const bool RANGES_IN_FILL_SPACE = true;

	// A piece's bars split between a range and the callback (TPO Profile's SplitSpan): no range starts
	// before bar 0 or at/after the last loaded bar + 1 (a range starts on a loaded bar). There are no bars
	// there, so the callback blends those parts over the chart background in the range's own color and
	// opacity (grid lines and the lines of studies drawn under this one do not show through them).
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

	// How far past the current bar's end the single prints reach, in seconds. NinjaTrader draws them to
	// X(the current bar's end + 30 minutes) (NT:2022), and its time axis past the last bar holds the
	// coming bars of the trading hours only: a time in the break after the session (16:00-17:00 CT, the
	// weekend) falls on the session's last bar, so after the close they end there (NinjaTrader's
	// screenshot). The session's end is the Session Times' end after the current bar (a new bar at the
	// session's start is no break; an early close they do not hold keeps the 30 minutes).
	int SinglePrintReach(const ChartBar& current, ChartSessions sessions)
	{
		sessions.NewBarAtSessionStart = false;
		const int64_t cut = SessionCutAfter(FloorDiv(current.Su, US_PER_SECOND), sessions);
		if (cut == INT64_MAX)
			return 1800;
		const int64_t left = FloorDiv(cut * US_PER_SECOND - current.Eu, US_PER_SECOND);
		return (int)(std::max)((int64_t)0, (std::min)((int64_t)1800, left));
	}

	// The bar where the single prints end: the current bar + the reach in bars, the nearest whole bar (a
	// range ends at a bar's center; NinjaTrader's end is a fraction of a bar on bars that do not divide
	// 30 minutes). Their borders end there too, so each outline hugs its fill as NinjaTrader's.
	int SinglePrintEndBar(int lastBar, int secondsPerBar, int reachSeconds)
	{
		return lastBar + (int)RoundHalfUp((double)reachSeconds / (double)(std::max)(1, secondsPerBar));
	}

	// The single prints as ranges (spec C.5.5 SP; NinjaTrader fills each block from X(Start) to
	// X(the current bar's end + 30 minutes), NT:2020-2027): runs of adjacent blocks (one's Top the next
	// one's Bottom) with the same Start and Live, from the bar before the one starting at Start (X(Start):
	// that bar's center) to endBar (SinglePrintEndBar). Level zones (Start = MinValue, Stage 4) are not
	// single prints. Not yet split at the chart's ends (SplitSpan). The id: the run's lowest block key,
	// unique among the pieces of one start bar.
	std::vector<RangePiece> SinglePrintPieces(const std::vector<ZoneItem>& zones, const std::vector<ChartBar>& bars, int endBar, uint32_t color,
		int transparency)
	{
		std::vector<RangePiece> pieces;
		if (bars.empty())
			return pieces;
		std::vector<const ZoneItem*> order;
		for (const ZoneItem& z : zones)
			if (z.Start != CT_MIN && z.Top > z.Bottom)
				order.push_back(&z);
		std::stable_sort(order.begin(), order.end(), [](const ZoneItem* a, const ZoneItem* b)
			{ return a->Start != b->Start ? a->Start < b->Start : a->Live != b->Live ? b->Live : a->Bottom < b->Bottom; });
		std::set<uint64_t> used;
		size_t a = 0;
		while (a < order.size())
		{
			size_t b = a + 1;
			while (b < order.size() && order[b]->Start == order[a]->Start && order[b]->Live == order[a]->Live && order[b]->Bottom == order[b - 1]->Top)
				b++;
			RangePiece r;
			r.StartBar		= (int)std::floor(BarPosition(bars, order[a]->Start) + 0.5);
			r.EndBar		= endBar;
			r.Bottom		= order[a]->Bottom;
			r.Top			= order[b - 1]->Top;
			r.Color			= color;
			r.Transparency	= transparency;
			const int64_t key = (int64_t)std::floor(order[a]->Bottom / (order[a]->Top - order[a]->Bottom) + 0.5);
			const int64_t high = FloorDiv(key, 65536), low = key - high * 65536;
			r.Id = RangeId(RK_SP, (int)(high % 4096), low);
			for (int bump = 1; bump < 4096 && !used.insert(RangeKey(r.StartBar, r.Id)).second; bump++)
				r.Id = RangeId(RK_SP, (int)((high + bump) % 4096), low);
			if (r.EndBar > r.StartBar)
				pieces.push_back(r);
			a = b;
		}
		return pieces;
	}

	// ---- Study state ----

	const int TAG_SUBGRAPHS[12] = {SG_DEV_POC, SG_PM_POC, SG_PM_VAH, SG_PM_VAL, SG_PM_HIGH, SG_PM_LOW, SG_PW_HIGH, SG_PW_LOW, SG_PD_HIGH, SG_PD_LOW,
		SG_IB_HIGH, SG_IB_LOW};
	// NinjaTrader's markerNames (NT:1628), the line each tag shows.
	const char* const TAG_LINES[12] = {"Developing POC", "pmPOC", "pmVAH", "pmVAL", "pmHigh", "pmLow", "pwHigh", "pwLow", "pdHigh", "pdLow", "IB High",
		"IB Low"};

	struct StudyState
	{
		AmtCore						Core;
		std::string					Error;				// configuration error: drawn alone
		std::string					SettingsWarning;	// the session-time notice
		bool						Waiting		= false;	// the loading text (data not ready)
		bool						Built		= false;
		uint64_t					EngineKey	= 0;
		std::vector<ChartBar>		Bars;
		int							SecondsPerBar	= 0;
		CtClock						Clock;
		std::string					ClockZone;
		int							Kind		= SRC_NONE;
		// The hidden 1-minute chart (Periodic / Auto Anchored VP's resolution).
		bool						MinuteResolved	= false;
		std::string					MinuteRequested;
		std::string					MinuteSymbol;
		bool						MinuteMismatch	= false;
		int							MinuteDays		= 0;
		bool						HiddenReady		= false;
		// The minutes the engine read: a prefix of the source, hashed (a reload under it rebuilds).
		int64_t						HashedCount		= 0;
		uint64_t					MinuteHash		= FNV64_BASIS;
		int64_t						FirstMinute		= 0;
		// The hidden daily chart (TPO Profile's and If/Then's).
		bool						DailyResolved	= false;
		std::string					DailyRequested;
		std::string					DailySymbol;
		uint32_t					DailySignature	= 0;
		// Translucent ranges sent: (start bar, id) -> signature.
		std::map<uint64_t, uint32_t>	Sent;
		uint32_t					RangesKey	= 0;
		int							TagBar		= -1;
		// The daily levels (spec B.4.7): NinjaTrader's source of the engine's load, made again with each
		// engine; the file re-read at most every 5 s while live (wall clock).
		LevelFileSource				Levels;
		uint64_t					LevelsReadMs	= 0;
		bool						LevelsRead		= false;
		std::function<uint64_t()>	NowMs			= []() { return (uint64_t)GetTickCount64(); };	// tests replace it
		// The Discord sender (spec D), made when the switch and a valid URL are set; the setup notice.
		std::unique_ptr<DiscordSender>	Discord;
		uint64_t					DiscordKey		= 0;
		std::string					DiscordSetupWarning;
		// Diagnostics (tests, harness).
		int							Rebuilds	= 0;
		int							RangeAdds	= 0;
		int							RangeDeletes = 0;
		int							Resolves	= 0;
	};

	StudyState& GetState(SCStudyInterfaceRef sc)
	{
		void*& slot = sc.GetPersistentPointer(PP_STATE);
		if (slot == nullptr)
			slot = new StudyState();
		return *static_cast<StudyState*>(slot);
	}

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

	// ---- Settings from the inputs and subgraphs (spec A.5) ----

	bool Visible(const s_SCSubgraph_260& g)
	{
		return g.DrawStyle != DRAWSTYLE_HIDDEN && g.DrawStyle != DRAWSTYLE_IGNORE;
	}

	// COLORREF (0x00BBGGRR) -> NinjaTrader's ARGB.
	uint32_t ArgbOf(uint32_t colorref, uint32_t alpha = 255)
	{
		return (alpha << 24) | ((uint32_t)GetRValue(colorref) << 16) | ((uint32_t)GetGValue(colorref) << 8) | (uint32_t)GetBValue(colorref);
	}

	uint32_t ColorRefOf(uint32_t argb)
	{
		return RGB((argb >> 16) & 255, (argb >> 8) & 255, argb & 255);
	}

	// NinjaTrader's alpha from a transparency 0-100 (NT:991, NT:1018, NT:2042): integer division.
	uint32_t AlphaOfTransparency(int transparency)
	{
		return (uint32_t)(255 * (100 - (std::max)(0, (std::min)(100, transparency))) / 100);
	}

	std::string StyleName(int style)
	{
		switch (style)
		{
			case LINESTYLE_DASH:		return "Dashed";
			case LINESTYLE_DOT:			return "Dotted";
			case LINESTYLE_DASHDOT:		return "DashDot";
			case LINESTYLE_DASHDOTDOT:	return "DashDotDot";
			default:					return "Solid";
		}
	}

	int StyleOf(const std::string& name)
	{
		return name == "Dashed" ? LINESTYLE_DASH : name == "Dotted" ? LINESTYLE_DOT : name == "DashDot" ? LINESTYLE_DASHDOT
			: name == "DashDotDot" ? LINESTYLE_DASHDOTDOT : LINESTYLE_SOLID;
	}

	// NinjaTrader's "Label Text Color": Transparent (Use Labels Color off) = the line's own color.
	uint32_t LabelColorOf(const s_SCSubgraph_260& g)
	{
		return g.UseLabelsColor ? ArgbOf(g.LabelsColor) : 0x00FFFFFFu;
	}

	// A text input: "" when it is empty (GetString returns "Unset" for an empty string).
	std::string StringInput(SCStudyInterfaceRef sc, int input)
	{
		const char* text = sc.Input[input].GetPathAndFileName();
		return text != nullptr ? text : "";
	}

	// A "Show Labels / Label Size" input (spec A.1 rule 3): NinjaTrader's sizes, then Off.
	template <size_t N>
	void ReadLabels(SCStudyInterfaceRef sc, int input, const char* const (&list)[N], std::string& size, bool& show)
	{
		const unsigned index = sc.Input[input].GetIndex();
		show = index < N;
		if (show)
			size = list[index];
	}

	Settings ReadSettings(SCStudyInterfaceRef sc)
	{
		Settings s;
		auto in = [&sc](int i) -> s_SCInput_145& { return sc.Input[i]; };
		auto sg = [&sc](int k) -> const s_SCSubgraph_260& { return sc.Subgraph[k]; };
		auto yes = [&](int i) { return in(i).GetYesNo() != 0; };
		auto color = [&](int k, uint32_t alpha = 255) { return ArgbOf(sg(k).PrimaryColor, alpha); };
		auto width = [&](int k) { return (int)sg(k).LineWidth; };
		auto style = [&](int k) { return StyleName(sg(k).LineStyle); };
		auto shown = [&](int k) { return Visible(sg(k)); };

		// 1. Global
		s.row_scale			= Choice(ROW_SCALES, in(IN_ROW_SCALE).GetIndex());
		const double tick	= in(IN_MANUAL_TICK).GetDouble();
		s.tick_auto			= tick == 0;
		s.tick_manual_val	= tick > 0 ? tick : 0.25;
		s.layer_top_pick	= Choice(TOP_PICKS, in(IN_FORCE_ON_TOP).GetIndex());
		s.HideAllLabels		= yes(IN_HIDE_ALL_LABELS);
		s.ShowPriceTags		= yes(IN_SHOW_TAGS);
		s.tzguard_enable	= yes(IN_TZ_GUARD);
		// 2. Levels. lvl_text: the paste box until the study puts the accepted document there (spec B.4.7).
		s.lvl_paste			= StringInput(sc, IN_LEVELS_TEXT);
		s.levels_file		= StringInput(sc, IN_LEVELS_FILE);
		s.lvl_text			= s.lvl_paste;
		s.lvl_color_flip	= yes(IN_LVL_FLIP);
		s.lvl_flip_atr		= in(IN_LVL_FLIP_ATR).GetDouble();
		s.lvl_showZones		= yes(IN_LVL_SHOW_ZONES);
		s.lvl_zone_mode		= Choice(ZONE_MODES, in(IN_LVL_ZONE_MODE).GetIndex());
		s.lvl_zone_atr_pct	= in(IN_LVL_ZONE_ATR_PCT).GetDouble();
		s.lvl_zoneWidthTicks = in(IN_LVL_ZONE_TICKS).GetInt();
		s.lvl_zoneOpacity	= in(IN_LVL_ZONE_TRANSP).GetInt();
		ReadLabels(sc, IN_LVL_LABELS, LVL_SIZES, s.lvl_text_size_opt, s.LabelsLevels);
		s.lvl_x_offset		= in(IN_LVL_LABEL_OFFSET).GetInt();
		s.lvl_alerts		= yes(IN_LVL_ALERTS);
		s.lvl_alert_ip		= yes(IN_LVL_ALERT_PIVOT);
		s.lvl_alert_bull	= yes(IN_LVL_ALERT_RES);
		s.lvl_alert_bear	= yes(IN_LVL_ALERT_SUPP);
		s.lvl_ip_color		= color(SG_PIVOT);
		s.lvl_bull_color	= color(SG_RES);
		s.lvl_bear_color	= color(SG_SUPP);
		// NinjaTrader's shared width, style, Show Level Lines and label color: the PIVOT subgraph's; each
		// kind's own subgraph decides its lines when drawn (spec B.4.4, superset).
		s.lvl_thickness		= width(SG_PIVOT);
		s.lvl_style_in		= style(SG_PIVOT);
		s.lvl_showLine		= shown(SG_PIVOT) || shown(SG_RES) || shown(SG_SUPP);
		s.lvl_zone_style_in	= style(SG_LEVEL_ZONE_BORDER);
		s.lvl_txt_c			= LabelColorOf(sg(SG_PIVOT));
		// 3. Prev Day
		s.pd_use_rth		= yes(IN_PD_USE_RTH);
		s.pd_sess_time		= StringInput(sc, IN_PD_SESSION);
		ReadLabels(sc, IN_PD_LABELS, SIZES_4, s.pd_lb_size_in, s.LabelsPriorDay);
		s.pd_offset_val		= in(IN_PD_LABEL_OFFSET).GetInt();
		s.pd_alert_hl		= yes(IN_PD_ALERT_HL);
		s.pd_showH			= shown(SG_PD_HIGH);
		s.pd_showL			= shown(SG_PD_LOW);
		s.pd_showOpen		= shown(SG_PD_OPEN);
		s.pd_enable			= s.pd_showH || s.pd_showL || s.pd_showOpen;
		s.pd_high_c			= color(SG_PD_HIGH);
		s.pd_low_c			= color(SG_PD_LOW);
		s.pd_open_c			= color(SG_PD_OPEN);
		s.pd_high_width		= width(SG_PD_HIGH);
		s.pd_low_width		= width(SG_PD_LOW);
		s.pd_open_width		= width(SG_PD_OPEN);
		s.pd_style_in		= style(SG_PD_HIGH);
		s.pd_txt_c			= LabelColorOf(sg(SG_PD_HIGH));
		// 4. Prev Value
		s.cc_enable			= yes(IN_CC_ENABLE);
		s.cc_va_pct			= in(IN_CC_VA_PCT).GetDouble();
		s.cc_sess_def		= StringInput(sc, IN_CC_SESSION);
		ReadLabels(sc, IN_CC_LABELS, SIZES_4, s.cc_lb_size_in, s.LabelsPriorValue);
		s.cc_lb_offset		= in(IN_CC_LABEL_OFFSET).GetInt();
		const uint32_t vaAlpha = AlphaOfTransparency(100 - in(IN_CC_VA_OPACITY).GetInt());
		const uint32_t fillAlpha = AlphaOfTransparency(in(IN_CC_FILL_TRANSP).GetInt());
		s.cc_alert_va		= yes(IN_CC_ALERT_VA);
		s.cc_alert_80		= yes(IN_CC_ALERT_80);
		s.cc_show_poc		= shown(SG_PD_POC);
		s.cc_show_vah		= shown(SG_PD_VAH);
		s.cc_show_val		= shown(SG_PD_VAL);
		s.pd_poc_c			= color(SG_PD_POC);
		s.pd_vah_c			= color(SG_PD_VAH, vaAlpha);
		s.pd_val_c			= color(SG_PD_VAL, vaAlpha);
		s.cc_poc_width		= width(SG_PD_POC);
		s.cc_vah_width		= width(SG_PD_VAH);
		s.cc_val_width		= width(SG_PD_VAL);
		s.cc_poc_style_in	= style(SG_PD_POC);
		s.cc_txt_c			= LabelColorOf(sg(SG_PD_POC));
		s.cc_showFill		= shown(SG_FILL80);
		s.cc_col_active		= ArgbOf(sg(SG_FILL80).PrimaryColor, fillAlpha);
		s.cc_col_conf		= ArgbOf(sg(SG_FILL80).SecondaryColor, fillAlpha);
		// 5. OVN
		s.amt_enable		= yes(IN_OVN_ENABLE);
		s.amt_sess			= StringInput(sc, IN_OVN_SESSION);
		s.amt_del_sess		= StringInput(sc, IN_OVN_DELETE);
		ReadLabels(sc, IN_OVN_LABELS, SIZES_4, s.amt_lb_size_in, s.amt_showLb);
		s.amt_offset		= in(IN_OVN_LABEL_OFFSET).GetInt();
		s.amt_alert_ovn		= yes(IN_OVN_ALERT);
		s.amt_c_hi			= color(SG_OVN_HIGH);
		s.amt_c_lo			= color(SG_OVN_LOW);
		s.amt_width			= (std::max)(1, width(SG_OVN_HIGH));
		s.amt_style_in		= style(SG_OVN_HIGH);
		s.amt_c_txt_hi		= LabelColorOf(sg(SG_OVN_HIGH));
		s.amt_c_txt_lo		= LabelColorOf(sg(SG_OVN_LOW));
		// 6. IB
		s.ib_enable			= yes(IN_IB_ENABLE);
		s.ib_session		= StringInput(sc, IN_IB_SESSION);
		s.ib_extend			= Choice(IB_EXTENDS, in(IN_IB_EXTEND).GetIndex());
		s.ib_limit_ext		= yes(IN_IB_LIMIT_EXT);
		s.ib_stop_time		= StringInput(sc, IN_IB_STOP_TIME);
		ReadLabels(sc, IN_IB_LABELS, IB_SIZES, s.ib_label_size, s.ib_show_labels);
		s.ib_label_loc		= Choice(IB_LOCATIONS, in(IN_IB_LABEL_LOC).GetIndex());
		s.ib_lbl_offset		= in(IN_IB_LABEL_OFFSET).GetInt();
		s.ib_alert_ibh		= yes(IN_IB_ALERT_HIGH);
		s.ib_alert_ibl		= yes(IN_IB_ALERT_LOW);
		s.ib_alert_time		= StringInput(sc, IN_IB_ALERT_WINDOW);
		s.ib_show_mid		= shown(SG_IB_MID);
		s.ib_col_hi			= color(SG_IB_HIGH);
		s.ib_col_lo			= color(SG_IB_LOW);
		s.ib_col_mid		= color(SG_IB_MID);
		s.ib_lvl_width		= width(SG_IB_HIGH);
		s.ib_style_main		= style(SG_IB_HIGH);
		s.ib_style_int		= style(SG_IB_MID);
		s.ib_txt_c			= LabelColorOf(sg(SG_IB_HIGH));
		// 7. VWAP
		const int vwapStart	= in(IN_VWAP_START).GetTime(), vwapEnd = in(IN_VWAP_END).GetTime();
		s.vwap_start_h		= vwapStart / 3600;
		s.vwap_start_m		= vwapStart % 3600 / 60;
		s.vwap_end_h		= vwapEnd / 3600;
		s.vwap_end_m		= vwapEnd % 3600 / 60;
		s.vwap_alert		= yes(IN_VWAP_ALERT);
		s.vwap_enable		= shown(SG_VWAP);
		s.vwap_col			= color(SG_VWAP);
		s.vwap_width		= width(SG_VWAP);
		s.vwap_style		= style(SG_VWAP);
		// 8. Opens
		ReadLabels(sc, IN_OPEN_LABELS, SIZES_5, s.cc_open_lb_size, s.LabelsDOpen);
		s.cc_open_offset	= in(IN_OPEN_LABEL_OFFSET).GetInt();
		ReadLabels(sc, IN_WK_OPEN_LABELS, SIZES_5, s.wk_open_lb_size, s.LabelsWkOpen);
		s.LabelsOpens		= s.LabelsDOpen || s.LabelsWkOpen;
		s.wk_open_offset	= in(IN_WK_OPEN_LABEL_OFFSET).GetInt();
		s.wk_alert_open		= yes(IN_WK_OPEN_ALERT);
		s.cc_showOpen		= shown(SG_DOPEN);
		s.cc_c_open			= color(SG_DOPEN);
		s.cc_open_width		= width(SG_DOPEN);
		s.cc_open_style		= style(SG_DOPEN);
		s.wk_showOpen		= shown(SG_WK_OPEN);
		s.wk_c_open			= color(SG_WK_OPEN);
		s.wk_open_width		= width(SG_WK_OPEN);
		s.wk_open_style		= style(SG_WK_OPEN);
		s.opens_txt_c		= LabelColorOf(sg(SG_DOPEN));
		// 9. Prev Week
		ReadLabels(sc, IN_PW_LABELS, SIZES_4, s.pw_lb_size_in, s.LabelsPriorWeek);
		s.pw_offset			= in(IN_PW_LABEL_OFFSET).GetInt();
		s.pw_alert_hl		= yes(IN_PW_ALERT);
		s.pw_showH			= shown(SG_PW_HIGH);
		s.pw_showL			= shown(SG_PW_LOW);
		s.pw_enable			= s.pw_showH || s.pw_showL;
		s.pw_col			= color(SG_PW_HIGH);
		s.pw_width			= width(SG_PW_HIGH);
		s.pw_style_in		= style(SG_PW_HIGH);
		s.pw_c_txt			= LabelColorOf(sg(SG_PW_HIGH));
		// 10. Prev Month
		ReadLabels(sc, IN_PM_LABELS, SIZES_4, s.macro_text_size, s.LabelsPriorMonth);
		s.macro_offset		= in(IN_PM_LABEL_OFFSET).GetInt();
		s.macro_alert_lvl	= yes(IN_PM_ALERT);
		s.macro_show_month	= shown(SG_PM_VAH) || shown(SG_PM_VAL);
		s.macro_show_poc	= shown(SG_PM_POC);
		s.macro_show_hl		= shown(SG_PM_HIGH) || shown(SG_PM_LOW);
		s.macro_color		= color(SG_PM_VAH);
		s.macro_width		= width(SG_PM_VAH);
		s.macro_style		= style(SG_PM_VAH);
		s.macro_poc_color	= color(SG_PM_POC);
		s.macro_poc_width	= width(SG_PM_POC);
		s.macro_poc_style	= style(SG_PM_POC);
		s.macro_txt_c		= LabelColorOf(sg(SG_PM_VAH));
		// 11. Profile
		s.mvp_master		= yes(IN_MVP_ENABLE);
		s.mvp_tf_mode		= Choice(PERIODS, in(IN_MVP_PERIOD).GetIndex());
		s.mvp_sess_time		= StringInput(sc, IN_MVP_SESSION);
		s.mvp_sess_dur		= in(IN_MVP_SESSION_DURATION).GetDouble();
		s.mvp_calc_tf		= std::to_string(in(IN_MVP_CALC_PRECISION).GetInt());
		s.mvp_row_size		= in(IN_MVP_ROW_SIZE).GetDouble();
		s.mvp_val_pct		= in(IN_MVP_VA_PCT).GetDouble();
		s.mvp_profile_width	= in(IN_MVP_WIDTH).GetInt();
		s.mvp_align_right	= yes(IN_MVP_ALIGN_RIGHT);
		s.mvp_offset		= in(IN_MVP_OFFSET).GetInt();
		s.mvp_hist_va_transp	= in(IN_MVP_VA_TRANSP).GetInt();
		s.mvp_hist_out_transp	= in(IN_MVP_OUT_TRANSP).GetInt();
		ReadLabels(sc, IN_MVP_LABELS, SIZES_5, s.mvp_lb_size, s.LabelsProfiles);
		s.mvp_use_cur_alerts	= yes(IN_MVP_ALERTS);
		s.mvp_alert_time	= StringInput(sc, IN_MVP_ALERT_WINDOW);
		s.mvp_c_hist_va		= color(SG_VA_HIST);
		s.mvp_c_hist_out	= color(SG_OUT_HIST);
		s.mvp_show_poc		= shown(SG_DEV_POC);
		s.mvp_c_poc			= color(SG_DEV_POC);
		s.mvp_poc_width		= width(SG_DEV_POC);
		s.mvp_poc_style		= style(SG_DEV_POC);
		s.mvp_txt_c			= LabelColorOf(sg(SG_DEV_POC));
		s.mvp_show_vah		= shown(SG_DEV_VAH);
		s.mvp_show_val		= shown(SG_DEV_VAL);
		s.mvp_c_levels		= color(SG_DEV_VAH);
		s.mvp_lvl_width		= width(SG_DEV_VAH);
		s.mvp_lvl_style		= style(SG_DEV_VAH);
		// 12. Walls
		s.mvp_wall_transp	= in(IN_WALL_TRANSP).GetInt();
		s.mvp_extend_walls	= yes(IN_WALL_EXTEND);
		s.mvp_smooth_len	= in(IN_WALL_SMOOTHING).GetInt();
		s.mvp_min_wall_dist	= in(IN_WALL_MIN_DISTANCE).GetInt();
		s.mvp_use_auto_scale	= yes(IN_WALL_AUTO_SCALE);
		s.mvp_scale_start	= in(IN_WALL_START_MULT).GetDouble();
		s.mvp_scale_end		= in(IN_WALL_END_MULT).GetDouble();
		s.mvp_vol_mult		= in(IN_WALL_FIXED_MULT).GetDouble();
		s.mvp_show_walls	= shown(SG_WALL);
		s.mvp_c_wall_base	= color(SG_WALL);
		s.mvp_w_wall		= width(SG_WALL);
		s.mvp_wall_style	= style(SG_WALL);
		// 13. TPO
		s.sp_rth_session	= StringInput(sc, IN_TPO_SESSION);
		s.sp_tpo_minutes	= in(IN_TPO_MINUTES).GetInt();
		s.sp_ticks_per_block	= in(IN_TPO_TICKS_PER_BLOCK).GetInt();
		s.sp_min_ticks		= in(IN_TPO_MIN_SINGLE_TICKS).GetInt();
		s.sp_filter_tails	= yes(IN_TPO_FILTER_TAILS);
		s.sp_tail_max		= in(IN_TPO_MAX_TAIL).GetInt();
		s.sp_max_days		= in(IN_TPO_MAX_DAYS).GetInt();
		s.sp_color_hist		= color(SG_SP, AlphaOfTransparency(in(IN_SP_TRANSP).GetInt()));
		ReadLabels(sc, IN_POOR_LABELS, SIZES_5, s.sp_poor_lb_size, s.LabelsPoor);
		s.sp_border_c		= color(SG_SP_BORDER);
		s.sp_border_w		= shown(SG_SP_BORDER) ? (std::max)(1, (std::min)(4, width(SG_SP_BORDER))) : 0;
		s.sp_border_style	= style(SG_SP_BORDER);
		s.sp_show_poor		= shown(SG_POOR_HIGH) || shown(SG_POOR_LOW);
		s.sp_col_poor_h		= color(SG_POOR_HIGH);
		s.sp_col_poor_l		= color(SG_POOR_LOW);
		s.sp_poor_width		= width(SG_POOR_HIGH);
		s.sp_poor_style_in	= style(SG_POOR_HIGH);
		s.sp_poor_txt_c		= LabelColorOf(sg(SG_POOR_HIGH));
		// 14. nPOC
		s.npoc_enable		= yes(IN_NPOC_ENABLE);
		const double bin	= in(IN_NPOC_BIN).GetDouble();
		s.amt_vauto			= bin == 0;
		s.amt_vres			= bin > 0;
		s.amt_res_val		= bin > 0 ? bin : 0.25;
		ReadLabels(sc, IN_NPOC_LABELS, SIZES_5, s.npoc_lb_size, s.LabelsNakedPoc);
		s.npoc_lb_offset	= in(IN_NPOC_LABEL_OFFSET).GetInt();
		s.npoc_alert		= yes(IN_NPOC_ALERT);
		s.npoc_d_show		= shown(SG_NPOC_DAILY);
		s.npoc_w_show		= shown(SG_NPOC_WEEKLY);
		s.npoc_m_show		= shown(SG_NPOC_MONTHLY);
		s.npoc_c			= color(SG_NPOC_DAILY);
		s.npoc_c_w			= color(SG_NPOC_WEEKLY);
		s.npoc_c_m			= color(SG_NPOC_MONTHLY);
		s.npoc_w_d			= width(SG_NPOC_DAILY);
		s.npoc_w_w			= width(SG_NPOC_WEEKLY);
		s.npoc_w_m			= width(SG_NPOC_MONTHLY);
		s.npoc_style_in		= style(SG_NPOC_DAILY);
		s.npoc_txt_c		= LabelColorOf(sg(SG_NPOC_DAILY));
		// 15. Inventory
		s.inv_enable		= yes(IN_INV_ENABLE);
		const int globex	= in(IN_INV_GLOBEX_START).GetTime(), rthOpen = in(IN_INV_RTH_OPEN).GetTime();
		s.inv_start_h		= globex / 3600;
		s.inv_start_minute	= globex / 60;
		s.inv_end_h			= rthOpen / 3600;
		s.inv_end_m			= rthOpen % 3600 / 60;
		ReadLabels(sc, IN_INV_LABELS, SIZES_4, s.inv_lb_size_in, s.LabelsInventory);
		s.inv_offset		= in(IN_INV_LABEL_OFFSET).GetInt();
		s.inv_alert			= yes(IN_INV_ALERT);
		s.inv_show_line		= shown(SG_SETTLE) || shown(SG_TRAP);
		s.inv_c_settle		= color(SG_SETTLE);
		s.inv_settle_width	= (std::max)(1, (std::min)(10, width(SG_SETTLE)));
		s.inv_settle_style	= style(SG_SETTLE);
		s.inv_txt_c			= LabelColorOf(sg(SG_SETTLE));
		s.inv_c_trap		= color(SG_TRAP);
		s.inv_width			= width(SG_TRAP);
		s.inv_style_in		= style(SG_TRAP);
		s.inv_txt_trap		= sg(SG_TRAP).Name.GetChars();
		// 16. Spike
		s.spikeTimeRange	= StringInput(sc, IN_SPIKE_WINDOW);
		ReadLabels(sc, IN_SPIKE_LABELS, SIZES_4, s.spike_lbl_size, s.LabelsSpike);
		s.spike_offset		= in(IN_SPIKE_LABEL_OFFSET).GetInt();
		s.spike_alert		= yes(IN_SPIKE_ALERT);
		s.spike_show_sup	= shown(SG_SPIKE_SUP);
		s.spike_show_res	= shown(SG_SPIKE_RES);
		s.showSpike			= s.spike_show_sup || s.spike_show_res;
		s.spike_c_sup		= color(SG_SPIKE_SUP);
		s.spike_c_res		= color(SG_SPIKE_RES);
		s.spike_width		= width(SG_SPIKE_SUP);
		s.spike_style		= style(SG_SPIKE_SUP);
		s.spike_txt_c		= LabelColorOf(sg(SG_SPIKE_SUP));
		// 17. Dashboard
		s.tbl_show			= yes(IN_TBL_SHOW);
		s.tbl_pos			= Choice(TBL_POSITIONS, in(IN_TBL_POSITION).GetIndex());
		s.tbl_size			= Choice(SIZES_4, in(IN_TBL_TEXT_SIZE).GetIndex());
		s.tbl_session		= StringInput(sc, IN_TBL_SESSION);
		s.context_session	= StringInput(sc, IN_CONTEXT_SESSION);
		s.daily_atr_length	= in(IN_ATR_PERIOD).GetInt();
		// 18. Alerts
		s.alertcap_enable	= yes(IN_CAP_ENABLE);
		s.alertcap_max		= in(IN_CAP_MAX).GetInt();
		s.alertcap_window_min	= in(IN_CAP_WINDOW).GetInt();
		s.LevelAlertMode	= Choice(ALERT_MODES, in(IN_ALERT_MODE).GetIndex());
		s.AlertZoneTicks	= in(IN_ALERT_ZONE_TICKS).GetInt();
		// 20. NinjaTrader Limits: constants (spec A.4)
		s.MaxProfileRows	= MAX_PROFILE_ROWS;
		s.MaxStructures		= MAX_STRUCTURES;
		return s;
	}

	// ---- Data sources ----

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

	// The bar where the newest frame's single prints end (fills and borders): the current bar's end + 30
	// minutes, cut at the Session Times' end (SinglePrintReach, SinglePrintEndBar).
	int SinglePrintEndNow(SCStudyInterfaceRef sc, const StudyState& st)
	{
		const int index = st.Core.View.Bar.Index;
		const int reach = index >= 0 && index < (int)st.Bars.size() ? SinglePrintReach(st.Bars[(size_t)index], SessionsOf(sc)) : 1800;
		return SinglePrintEndBar(index, sc.SecondsPerBar, reach);
	}

	// This chart's bars from `from` on (spec C.2.1). True when a bar the engine already took changed
	// (a backfill, a correction, an inserted bar): the engine is built again.
	bool ReadBars(SCStudyInterfaceRef sc, StudyState& st, int from, double tick)
	{
		const int n = sc.ArraySize;
		const ChartSessions sessions = SessionsOf(sc);
		bool changed = (int)st.Bars.size() > n && st.Core.CommittedIndex >= n;
		const int oldCount = (int)st.Bars.size();
		st.Bars.resize((size_t)(std::max)(0, n));
		for (int i = (std::max)(0, from); i < n; i++)
		{
			ChartBar b;
			b.Su = Micros(sc.BaseDateTimeIn[i]);
			const bool hasNext = i + 1 < n;
			b.Eu = TimeBarEnd(b.Su, sc.SecondsPerBar, hasNext, hasNext ? Micros(sc.BaseDateTimeIn[i + 1]) : 0,
				SessionCutAfter(FloorDiv(b.Su, US_PER_SECOND), sessions));
			b.S			= st.Clock.Of(b.Su);
			b.E			= st.Clock.Of(b.Eu);
			b.Open		= SnapToTick(sc.Open[i], tick);
			b.High		= SnapToTick(sc.High[i], tick);
			b.Low		= SnapToTick(sc.Low[i], tick);
			b.Close		= SnapToTick(sc.Close[i], tick);
			b.Volume	= sc.Volume[i];
			b.Empty		= IsEmptyColumn(sc.Volume[i], sc.NumberOfTrades[i], sc.Open[i], sc.High[i], sc.Low[i], sc.Close[i], i > 0, i > 0 ? sc.Close[i - 1] : 0.0f);
			if (i < oldCount && i <= st.Core.CommittedIndex && !b.SameAs(st.Bars[(size_t)i]))
				changed = true;
			st.Bars[(size_t)i] = b;
		}
		return changed;
	}

	std::string ChartSymbol(SCStudyInterfaceRef sc, int chartNumber)
	{
		const SCString symbol = sc.GetChartSymbol(chartNumber);
		return symbol.GetChars();
	}

	bool SameSessionTimes(const n_ACSIL::s_ChartSessionTimes& a, const n_ACSIL::s_ChartSessionTimes& b)
	{
		if (a.StartTime.GetTimeInSeconds() != b.StartTime.GetTimeInSeconds() || a.EndTime.GetTimeInSeconds() != b.EndTime.GetTimeInSeconds()
			|| (a.UseEveningSessionTimes != 0) != (b.UseEveningSessionTimes != 0) || a.LoadWeekendDataSetting != b.LoadWeekendDataSetting)
			return false;
		return a.UseEveningSessionTimes == 0 || (a.EveningStartTime.GetTimeInSeconds() == b.EveningStartTime.GetTimeInSeconds()
			&& a.EveningEndTime.GetTimeInSeconds() == b.EveningEndTime.GetTimeInSeconds());
	}

	// Whether chart `chart` holds this chart's minutes: 1-minute intraday bars with this chart's
	// Session Times and time zone.
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

	// The hidden chart's Days to Load: 0 takes this chart's (NinjaTrader's minute series covers the
	// chart's range); with Load Chart Data by Date Range, the days from its start date to today.
	int MinuteDaysToLoad(SCStudyInterfaceRef sc)
	{
		if (sc.LoadChartDataByDateRange == 0 || sc.ChartDataStartDate <= 0)
			return 0;
		return (std::max)(1, sc.CurrentSystemDateTime.GetDate() - sc.ChartDataStartDate + 1);
	}

	// A hidden 1-minute chart of this chart's symbol, continuous-contract option, Session Times and
	// time zone, found or opened (Periodic / Auto Anchored VP's, so they share it). Sierra Chart hands
	// every chart and study asking for the same settings the same chart: it is never rewritten.
	int OpenMinuteChart(SCStudyInterfaceRef sc, int prior, int days)
	{
		n_ACSIL::s_ChartSessionTimes times;
		sc.GetSessionTimesFromChart(sc.ChartNumber, times);
		s_ACSOpenChartParameters p;
		p.PriorChartNumber			= prior;
		p.ChartDataType				= INTRADAY_DATA;
		p.Symbol					= sc.GetRealTimeSymbol();
		p.IntradayBarPeriodType		= IBPT_DAYS_MINS_SECS;
		p.IntradayBarPeriodLength	= 60;
		p.DaysToLoad				= days;
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

	// The hidden chart's number (0: none), resolved on a full recalculation, while there is none,
	// when this chart's symbol changed, and when the chart no longer holds what it held.
	int ResolveMinuteChart(SCStudyInterfaceRef sc, StudyState& st, int days)
	{
		int& chart = sc.GetPersistentInt(PI_MINUTE_CHART);
		const std::string symbol = sc.GetRealTimeSymbol().GetChars();
		const bool newSymbol = !st.MinuteResolved || symbol != st.MinuteRequested;
		if (st.MinuteMismatch && !sc.IsFullRecalculation && !newSymbol)
			return 0;
		int prior = chart;
		bool resolve = sc.IsFullRecalculation || chart == 0 || newSymbol || days != st.MinuteDays;
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
			chart = OpenMinuteChart(sc, prior, days);
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
		st.MinuteDays		= days;
		return chart;
	}

	// The first date at which two daily histories differ (INT_MAX: none).
	int FirstDailyDifference(const DailyHistory& a, const DailyHistory& b)
	{
		const size_t n = (std::min)(a.Data.size(), b.Data.size());
		for (size_t i = 0; i < n; i++)
		{
			const DailyValue& x = a.Data[i];
			const DailyValue& y = b.Data[i];
			if (x.Date != y.Date || x.Close != y.Close || x.High != y.High || x.Low != y.Low || !(x.Atr == y.Atr || (x.Atr != x.Atr && y.Atr != y.Atr))
				|| !(x.Atr14 == y.Atr14 || (x.Atr14 != x.Atr14 && y.Atr14 != y.Atr14)))
				return (std::min)(x.Date, y.Date);
		}
		if (a.Data.size() != b.Data.size())
			return a.Data.size() > n ? a.Data[n].Date : b.Data[n].Date;
		return INT_MAX;
	}

	// The hidden daily chart (TPO Profile's ReadDailyChart, the parameters If/Then uses, so they all
	// share it): every daily bar goes to DailyHistory in date order (spec C.2.4). The history is built
	// again when its signature changes (the chart, its bar count, the last completed bar, the ATR
	// period); `changed` then holds the earliest date that differs (a committed bar that could have
	// read it rebuilds the engine; a new day's bar does not). Returns the chart number (0: none).
	int ReadDailyChart(SCStudyInterfaceRef sc, StudyState& st, int atrLength, double tick, int& changed, bool& downloading)
	{
		changed = INT_MAX;
		downloading = false;
		int& chartNumber = sc.GetPersistentInt(PI_DAILY_CHART);
		const std::string symbol = sc.GetRealTimeSymbol().GetChars();
		bool resolve = sc.IsFullRecalculation || chartNumber == 0 || !st.DailyResolved || symbol != st.DailyRequested;
		if (!resolve && ChartSymbol(sc, chartNumber) != st.DailySymbol)
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
			st.DailyResolved	= true;
			st.DailyRequested	= symbol;
			st.DailySymbol		= chartNumber != 0 ? ChartSymbol(sc, chartNumber) : std::string();
		}
		uint32_t signature = 2166136261u;
		signature = Fnv1a(signature, &atrLength, sizeof(atrLength));
		signature = Fnv1a(signature, &tick, sizeof(tick));
		DailyHistory history(atrLength);
		if (chartNumber != 0)
		{
			downloading = sc.ChartIsDownloadingHistoricalData(chartNumber) != 0;
			SCGraphData daily;
			sc.GetChartBaseData(chartNumber, daily);
			SCDateTimeArray times;
			sc.GetChartDateTimeArray(chartNumber, times);
			const int count = (std::min)(daily[SC_LAST].GetArraySize(), times.GetArraySize());
			signature = Fnv1a(signature, &chartNumber, sizeof(chartNumber));
			signature = Fnv1a(signature, st.DailySymbol.data(), st.DailySymbol.size());
			signature = Fnv1a(signature, &count, sizeof(count));
			// What can change while the chart is open: the last completed bar and the date of the
			// developing one; no trading date reads the developing bar (Before is strict).
			for (int i = (std::max)(0, count - 2); i < count; i++)
			{
				const int date = times[i].GetDate();
				signature = Fnv1a(signature, &date, sizeof(date));
				if (i == count - 2)
				{
					const float bar[3] = {static_cast<float>(daily[SC_HIGH][i]), static_cast<float>(daily[SC_LOW][i]),
						static_cast<float>(daily[SC_LAST][i])};
					signature = Fnv1a(signature, bar, sizeof(bar));
				}
			}
			if (signature != st.DailySignature)
				for (int i = 0; i < count; i++)
					history.Add(times[i].GetDate(), SnapToTick(daily[SC_HIGH][i], tick), SnapToTick(daily[SC_LOW][i], tick),
						SnapToTick(daily[SC_LAST][i], tick));
		}
		if (signature != st.DailySignature)
		{
			changed = st.DailySignature == 0 ? INT_MIN : FirstDailyDifference(st.Core.Daily, history);
			if (st.Core.Daily.Ra.Period != history.Ra.Period)
				changed = INT_MIN;
			st.Core.Daily		= history;
			st.DailySignature	= signature;
		}
		return chartNumber;
	}

	// This chart's newest trade: sc.LatestDateTimeForLastBar inside the last bar holding trades,
	// else that bar's start (Periodic VP's NewestTrade).
	int64_t NewestTrade(const std::vector<ChartBar>& bars, int64_t latest)
	{
		int j = (int)bars.size() - 1;
		while (j > 0 && bars[(size_t)j].Empty)
			j--;
		if (j < 0)
			return latest;
		const ChartBar& b = bars[(size_t)j];
		return latest >= b.Su && latest <= b.Eu ? latest : b.Su;
	}

	// Whether the hidden 1-minute chart reaches this chart's newest trade: its last minute starts at
	// most a minute before that trade's minute. Not checked during a replay.
	bool MinutesCover(int64_t lastMinute, int64_t newest, bool replay)
	{
		return replay || lastMinute >= FloorDiv(newest, US_PER_MINUTE) * US_PER_MINUTE - US_PER_MINUTE;
	}

	// During a replay the hidden 1-minute chart is not replayed with this chart: it already holds the
	// minutes after the replay's time. The forming bar must not take them (NinjaTrader's Playback
	// replays every series in step), so no minute starting after the replay's newest trade is read:
	// sc.LatestDateTimeForLastBar when it lies in the last bar holding trades (Periodic VP's replay
	// clip), else no limit.
	int64_t ReplayReadLimit(const std::vector<ChartBar>& bars, int64_t latest, bool replay)
	{
		if (!replay)
			return INT64_MAX;
		int j = (int)bars.size() - 1;
		while (j > 0 && bars[(size_t)j].Empty)
			j--;
		if (j < 0)
			return INT64_MAX;
		const ChartBar& b = bars[(size_t)j];
		return latest >= b.Su && latest <= b.Eu ? latest : INT64_MAX;
	}

	uint64_t MinuteRecHash(uint64_t h, const MinuteRec& r)
	{
		const double values[5] = {r.Open, r.High, r.Low, r.Close, r.Volume};
		h = Fnv1a64(h, &r.M, sizeof(r.M));
		h = Fnv1a64(h, values, sizeof(values));
		const uint8_t empty = r.Empty ? 1 : 0;
		return Fnv1a64(h, &empty, 1);
	}

	// The price-scale tags (spec B.1.7): the newest frame's line price on the last bar, 0 elsewhere;
	// the bar that was last before keeps nothing; a full recalculation clears every bar.
	void WriteTags(SCStudyInterfaceRef sc, StudyState& st, bool clearAll)
	{
		const int n = sc.ArraySize;
		if (clearAll)
		{
			for (int k : TAG_SUBGRAPHS)
				for (int i = 0; i < n; i++)
					sc.Subgraph[k][i] = 0.0f;
			st.TagBar = -1;
		}
		if (n == 0)
			return;
		if (st.TagBar >= 0 && st.TagBar < n && st.TagBar != n - 1)
			for (int k : TAG_SUBGRAPHS)
				sc.Subgraph[k][st.TagBar] = 0.0f;
		const Settings& cfg = st.Core.Cfg;
		const bool show = cfg.ShowPriceTags && !cfg.HideAllLabels && st.Error.empty() && !st.Waiting && st.Core.HasView;
		for (int t = 0; t < 12; t++)
		{
			float value = 0.0f;
			// A hidden subgraph shows no tag even where its line is in the frame (pmHigh and pmLow, pmVAH
			// and pmVAL share one NinjaTrader switch; the IB lines have none).
			if (show && Visible(sc.Subgraph[TAG_SUBGRAPHS[t]]))
				for (const LineItem& l : st.Core.View.Lines)
					if (l.Name == TAG_LINES[t])
					{
						value = (float)l.Price;
						break;
					}
			sc.Subgraph[TAG_SUBGRAPHS[t]][n - 1] = value;
		}
		st.TagBar = n - 1;
	}

	// ---- Translucent ranges in Sierra Chart ----

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

	// The ranges the newest frame wants (the completed profiles, the 80% Rule fill, the single prints, the
	// daily levels' zones), sorted by key.
	std::vector<RangePiece> DesiredRanges(SCStudyInterfaceRef sc, const StudyState& st)
	{
		std::vector<RangePiece> desired;
		const Settings& cfg = st.Core.Cfg;
		const int count = (int)st.Bars.size();
		HistogramLook va, out;
		va.Show				= Visible(sc.Subgraph[SG_VA_HIST]);
		va.Color			= sc.Subgraph[SG_VA_HIST].PrimaryColor;
		va.Transparency		= (std::max)(0, (std::min)(100, cfg.mvp_hist_va_transp));
		out.Show			= Visible(sc.Subgraph[SG_OUT_HIST]);
		out.Color			= sc.Subgraph[SG_OUT_HIST].PrimaryColor;
		out.Transparency	= (std::max)(0, (std::min)(100, cfg.mvp_hist_out_transp));
		for (const FrameProfile& h : st.Core.View.Profiles)
		{
			if (h.Current || count == 0)
				continue;
			const int anchor = NearestBar(BarPosition(st.Bars, h.End), count);
			const std::vector<RangePiece> pieces = ProfilePieces(h, anchor, cfg.mvp_profile_width, cfg.mvp_align_right, va, out);
			desired.insert(desired.end(), pieces.begin(), pieces.end());
		}
		// The 80% Rule fill: Show 80% Rule Fill is the subgraph's visibility (display only, NT:3260).
		if (cfg.cc_showFill)
		{
			const s_SCSubgraph_260& g = sc.Subgraph[SG_FILL80];
			const std::vector<RangePiece> pieces = Fill80Pieces(st.Core.Samples, st.Core.ViewSamples, st.Bars, g.PrimaryColor, g.SecondaryColor,
				(std::max)(0, (std::min)(100, sc.Input[IN_CC_FILL_TRANSP].GetInt())));
			desired.insert(desired.end(), pieces.begin(), pieces.end());
		}
		// The single prints: Hidden on the Single Print subgraph draws none (they are still tracked). The
		// parts no range can hold (before bar 0, past the last bar when Sierra Chart does not draw ranges
		// there) are the callback's (DrawSinglePrints).
		const s_SCSubgraph_260& sp = sc.Subgraph[SG_SP];
		if (Visible(sp))
			for (const RangePiece& r : SinglePrintPieces(st.Core.View.Zones, st.Bars, SinglePrintEndNow(sc, st), sp.PrimaryColor,
				(std::max)(0, (std::min)(100, sc.Input[IN_SP_TRANSP].GetInt()))))
			{
				const SpanSplit split = SplitSpan(r.StartBar, r.EndBar, count);
				if (!split.HasRange)
					continue;
				RangePiece q	= r;
				q.StartBar		= split.RangeStart;
				q.EndBar		= split.RangeEnd;
				desired.push_back(q);
			}
		// The daily levels' zones (spec C.5.5 ZONE): NinjaTrader fills each across the whole panel (Start =
		// MinValue, NT:2020-2027), so each is a range from bar 0 extended to the chart's end, in the level's color
		// (a flipped level's is the other side's) at the Zone Transparency; its ordinal is its level's place.
		if (count > 0)
		{
			int ordinal = 0;
			for (const ZoneItem& z : st.Core.View.Zones)
			{
				if (z.Start != CT_MIN)
					continue;
				RangePiece r;
				r.StartBar		= 0;
				r.EndBar		= 0;
				r.Id			= RangeId(RK_ZONE, ordinal++, 0);
				r.Top			= z.Top;
				r.Bottom		= z.Bottom;
				r.Color			= ColorRefOf(z.Color);
				r.Transparency	= (std::max)(0, (std::min)(100, cfg.lvl_zoneOpacity));
				r.ExtendToEnd	= true;
				desired.push_back(r);
			}
		}
		std::sort(desired.begin(), desired.end(), [](const RangePiece& a, const RangePiece& b) { return RangeKey(a.StartBar, a.Id) < RangeKey(b.StartBar, b.Id); });
		desired.erase(std::unique(desired.begin(), desired.end(), [](const RangePiece& a, const RangePiece& b) { return RangeKey(a.StartBar, a.Id) == RangeKey(b.StartBar, b.Id); }),
			desired.end());
		return desired;
	}

	// Only ranges that changed are sent (re-adding a start bar and id updates it in place), the ones no
	// longer wanted are deleted, and a call that changes nothing makes no calls (TPO Profile's).
	void UpdateRanges(SCStudyInterfaceRef sc, StudyState& st)
	{
		ForgetRangesOnFullRecalculation(sc, st);
		if (sc.HideStudy || !st.Error.empty() || st.Waiting || !st.Core.HasView)
		{
			DeleteRanges(sc, st);
			return;
		}
		const std::vector<RangePiece> desired = DesiredRanges(sc, st);
		uint32_t key = 2166136261u;
		for (const RangePiece& r : desired)
		{
			const uint32_t signature = RangeSignature(r);
			key = Fnv1a(Fnv1a(Fnv1a(key, &r.StartBar, sizeof(r.StartBar)), &r.Id, sizeof(r.Id)), &signature, sizeof(signature));
		}
		key = key == 0 ? 1 : key;
		if (key == st.RangesKey)
			return;
		auto wanted = [&desired](uint64_t rangeKey)
		{
			const auto found = std::lower_bound(desired.begin(), desired.end(), rangeKey,
				[](const RangePiece& r, uint64_t k) { return RangeKey(r.StartBar, r.Id) < k; });
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
		for (const RangePiece& r : desired)
		{
			const uint32_t signature = RangeSignature(r);
			uint32_t& sent = st.Sent[RangeKey(r.StartBar, r.Id)];
			if (sent == signature)
				continue;
			n_ACSIL::s_LineUntilFutureIntersection line;
			line.StartBarIndex					= r.StartBar;
			line.EndBarIndex					= r.ExtendToEnd ? 0 : r.EndBar;
			line.LineIDForBar					= r.Id;
			line.LineValue						= (float)r.Top;
			line.UseLineValue2					= 1;
			line.LineValue2ForRange				= (float)r.Bottom;
			line.LineColor						= r.Color;
			line.LineWidth						= 0;
			line.LineStyle						= 0;
			line.DrawValueLabel					= 0;
			line.DrawNameLabel					= 0;
			line.AlwaysExtendToEndOfChart		= r.ExtendToEnd ? 1 : 0;
			line.TransparencyLevel				= r.Transparency;
			line.PerformCloseCrossoverComparison = 0;
			sc.AddLineUntilFutureIntersectionEx(line);
			st.RangeAdds++;
			sent = signature;
		}
		st.RangesKey = key;
	}

	// ---- One study call (spec C.1 steps 3-7, C.4) ----

	std::string LogText(const std::string& message)
	{
		return "Tatanka AMT Toolkit: " + message;
	}

	void ProcessCall(SCStudyInterfaceRef sc, StudyState& st)
	{
		AmtCore& core = st.Core;
		const double tick = DecimalTickSize(sc.TickSize);
		const std::string symbol = sc.Symbol.GetChars();
		st.Waiting = false;

		// The CT clock: Sierra Chart's conversion from the chart's time zone (cached per hour; used
		// during this call only).
		const SCString zone = sc.GetChartTimeZone(sc.ChartNumber);
		const std::string zoneName = zone.GetChars();
		st.Clock.Convert = [&sc](int64_t us)
		{
			return sc.ConvertDateTimeFromChartTimeZone(SCDateTime::MICROSECONDS(us), TIMEZONE_CHICAGO).AsMicrosecondsSinceBaseDate();
		};
		if (zoneName != st.ClockZone)
		{
			st.Clock.Offsets.clear();
			st.ClockZone = zoneName;
			st.Bars.clear();
			st.Built = false;
		}

		// This chart's bars (all of them on a full recalculation).
		const int n = sc.ArraySize;
		const bool fullRead = sc.IsFullRecalculation || st.Bars.empty() || n < (int)st.Bars.size() || st.SecondsPerBar != sc.SecondsPerBar;
		const int from = fullRead ? 0 : (std::max)(0, (std::min)(sc.UpdateStartIndex, (int)st.Bars.size() - 1));
		const bool barsChanged = ReadBars(sc, st, from, tick);
		st.SecondsPerBar = sc.SecondsPerBar;

		// The minute source (spec C.2.2): this chart on a 1-minute chart of whole minutes, else the
		// hidden 1-minute chart.
		bool aligned = sc.SecondsPerBar == 60;
		for (const ChartBar& b : st.Bars)
			if (aligned && !b.Empty && b.Su % US_PER_MINUTE != 0)
				aligned = false;
		const int kind = aligned ? SRC_OWN : SRC_HIDDEN;
		const int chart = kind == SRC_HIDDEN ? ResolveMinuteChart(sc, st, MinuteDaysToLoad(sc)) : 0;

		int dailyChangedFrom = INT_MAX;
		bool dailyDownloading = false;
		const int dailyChart = ReadDailyChart(sc, st, core.Cfg.daily_atr_length, tick, dailyChangedFrom, dailyDownloading);
		// A daily bar a committed bar may have read (Before is strict: the trading dates after it).
		const bool dailyChanged = dailyChangedFrom != INT_MAX && core.CommittedIndex >= 0 && core.CommittedIndex < (int)st.Bars.size()
			&& dailyChangedFrom < TradingDate(st.Bars[(size_t)core.CommittedIndex].S);

		// Readiness (spec C.2.2): nothing is processed while a chart downloads or the hidden chart has
		// not reached this chart's newest trade (NinjaTrader's loading text).
		SCGraphData data;
		SCDateTimeArray times;
		ArrayMinutes<SCDateTimeArray, SCFloatArray> hidden;
		BarMinutes own;
		own.Bars = &st.Bars;
		const MinuteSource* minutes = nullptr;
		bool waiting = sc.ChartIsDownloadingHistoricalData(sc.ChartNumber) != 0 || dailyDownloading;
		bool minuteDownloading = false;
		if (kind == SRC_OWN)
			minutes = &own;
		else if (chart == 0)
		{
			// No hidden chart: every bar uses the chart-bar fallback (NinjaTrader's warning), no waiting.
			int& logged = sc.GetPersistentInt(PI_NO_CHART_LOGGED);
			if (logged == 0)
				sc.AddMessageToLog(TEXT_NO_MINUTE_CHART_LOG, 0);
			logged = 1;
		}
		else
		{
			sc.GetPersistentInt(PI_NO_CHART_LOGGED) = 0;
			sc.GetChartBaseData(chart, data);
			sc.GetChartDateTimeArray(chart, times);
			int count = times.GetArraySize();
			const int columns[] = {SC_OPEN, SC_HIGH, SC_LOW, SC_LAST, SC_VOLUME};
			for (int column : columns)
				count = (std::min)(count, data[column].GetArraySize());
			minuteDownloading = sc.ChartIsDownloadingHistoricalData(chart) != 0;
			if (count <= 0 || minuteDownloading)
				waiting = true;
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
				minutes			= &hidden;
			}
		}

		// The engine key (spec C.4).
		uint64_t key = SettingsKey(core.Cfg);
		const int64_t numbers[] = {kind, chart, sc.SecondsPerBar, sc.StartTime1, sc.EndTime1, sc.StartTime2, sc.EndTime2, sc.UseSecondStartEndTimes,
			sc.NewBarAtSessionStart, dailyChart};
		key = Fnv1a64(key, numbers, sizeof(numbers));
		key = Fnv1a64(key, &tick, sizeof(tick));
		key = Fnv1a64Text(Fnv1a64Text(key, symbol), zoneName);
		bool rebuild = !st.Built || key != st.EngineKey || barsChanged || dailyChanged;

		// The minutes the engine read must still be there, unchanged (a reload of the hidden chart).
		if (!rebuild && minutes != nullptr && st.HashedCount > 0)
		{
			const int64_t count = minutes->Count();
			if (count < st.HashedCount || minutes->At(0).M != st.FirstMinute)
				rebuild = true;
			else if (sc.IsFullRecalculation)
			{
				uint64_t h = FNV64_BASIS;
				for (int64_t k = 0; k < st.HashedCount; k++)
					h = MinuteRecHash(h, minutes->At(k));
				rebuild = h != st.MinuteHash;
			}
		}
		if (!waiting && kind == SRC_HIDDEN && minutes != nullptr && (rebuild || !st.HiddenReady))
		{
			const int64_t latest = Micros(sc.LatestDateTimeForLastBar);
			if (!MinutesCover(minutes->At(minutes->Count() - 1).M, NewestTrade(st.Bars, latest), sc.IsReplayRunning() != 0))
				waiting = true;
		}
		if (waiting)
		{
			if (rebuild)
			{
				core.Reset();
				st.Built = false;
			}
			st.Waiting		= true;
			st.HiddenReady	= false;
			return;
		}
		// The levels file's write time in CT (NinjaTrader's TimeZoneInfo conversion): UTC -> the chart's time
		// zone -> CT.
		st.Levels.ToCt = [&sc, &st](int64_t utcSeconds)
		{
			const SCDateTime utc = SCDateTime::MICROSECONDS(utcSeconds * US_PER_SECOND);
			const SCDateTime chart = sc.ConvertDateTimeUTCToChartTimeZone != nullptr ? sc.ConvertDateTimeUTCToChartTimeZone(utc) : utc;
			return st.Clock.Of(Micros(chart));
		};
		if (rebuild)
		{
			core.Reset();
			st.Built		= true;
			st.EngineKey	= key;
			st.HashedCount	= 0;
			st.MinuteHash	= FNV64_BASIS;
			st.Rebuilds++;
			// NinjaTrader's load (NT:1710-1713): a new levels source from the paste box and the file, checked
			// against this chart's root and last price; the engine is built from what it accepted.
			double reference = NaN;
			for (size_t i = st.Bars.size(); i-- > 0 && !Valid(reference);)
				if (!st.Bars[i].Empty)
					reference = st.Bars[i].Close;
			const SCString dataFolder = sc.DataFilesFolder != nullptr ? sc.DataFilesFolder() : SCString();
			std::string cacheDirectory = dataFolder.GetChars();
			if (!cacheDirectory.empty())
				cacheDirectory += std::string(cacheDirectory.back() == '\\' || cacheDirectory.back() == '/' ? "" : "\\") + "Tatanka\\LevelsCache";
			const std::function<CtTime(int64_t)> toCt = st.Levels.ToCt;
			st.Levels = LevelFileSource();
			st.Levels.ToCt = toCt;
			st.Levels.ReferencePrice = reference;
			st.Levels.Initialize(core.Cfg.levels_file, MathEx::LevelsRoot(RootOf(symbol)), core.Cfg.lvl_paste, cacheDirectory);
			st.LevelsRead = false;
		}
		core.Cfg.lvl_text = st.Levels.Current.Serialize();
		st.HiddenReady	= kind == SRC_HIDDEN && minutes != nullptr;
		st.Kind			= kind;

		core.Root		= RootOf(symbol);
		core.Tick		= tick;
		core.Minutes	= sc.SecondsPerBar / 60;
		core.PriceText	= [&sc, tick](double v) { return Valid(v) ? std::string(sc.FormatGraphValue(std::floor(v / tick + 0.5) * tick, sc.BaseGraphValueFormat).GetChars())
			: std::string("---"); };
		if (core.Committed)
			core.Committed->PriceText = core.PriceText;

		BarMinutes chartBars;
		chartBars.Bars = &st.Bars;
		CallInput in;
		in.Bars			= &st.Bars;
		in.Minutes		= minutes;
		in.MacroMinutes	= minutes != nullptr ? minutes : &chartBars;
		in.Gate			= kind == SRC_HIDDEN && minutes != nullptr;
		in.ClipUs		= st.Bars.empty() ? INT64_MIN : FloorDiv(st.Bars[0].Su, US_PER_MINUTE) * US_PER_MINUTE;
		// The commit gate still reads the whole hidden chart: a replay's completed bars are complete there.
		in.ReadLimitUs	= kind == SRC_HIDDEN ? ReplayReadLimit(st.Bars, Micros(sc.LatestDateTimeForLastBar), sc.IsReplayRunning() != 0) : INT64_MAX;
		in.Clock		= &st.Clock;
		// Live (spec C.6): not a full recalculation, nothing downloading, and not a call that rebuilt
		// the engine (its notices are remembered, not delivered: FIX G7).
		in.Live			= !rebuild && !sc.IsFullRecalculation && sc.ChartIsDownloadingHistoricalData(sc.ChartNumber) == 0 && !minuteDownloading
			&& !dailyDownloading;
		const unsigned sound = sc.Input[IN_ALERT_SOUND].GetAlertSoundNumber();
		const bool replay = sc.IsReplayRunning() != 0;
		in.Send = [&sc, &st, &symbol, sound, replay](const std::string&, const std::string& text)
		{
			// No Alert = nothing; No Sound = the Alerts Log only; else that sound (spec C.6).
			if (sound > 0)
				sc.AlertWithMessage((int)sound - 1, ("[" + symbol + "] " + text).c_str(), 0);
			// Discord (spec D): this is only called for live alerts; never in a replay (NinjaTrader skips
			// Playback, NT:1897). Stamped with the latest trade's CT time (FIX G3: NinjaTrader stamps the
			// forming bar's end).
			if (st.Discord && !replay)
				st.Discord->Enqueue("[" + symbol + "] " + text + " | " + CtStamp(st.Clock.Of(Micros(sc.LatestDateTimeForLastBar))) + " CT");
		};
		// The levels file while live, at most every 5 s, after this call's commits and before the preview
		// (NinjaTrader's ReadLevelsFile, NT:1900-1912): a new revision replaces the engine's levels.
		const bool live = in.Live;
		in.BeforePreview = [&st, &core, live]()
		{
			if (!live || TrimNet(Utf16Of(core.Cfg.levels_file)).empty())
				return;
			const uint64_t now = st.NowMs();
			if (st.LevelsRead && now - st.LevelsReadMs < 5000)
				return;
			st.LevelsRead	= true;
			st.LevelsReadMs	= now;
			st.Levels.ReferencePrice = st.Bars.empty() ? NaN : st.Bars.back().Close;
			if (st.Levels.Refresh())
				core.ReplaceLevels(st.Levels.Current);
		};
		core.Run(in);

		// Remember what was read from the minute source.
		if (minutes != nullptr)
		{
			const int64_t used = (std::min)(core.MinutesUsed, minutes->Count());
			if (st.HashedCount == 0 && used > 0)
				st.FirstMinute = minutes->At(0).M;
			for (int64_t k = st.HashedCount; k < used; k++)
				st.MinuteHash = MinuteRecHash(st.MinuteHash, minutes->At(k));
			st.HashedCount = (std::max)(st.HashedCount, used);
		}
		// The formatter and the time conversion hold this call's sc: they are set again on the next call.
		core.PriceText = nullptr;
		if (core.Committed)
			core.Committed->PriceText = nullptr;
		st.Levels.ToCt = nullptr;
	}

	// ---- Drawing helpers (If/Then's, Level Lines', Periodic VP's) ----

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

	// The drawing callback has no transparency: a translucent color is blended over what is under it.
	uint32_t Blend(uint32_t color, double opacity, uint32_t background)
	{
		opacity = (std::max)(0.0, (std::min)(1.0, opacity));
		auto mix = [opacity](int c, int b) { return (int)(c * opacity + b * (1.0 - opacity) + 0.5); };
		return RGB(mix(GetRValue(color), GetRValue(background)), mix(GetGValue(color), GetGValue(background)), mix(GetBValue(color), GetBValue(background)));
	}

	// An ARGB color drawn over the background.
	uint32_t Drawn(uint32_t argb, uint32_t background)
	{
		const uint32_t alpha = argb >> 24;
		return alpha >= 255 ? ColorRefOf(argb) : Blend(ColorRefOf(argb), alpha / 255.0, background);
	}

	// On/off run lengths in multiples of the line width, NinjaTrader's Direct2D styles (Level Lines').
	const std::vector<int>& DashPattern(int style)
	{
		static const std::vector<int> solid;
		static const std::vector<int> dash			= {2, 2};
		static const std::vector<int> dot			= {1, 1};
		static const std::vector<int> dashDot		= {2, 2, 1, 2};
		static const std::vector<int> dashDotDot	= {2, 2, 1, 2, 1, 2};
		switch (style)
		{
			case LINESTYLE_DASH:		return dash;
			case LINESTYLE_DOT:			return dot;
			case LINESTYLE_DASHDOT:		return dashDot;
			case LINESTYLE_DASHDOTDOT:	return dashDotDot;
			default:					return solid;
		}
	}

	// A horizontal line as filled rectangles (GDI pens draw wide dashes solid), rows [y - w/2, y - w/2 + w).
	void DrawHorizontalLine(SCStudyInterfaceRef sc, int x0, int x1, int y, int width, int style, uint32_t color)
	{
		width = (std::max)(1, width);
		const int top = y - width / 2;
		const std::vector<int>& pattern = DashPattern(style);
		if (pattern.empty())
		{
			FillRect(sc, x0, top, x1, top + width, color);
			return;
		}
		size_t run = 0;
		for (int x = x0; x < x1; run = (run + 1) % pattern.size())
		{
			const int length = pattern[run] * width;
			if (run % 2 == 0)
				FillRect(sc, x, top, (std::min)(x + length, x1), top + width, color);
			x += length;
		}
	}

	// A vertical line as filled rectangles, columns [x - w/2, x - w/2 + w), dashed downwards.
	void DrawVerticalLine(SCStudyInterfaceRef sc, int x, int y0, int y1, int width, int style, uint32_t color)
	{
		width = (std::max)(1, width);
		const int left = x - width / 2;
		const std::vector<int>& pattern = DashPattern(style);
		if (pattern.empty())
		{
			FillRect(sc, left, y0, left + width, y1, color);
			return;
		}
		size_t run = 0;
		for (int y = y0; y < y1; run = (run + 1) % pattern.size())
		{
			const int length = pattern[run] * width;
			if (run % 2 == 0)
				FillRect(sc, left, y, left + width, (std::min)(y + length, y1), color);
			y += length;
		}
	}

	// NinjaTrader's DrawRectangle outline (Direct2D): a stroke `width` wide centered on each edge, in
	// the dash style. Each edge starts its own dash pattern (Direct2D runs one pattern around the
	// rectangle: a dash may fall a little differently at the corners).
	void DrawRectBorder(SCStudyInterfaceRef sc, int left, int top, int right, int bottom, int width, int style, uint32_t color)
	{
		width = (std::max)(1, width);
		const int half = width / 2;
		DrawHorizontalLine(sc, left - half, right - half + width, top, width, style, color);
		DrawHorizontalLine(sc, left - half, right - half + width, bottom, width, style, color);
		DrawVerticalLine(sc, left, top, bottom, width, style, color);
		DrawVerticalLine(sc, right, top, bottom, width, style, color);
	}

	// A sloped segment with a pen; styled ones as their dash pattern, which restarts at each segment
	// (NinjaTrader draws each VWAP segment with its own DrawLine).
	void DrawSegment(SCStudyInterfaceRef sc, int x0, int y0, int x1, int y1, int width, int style, uint32_t color)
	{
		n_ACSIL::s_GraphicsPen pen;
		pen.m_PenColor	= GraphicsColor(color);
		pen.m_Width		= (std::max)(1, width);
		pen.m_PenStyle	= n_ACSIL::s_GraphicsPen::e_PenStyle::PEN_STYLE_SOLID;
		sc.Graphics.SetPen(pen);
		const std::vector<int>& pattern = DashPattern(style);
		if (pattern.empty())
		{
			sc.Graphics.MoveTo(x0, y0);
			sc.Graphics.LineTo(x1, y1);
			return;
		}
		const double dx = x1 - x0, dy = y1 - y0, length = std::sqrt(dx * dx + dy * dy);
		if (!(length > 0))
			return;
		double at = 0;
		for (size_t run = 0; at < length; run = (run + 1) % pattern.size())
		{
			const double piece = (double)pattern[run] * (std::max)(1, width);
			if (run % 2 == 0)
			{
				const double end = (std::min)(length, at + piece);
				sc.Graphics.MoveTo((int)RoundHalfUp(x0 + dx * at / length), (int)RoundHalfUp(y0 + dy * at / length));
				sc.Graphics.LineTo((int)RoundHalfUp(x0 + dx * end / length), (int)RoundHalfUp(y0 + dy * end / length));
			}
			at += piece;
		}
	}

	// Direct2D's aliased fill covers the pixels whose centers lie inside: the edge of a span at v.
	int PixEdge(double v)
	{
		return (int)std::ceil(v - 0.5);
	}

	// NinjaTrader lays out in DIPs (1/96 inch). This is that scale: the window's DPI, or, when the
	// window reports 96 on a scaled display, how much larger the selected font drew than
	// GetTextSizeWithFont measured it. Call after SetTextFont(font). (If/Then's.)
	double DipScale(SCStudyInterfaceRef sc, const n_ACSIL::s_GraphicsFont& font)
	{
		const int dpi = sc.Graphics.GetDeviceCaps(LOGPIXELSY);
		const double fromDpi = dpi > 0 ? dpi / 96.0 : 1.0;
		n_ACSIL::s_GraphicsSize selected, withFont;
		sc.Graphics.GetTextSize(SCString("Ag"), selected);
		sc.Graphics.GetTextSizeWithFont(SCString("Ag"), font, withFont);
		const double fromText = withFont.Height > 0 ? std::floor(4.0 * selected.Height / withFont.Height + 0.5) / 4.0 : 1.0;
		return (std::max)(1.0, (std::min)(4.0, (std::max)(fromDpi, fromText)));
	}

	// Text size in the drawing font: the larger of GetTextSize (the selected font) and
	// GetTextSizeWithFont (which can measure several times too small on a scaled display).
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

	using TextMeasure = std::function<int(const std::string&)>;

	// Greedy word wrap at spaces (NinjaTrader's DirectWrite layout box; Periodic VP's).
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
						cut = space;
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

	// NinjaTrader's FontSize (NT:1984), DIPs.
	double FontSizeDips(const std::string& name)
	{
		const std::string lower = [&name]()
		{
			std::string l = name;
			for (char& c : l)
				if (c >= 'A' && c <= 'Z')
					c = (char)(c - 'A' + 'a');
			return l;
		}();
		return lower == "tiny" ? 10 : lower == "small" ? 12 : lower == "large" ? 18 : lower == "huge" ? 24 : 14;
	}

	// Font points from NinjaTrader's DIPs: x 0.75, half up (10 -> 8, 12 -> 9, 14 -> 11, 18 -> 14, 24 -> 18).
	int PointsOf(double dips)
	{
		return (std::max)(1, (int)RoundHalfUp(dips * 0.75));
	}

	n_ACSIL::s_GraphicsFont SegoeFont(int points)
	{
		n_ACSIL::s_GraphicsFont font;
		font.m_FaceName	= "Segoe UI";
		font.m_Height	= points;
		font.m_Weight	= FW_NORMAL;
		return font;
	}

	// The chart region in pixels (NinjaTrader's ChartPanel), the DIP scale and the chart background.
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

	// The text font (set only when its size changes) and color.
	struct Painter
	{
		s_sc*						Sc			= nullptr;
		n_ACSIL::s_GraphicsFont		Font;
		int							Points		= -1;
		uint32_t					Color		= 0;
		bool						HasColor	= false;

		void Use(int points)
		{
			if (points == Points)
				return;
			Font	= SegoeFont(points);
			Points	= points;
			Sc->Graphics.SetTextFont(Font);
		}

		int Width(const std::string& text) const { return MeasureLine(*Sc, Font, text).Width; }
		int Height() const { return (std::max)(1, (std::max)(MeasureLine(*Sc, Font, "Ag").Height, (int)Sc->Graphics.GetTextHeight())); }

		void Text(const std::string& text, int x, int y, uint32_t color)
		{
			if (!HasColor || Color != color)
			{
				Sc->Graphics.SetTextColor(GraphicsColor(color));
				Color		= color;
				HasColor	= true;
			}
			Sc->Graphics.DrawTextAt(SCString(text.c_str()), x, y);
		}

		// NinjaTrader's DrawText in a layout box maxWidth wide: word-wrapped, top-left aligned.
		void Wrapped(const std::string& text, int x, int y, int maxWidth, uint32_t color)
		{
			const TextMeasure measure = [this](const std::string& t) { return Width(t); };
			const std::vector<std::string> lines = WrapWords(text, (std::max)(1, maxWidth), measure);
			const int lineHeight = Height();
			for (size_t i = 0; i < lines.size(); i++)
				if (!lines[i].empty())
					Text(lines[i], x, y + (int)i * lineHeight, color);
		}
	};

	// A price as the chart shows it, snapped to the tick first (spec Notation "Price"; NinjaTrader's
	// MathEx.Price with Sierra Chart's own format, the bond 32nds included).
	std::string PriceText(SCStudyInterfaceRef sc, double v)
	{
		if (!Valid(v))
			return "---";
		const double tick = DecimalTickSize(sc.TickSize);
		const double snapped = tick > 0 ? std::floor(v / tick + 0.5) * tick : v;
		const SCString text = sc.FormatGraphValue(snapped, sc.BaseGraphValueFormat);
		return text.GetChars();
	}

	int PriceY(SCStudyInterfaceRef sc, double price)
	{
		return sc.RegionValueToYPixelCoordinate((float)price, sc.GraphRegion);
	}

	// A bar's center; past the last loaded bar (the fill space) and before bar 0, one bar spacing per bar.
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

	// How a line kind is drawn now (spec A.3, C.5.3): its subgraph's visibility, color, width, style,
	// label color and name. The alpha is NinjaTrader's where its color carries one.
	struct LineLook
	{
		bool		Known		= false;
		bool		Visible		= true;
		uint32_t	Argb		= 0;
		int			Width		= 1;
		int			Style		= LINESTYLE_SOLID;
		bool		UseLabel	= false;
		uint32_t	LabelColor	= 0;
		std::string	Name;
	};

	// A daily level's kind from its line id ("PIVOT", "RES3", "FLIPPED SUPP1"): SG_PIVOT, SG_RES or SG_SUPP
	// (its own kind's, whatever the flip), -1 for another name. `number`: the level's number ("3").
	int LevelSubgraphOf(const std::string& id, std::string& number, bool& flipped)
	{
		flipped = StartsWith(id, "FLIPPED ");
		const std::string name = flipped ? id.substr(8) : id;
		number.clear();
		if (name == "PIVOT")
			return SG_PIVOT;
		const int kind = StartsWith(name, "RES") ? SG_RES : StartsWith(name, "SUPP") ? SG_SUPP : -1;
		if (kind < 0)
			return -1;
		number = name.substr(kind == SG_RES ? 3 : 4);
		if (number.empty() || number.find_first_not_of("0123456789") != std::string::npos)
			return -1;
		return kind;
	}

	// The subgraph of a line id (NinjaTrader's line name), -1 for none. The daily levels and their zone
	// borders (group "Levels") are resolved first (spec G14: a TRAP ACTIVE subgraph renamed to "" or to a
	// level's name never claims them).
	int SubgraphOfLine(const std::string& id, const std::string& group, const Settings& cfg)
	{
		if (group == "Levels")
		{
			if (id.empty())
				return SG_LEVEL_ZONE_BORDER;
			std::string number;
			bool flipped = false;
			const int kind = LevelSubgraphOf(id, number, flipped);
			if (kind >= 0)
				return kind;
		}
		static const std::pair<const char*, int> table[] = {
			{"Developing POC", SG_DEV_POC}, {"Developing VAH", SG_DEV_VAH}, {"Developing VAL", SG_DEV_VAL}, {"HVN", SG_WALL},
			{"pdPOC", SG_PD_POC}, {"pdVAH", SG_PD_VAH}, {"pdVAL", SG_PD_VAL}, {"pmVAH", SG_PM_VAH}, {"pmVAL", SG_PM_VAL}, {"pmPOC", SG_PM_POC},
			{"pdHigh", SG_PD_HIGH}, {"pdLow", SG_PD_LOW}, {"pdOpen", SG_PD_OPEN}, {"IB High", SG_IB_HIGH}, {"IB Low", SG_IB_LOW},
			{"IB Midpoint", SG_IB_MID}, {"OVN High", SG_OVN_HIGH}, {"OVN Low", SG_OVN_LOW}, {"SETTLE", SG_SETTLE},
			{"Spike Base (Supp)", SG_SPIKE_SUP}, {"Spike Base (Res)", SG_SPIKE_RES}, {"dOpen", SG_DOPEN}, {"wkOpen", SG_WK_OPEN},
			{"pwHigh", SG_PW_HIGH}, {"pwLow", SG_PW_LOW}, {"pmHigh", SG_PM_HIGH}, {"pmLow", SG_PM_LOW}, {"Daily nPOC", SG_NPOC_DAILY},
			{"Weekly nPOC", SG_NPOC_WEEKLY}, {"Monthly nPOC", SG_NPOC_MONTHLY}, {"Poor High", SG_POOR_HIGH}, {"Poor Low", SG_POOR_LOW}};
		for (const auto& entry : table)
			if (id == entry.first)
				return entry.second;
		if (id == cfg.inv_txt_trap)
			return SG_TRAP;		// NinjaTrader names the trapped settlement line with its Trap Text
		return -1;
	}

	// NinjaTrader's alpha of a line kind from the current settings (pdVAH/pdVAL 50 %, walls).
	uint32_t AlphaOfLine(const std::string& id, const Settings& cfg)
	{
		if (id == "pdVAH")
			return cfg.pd_vah_c >> 24;
		if (id == "pdVAL")
			return cfg.pd_val_c >> 24;
		if (id == "HVN")
			return AlphaOfTransparency(cfg.mvp_wall_transp);
		return 255;
	}

	LineLook LookOf(SCStudyInterfaceRef sc, const Settings& cfg, const LineItem& line)
	{
		LineLook look;
		const int k = SubgraphOfLine(line.Name, line.Group, cfg);
		if (k == SG_PIVOT || k == SG_RES || k == SG_SUPP || k == SG_LEVEL_ZONE_BORDER)
		{
			// A daily level (spec B.4.4): the frame's color (a flipped level takes the other side's), its own
			// kind's subgraph for the width, style and label color (Hidden: no line, the label and zone stay),
			// its label "FLIPPED " + that subgraph's Name + the number. A zone border: the Level Zone Border
			// subgraph's visibility, width and style, the level's color.
			const s_SCSubgraph_260& g = sc.Subgraph[k];
			look.Known		= true;
			look.Argb		= line.Color;
			look.Style		= g.LineStyle;
			look.UseLabel	= g.UseLabelsColor != 0;
			look.LabelColor	= g.LabelsColor;
			if (k == SG_LEVEL_ZONE_BORDER)
			{
				look.Visible	= Visible(g);
				look.Width		= (int)g.LineWidth;
				return look;
			}
			std::string number;
			bool flipped = false;
			LevelSubgraphOf(line.Name, number, flipped);
			look.Width	= line.Width > 0 && Visible(g) ? (int)g.LineWidth : 0;
			look.Name	= (flipped ? "FLIPPED " : "") + std::string(g.Name.GetChars()) + number;
			return look;
		}
		if (k < 0)
		{
			look.Argb	= line.Color;
			look.Width	= line.Width;
			look.Style	= StyleOf(line.Style);
			look.Name	= line.Name;
			return look;
		}
		const s_SCSubgraph_260& g = sc.Subgraph[k];
		look.Known		= true;
		look.Visible	= Visible(g);
		look.Argb		= ArgbOf(g.PrimaryColor, AlphaOfLine(line.Name, cfg));
		look.Width		= line.Width <= 0 ? 0 : (int)g.LineWidth;
		look.Style		= g.LineStyle;
		look.UseLabel	= g.UseLabelsColor != 0;
		look.LabelColor	= g.LabelsColor;
		look.Name		= g.Name.GetChars();
		return look;
	}

	// NinjaTrader's IsTopLayer (NT:2070-2085), by the line's id. FIX G13: Daily Levels (All) lifts the
	// daily levels' label group (the levels and their zone borders); NinjaTrader lifts every line
	// extended both ways, IB lines with Extend IB Levels = Both too.
	bool IsTopLayer(const Settings& cfg, const LineItem& l)
	{
		const std::string& pick = cfg.layer_top_pick;
		if (pick == "Daily Levels (All)")	return l.Group == "Levels";
		if (pick == "Profile POC")			return l.Name == "Developing POC";
		if (pick == "Profile VAH")			return l.Name == "Developing VAH";
		if (pick == "Profile VAL")			return l.Name == "Developing VAL";
		if (pick == "Prev Day High")		return l.Name == "pdHigh";
		if (pick == "Prev Day Low")			return l.Name == "pdLow";
		if (pick == "Prev Month VAH")		return l.Name == "pmVAH";
		if (pick == "Prev Month VAL")		return l.Name == "pmVAL";
		if (pick == "Spike Base")			return StartsWith(l.Name, "Spike Base");
		return l.Name == pick;
	}

	// Per-line label switches Sierra Chart splits from NinjaTrader's shared ones (spec A.2 #55/#57).
	bool LabelAllowed(const Settings& cfg, const LineItem& l)
	{
		if (l.Name == "dOpen")
			return cfg.LabelsDOpen;
		if (l.Name == "wkOpen")
			return cfg.LabelsWkOpen;
		return true;
	}

	// What one frame draw needs.
	struct View
	{
		const StudyState*	St			= nullptr;
		Canvas				C;
		Painter				P;
		double				Spacing		= 8;

		int X(SCStudyInterfaceRef sc, CtTime t) const
		{
			return PositionX(BarPosition(St->Bars, t), [&sc](int i) { return BarX(sc, i); });
		}
	};

	// NinjaTrader's RenderLine (NT:2086-2107): the segment, then the label at the current bar's end
	// (at the line's own end when it stopped earlier: FIX G2) plus the offset, clamped inside the
	// panel, in the label color. A line extended to the panel's right edge has not stopped: its
	// label stays at the current bar, as NinjaTrader's (the IB with Extend Right or Both).
	void RenderLine(SCStudyInterfaceRef sc, View& v, const LineItem& line, bool history)
	{
		if (!Valid(line.Price))
			return;
		const Settings& cfg = v.St->Core.Cfg;
		const LineLook look = LookOf(sc, cfg, line);
		if (!look.Visible)
			return;
		const Canvas& c = v.C;
		int y = PriceY(sc, line.Price);
		if (y < c.Top - c.Dip(25) || y > c.Bottom + c.Dip(25))
			return;
		const bool leftEdge = line.Start == CT_MIN || line.Extend == "Left" || line.Extend == "Both";
		const bool rightEdge = line.Extend == "Right" || line.Extend == "Both";
		const double x1 = leftEdge ? c.Left : v.X(sc, line.Start);
		const double x2 = rightEdge ? c.Right : v.X(sc, line.End) + line.Offset * v.Spacing;
		const uint32_t color = Drawn(look.Argb, c.Background);
		if (look.Width > 0)
			DrawHorizontalLine(sc, PixEdge((std::max)((double)c.Left, x1)), PixEdge((std::min)((double)c.Right, x2)), y, c.Stroke(look.Width), look.Style, color);
		if (history || !line.Label || !LabelAllowed(cfg, line))
			return;
		double labelX = v.X(sc, rightEdge ? v.St->Core.View.Bar.End : line.End) + line.Offset * v.Spacing + c.Dip(4);
		if (StartsWith(line.Name, "IB ") && cfg.ib_label_loc == "Left")
			labelX = x1;
		const double size = FontSizeDips(line.Size);
		const std::string name = look.Known ? look.Name : line.Name;
		const std::string label = name + ": " + PriceText(sc, line.Price);
		const double estimated = (std::max)(80.0, Utf16Length(label) * size * .56) * c.Scale;
		labelX = (std::max)((double)c.Left + c.Dip(2), (std::min)(labelX, c.Right - estimated - c.Dip(4)));
		// A daily level with a zone: the label sits in the middle of the zone's lower half (NT:2102-2106). A
		// daily level is a named line of the "Levels" group (FIX G13; NinjaTrader tests Extend == "Both").
		if (line.Group == "Levels" && !line.Name.empty() && cfg.lvl_showZones)
		{
			const double tick = DecimalTickSize(sc.TickSize);
			for (const ZoneItem& z : v.St->Core.View.Zones)
				if (z.Start == CT_MIN && std::fabs((z.Top + z.Bottom) / 2 - line.Price) < tick * .01)
				{
					y = PriceY(sc, line.Price - (z.Top - z.Bottom) / 4);
					break;
				}
		}
		v.P.Use(PointsOf(size));
		const uint32_t text = look.UseLabel ? look.LabelColor : color;
		v.P.Text(label, (int)RoundHalfUp(labelX), y - c.Dip(size / 2 + 2), text);
	}

	// The single prints' parts that are not ranges (SplitSpan's callback parts: before bar 0, past the
	// last bar when RANGES_IN_FILL_SPACE is off), blended in the ranges' color and opacity; then each
	// block's border when the Single Print Border subgraph is shown (NinjaTrader's BorderWidth > 0,
	// NT:2020-2028) and the Single Print subgraph too: X(Start) to the fills' end (X(the current bar's end
	// + 30 minutes), cut at the session's end: SinglePrintEndNow), clipped to the panel.
	void DrawSinglePrints(SCStudyInterfaceRef sc, View& v)
	{
		const StudyState& st = *v.St;
		const Frame& f = st.Core.View;
		const Canvas& c = v.C;
		const int endBar = SinglePrintEndNow(sc, st);
		const s_SCSubgraph_260& fill = sc.Subgraph[SG_SP];
		if (Visible(fill))
		{
			const int transparency = (std::max)(0, (std::min)(100, sc.Input[IN_SP_TRANSP].GetInt()));
			const uint32_t color = Blend(fill.PrimaryColor, (100 - transparency) / 100.0, c.Background);
			for (const RangePiece& r : SinglePrintPieces(f.Zones, st.Bars, endBar, fill.PrimaryColor, transparency))
			{
				const SpanSplit split = SplitSpan(r.StartBar, r.EndBar, (int)st.Bars.size());
				const int top = PriceY(sc, r.Top), bottom = PriceY(sc, r.Bottom);
				for (int k = 0; k < split.Parts; k++)
					FillRect(sc, BarX(sc, split.Start[k]), top, BarX(sc, split.End[k]), bottom, color);
			}
		}
		// The outlines belong to the single prints: hiding the Single Print subgraph hides them too (the
		// user's decision, Stage 3 review), whatever the Single Print Border subgraph says.
		const s_SCSubgraph_260& border = sc.Subgraph[SG_SP_BORDER];
		if (!Visible(border) || !Visible(fill))
			return;
		const int width = c.Stroke((std::max)(1, (std::min)(4, (int)border.LineWidth)));
		const double xEnd = BarX(sc, endBar);
		for (const ZoneItem& z : f.Zones)
		{
			if (z.Start == CT_MIN)
				continue;
			const int ya = PriceY(sc, z.Top), yb = PriceY(sc, z.Bottom);
			if (yb < c.Top || ya > c.Bottom)
				continue;
			const double xa = v.X(sc, z.Start);
			const int x0 = PixEdge((std::max)((double)c.Left, xa));
			const int x1 = x0 + (std::max)(1, PixEdge((std::min)((double)c.Right, xEnd)) - x0);
			DrawRectBorder(sc, x0, ya, x1, ya + (std::max)(1, yb - ya), width, border.LineStyle, border.PrimaryColor);
		}
	}

	// The developing profile in the right fill space with NinjaTrader's exact geometry (NT:2029-2045).
	// The completed profiles are translucent ranges (UpdateRanges).
	void DrawCurrentProfile(SCStudyInterfaceRef sc, View& v, const FrameProfile& h)
	{
		const Settings& cfg = v.St->Core.Cfg;
		const Canvas& c = v.C;
		if (!h.Data || h.Data->Rows.empty())
			return;
		double max = 0;
		for (const auto& row : h.Data->Rows)
			max = (std::max)(max, row.second);
		if (!(max > 0))
			return;
		double anchor = v.X(sc, h.End);
		const double width = cfg.mvp_profile_width * v.Spacing;
		anchor += (cfg.mvp_offset - (cfg.mvp_align_right ? 0 : cfg.mvp_profile_width)) * v.Spacing;
		if (anchor + width < c.Left || anchor - width > c.Right)
			return;
		const bool showVa = Visible(sc.Subgraph[SG_VA_HIST]), showOut = Visible(sc.Subgraph[SG_OUT_HIST]);
		const uint32_t va = Blend(sc.Subgraph[SG_VA_HIST].PrimaryColor, AlphaOfTransparency(cfg.mvp_hist_va_transp) / 255.0, c.Background);
		const uint32_t out = Blend(sc.Subgraph[SG_OUT_HIST].PrimaryColor, AlphaOfTransparency(cfg.mvp_hist_out_transp) / 255.0, c.Background);
		const double step = h.Data->Step;
		for (const auto& row : h.Data->Rows)
		{
			const double price = (double)row.first * step;
			const int ya = PriceY(sc, price + step / 2), yb = PriceY(sc, price - step / 2);
			if (yb < c.Top || ya > c.Bottom)
				continue;
			const double w = row.second / max * width;
			const bool inVa = price >= h.Stats.Val && price <= h.Stats.Vah;
			if (inVa ? !showVa : !showOut)
				continue;
			const double x = cfg.mvp_align_right ? anchor - w : anchor;
			FillRect(sc, PixEdge(x), ya, PixEdge(x + (std::max)(1.0, w)), ya + (std::max)(1, yb - ya), inVa ? va : out);
		}
	}

	// NinjaTrader's VWAP (NT:2049-2062): a segment between the centers of adjacent bars of one trading
	// date where both values exist, in the VWAP color, width and style, opaque.
	void DrawVwap(SCStudyInterfaceRef sc, View& v)
	{
		const s_SCSubgraph_260& g = sc.Subgraph[SG_VWAP];
		if (!Visible(g))
			return;
		const AmtCore& core = v.St->Core;
		const int first = sc.IndexOfFirstVisibleBar, last = sc.IndexOfLastVisibleBar;
		const uint32_t color = g.PrimaryColor;
		const int width = v.C.Stroke(g.LineWidth);
		bool hasPrev = false;
		Sample prev;
		auto visit = [&](const Sample& s)
		{
			if (s.Index < first - 1 || s.Index > last)
			{
				prev	= s;
				hasPrev	= true;
				return;
			}
			if (hasPrev && SamplesJoin(v.St->Bars, prev.Index, s.Index) && Valid(s.Vwap) && Valid(prev.Vwap) && TradingDate(prev.Start) == TradingDate(s.Start))
				DrawSegment(sc, BarX(sc, prev.Index), PriceY(sc, prev.Vwap), BarX(sc, s.Index), PriceY(sc, s.Vwap), width, g.LineStyle, color);
			prev	= s;
			hasPrev	= true;
		};
		// The committed samples from the bar before the first visible one, then the previewed bars.
		auto it = std::lower_bound(core.Samples.begin(), core.Samples.end(), first - 1, [](const Sample& s, int i) { return s.Index < i; });
		if (it != core.Samples.begin())
			--it;
		for (; it != core.Samples.end() && it->Index <= last; ++it)
			visit(*it);
		for (const Sample& s : core.ViewSamples)
			visit(s);
		sc.Graphics.ResetPen();
	}

	// NinjaTrader's dashboard (NT:2114-2134, spec B.1.6): DIP layout, blended colors.
	void DrawDashboard(SCStudyInterfaceRef sc, View& v, const Frame& f)
	{
		const Settings& cfg = v.St->Core.Cfg;
		const Canvas& c = v.C;
		const int rows = (int)f.Labels.size();
		if (rows == 0 || f.Values.size() != f.Labels.size() || f.Colors.size() != f.Labels.size())
			return;
		const double fs = FontSizeDips(cfg.tbl_size), rh = fs + 10, w = (std::max)(310.0, fs * 25), h = rh * (rows + 1);
		const int W = c.Dip(w), H = c.Dip(h), RH = c.Dip(rh);
		const int x = cfg.tbl_pos.find("Left") != std::string::npos ? c.Left + c.Dip(10) : c.Right - W - c.Dip(10);
		const int y = cfg.tbl_pos.find("Bottom") != std::string::npos ? c.Bottom - H - c.Dip(55)
			: cfg.tbl_pos.find("Middle") != std::string::npos ? c.Top + (c.Bottom - c.Top - H) / 2 : c.Top + c.Dip(10);
		const uint32_t background = Blend(RGB(0, 0, 0), 0xCC / 255.0, c.Background);
		FillRect(sc, x, y, x + W, y + H, background);
		const uint32_t header = Blend(RGB(0x1E, 0x22, 0x2D), 0xEE / 255.0, background);
		FillRect(sc, x, y, x + W, y + RH, header);
		// Header: product and version, the site right-aligned in a smaller font (NinjaTrader only).
		const double small = fs * .85;
		v.P.Use(PointsOf(small));
		const int siteWidth = v.P.Width(BRAND_SITE);
		v.P.Text(BRAND_SITE, x + W - c.Dip(8) - siteWidth, y + c.Dip(4 + (fs - small) * .6), RGB(0xB2, 0xB5, 0xBE));
		v.P.Use(PointsOf(fs));
		v.P.Text(std::string(BRAND_SHORT) + " v" + BRAND_VERSION, x + c.Dip(8), y + c.Dip(4), RGB(255, 255, 255));
		const uint32_t separator = Blend(RGB(0x66, 0x66, 0x66), 0x66 / 255.0, background);
		const int line = c.Stroke(1);
		FillRect(sc, x, y + RH, x + W, y + RH + line, separator);
		const int top = y + RH;
		for (int i = 0; i < rows; i++)
		{
			const int rowTop = top + c.Dip(i * rh);
			FillRect(sc, x, top + c.Dip((i + 1) * rh), x + W, top + c.Dip((i + 1) * rh) + line, separator);
			v.P.Text(f.Labels[(size_t)i], x + c.Dip(8), rowTop + c.Dip(4), RGB(255, 255, 255));
			v.P.Text(f.Values[(size_t)i], x + c.Dip(w * .44), rowTop + c.Dip(4), Drawn(f.Colors[(size_t)i], background));
		}
	}

	// The notice box's text (NT:1870, NT:2064): the session-time warning, the levels' (STALE, a rejected
	// paste or file, the cache), the frame's, the Discord setup and delivery warnings (never the URL).
	std::string Notices(const StudyState& st)
	{
		const Frame& f = st.Core.View;
		return NoticeText(st.SettingsWarning, st.Levels.Warning(TradingDate(f.Bar.Start)), f.Warning, st.DiscordSetupWarning,
			st.Discord ? st.Discord->Warning : std::string());
	}

	// The whole picture of the newest frame, in NinjaTrader's order (spec C.5.1): the 80% fill, the
	// single prints and the level zones are ranges (the single prints' borders and off-chart parts
	// come first here); the developing profile; history lines; frame lines (top layer last); the VWAP;
	// the dashboard; the notices.
	void DrawFrame(SCStudyInterfaceRef sc, View& v)
	{
		const AmtCore& core = v.St->Core;
		const Frame& f = core.View;
		const Settings& cfg = core.Cfg;
		const Canvas& c = v.C;
		DrawSinglePrints(sc, v);
		for (const FrameProfile& h : f.Profiles)
			if (h.Current)
				DrawCurrentProfile(sc, v, h);
		// The archive as NinjaTrader keeps it for the rolling pd lines shown now.
		const int shownPd = PdCombination(Visible(sc.Subgraph[SG_PD_HIGH]), Visible(sc.Subgraph[SG_PD_LOW]), Visible(sc.Subgraph[SG_PD_OPEN]));
		for (const ArchivedLine& a : core.History)
			if (a.In(shownPd))
				RenderLine(sc, v, a.Line, true);
		std::vector<const LineItem*> order;
		for (const LineItem& line : f.Lines)
			if (!IsTopLayer(cfg, line))
				order.push_back(&line);
		for (const LineItem& line : f.Lines)
			if (IsTopLayer(cfg, line))
				order.push_back(&line);
		for (const LineItem* line : order)
			RenderLine(sc, v, *line, false);
		DrawVwap(sc, v);
		if (cfg.tbl_show)
			DrawDashboard(sc, v, f);
		const std::string notices = Notices(*v.St);
		if (!notices.empty())
		{
			v.P.Use(PointsOf(12));
			v.P.Wrapped(notices, c.Left + c.Dip(10), c.Bottom - c.Dip(64), c.Right - c.Left - c.Dip(20), RGB(0xFF, 0xC6, 0x6B));
		}
	}

	void DrawAmtToolkit(HWND, HDC, SCStudyInterfaceRef sc)
	{
		const StudyState* state = PeekState(sc);
		if (sc.HideStudy || state == nullptr)
			return;
		View v;
		v.St		= state;
		v.P.Sc		= &sc;
		Canvas& c	= v.C;
		c.Left		= sc.StudyRegionLeftCoordinate;
		c.Top		= sc.StudyRegionTopCoordinate;
		c.Right		= sc.StudyRegionRightCoordinate;
		c.Bottom	= sc.StudyRegionBottomCoordinate;
		if (c.Right <= c.Left || c.Bottom <= c.Top)
			return;
		v.P.Use(PointsOf(14));		// before any measuring: see MeasureLine
		c.Scale = DipScale(sc, v.P.Font);
		uint32_t unusedWidth = 0;
		SubgraphLineStyles unusedStyle = LINESTYLE_SOLID;
		sc.GetGraphicsSetting(sc.ChartNumber, n_ACSIL::GRAPHICS_SETTING_CHART_BACKGROUND, c.Background, unusedWidth, unusedStyle);
		const int lastVisible = sc.IndexOfLastVisibleBar, firstVisible = sc.IndexOfFirstVisibleBar;
		v.Spacing = lastVisible > firstVisible ? std::abs(BarX(sc, lastVisible) - BarX(sc, lastVisible - 1)) : c.Dip(8);
		v.Spacing = (std::max)(1.0, v.Spacing);

		n_ACSIL::s_GraphicsRectangle clip;
		clip.Left	= c.Left;
		clip.Top	= c.Top;
		clip.Right	= c.Right;
		clip.Bottom	= c.Bottom;
		sc.Graphics.SetClippingRegionFromRectangle(clip);
		sc.Graphics.SetBackgroundMode(TRANSPARENT);
		sc.Graphics.SetTextAlign(TA_NOUPDATECP | TA_LEFT | TA_TOP);

		const std::string brand = std::string(BRAND_SHORT) + " v" + BRAND_VERSION;
		if (!state->Error.empty())
		{
			// NinjaTrader's fault text (NT:2001): nothing else.
			v.P.Use(PointsOf(16));
			v.P.Wrapped(brand + ": " + state->Error, c.Left + c.Dip(12), c.Top + c.Dip(12), c.Right - c.Left - c.Dip(24), RGB(0xFF, 0x50, 0x50));
		}
		else if (state->Waiting || !state->Core.HasView || state->Bars.empty())
		{
			// NinjaTrader's loading text (NT:2002).
			v.P.Use(PointsOf(14));
			v.P.Wrapped(brand + TEXT_LOADING_TAIL, c.Left + c.Dip(12), c.Top + c.Dip(12), c.Right - c.Left - c.Dip(24), RGB(0xC0, 0xC0, 0xC0));
		}
		else
			DrawFrame(sc, v);

		sc.Graphics.ResetTextAlign();
		sc.Graphics.ResetBackgroundMode();
		sc.Graphics.ResetTextColor();
		sc.Graphics.ResetClippingRegion();
		sc.Graphics.ResetTextFont();
	}

	// ==== Shared multi-line editor (the same code in every Tatanka study that has one) ====
	// Sierra Chart inputs are single-line, so a study's multi-line text (NinjaTrader's
	// large editor) is edited in this window, opened from the chart's right-click menu.
	// It runs on its own thread with its own message loop, so Sierra Chart's keyboard
	// shortcuts never see its keystrokes. The study function picks up the saved text on
	// its next call; sc.UpdateAlways is on while the editor is open, so that call comes
	// within a fraction of a second.
	//
	// Sierra Chart's Remote Build may not link user32.lib or gdi32.lib, so the Windows
	// functions are looked up at run time. Sierra Chart always has both DLLs loaded.

	struct Win32Api
	{
		decltype(&::OpenClipboard)			OpenClipboard			= nullptr;
		decltype(&::GetClipboardData)		GetClipboardData		= nullptr;
		decltype(&::CloseClipboard)			CloseClipboard			= nullptr;
		decltype(&::GetWindowLongPtrW)		GetWindowLongPtrW		= nullptr;
		decltype(&::SetWindowLongPtrW)		SetWindowLongPtrW		= nullptr;
		decltype(&::GetDC)					GetDC					= nullptr;
		decltype(&::ReleaseDC)				ReleaseDC				= nullptr;
		decltype(&::CreateWindowExW)		CreateWindowExW			= nullptr;
		decltype(&::SendMessageW)			SendMessageW			= nullptr;
		decltype(&::SetWindowTextW)			SetWindowTextW			= nullptr;
		decltype(&::SetFocus)				SetFocus				= nullptr;
		decltype(&::MoveWindow)				MoveWindow				= nullptr;
		decltype(&::GetClientRect)			GetClientRect			= nullptr;
		decltype(&::GetSysColorBrush)		GetSysColorBrush		= nullptr;
		decltype(&::GetWindowTextLengthW)	GetWindowTextLengthW	= nullptr;
		decltype(&::GetWindowTextW)			GetWindowTextW			= nullptr;
		decltype(&::DestroyWindow)			DestroyWindow			= nullptr;
		decltype(&::PostQuitMessage)		PostQuitMessage			= nullptr;
		decltype(&::DefWindowProcW)			DefWindowProcW			= nullptr;
		decltype(&::LoadCursorW)			LoadCursorW				= nullptr;
		decltype(&::RegisterClassExW)		RegisterClassExW		= nullptr;
		decltype(&::ShowWindow)				ShowWindow				= nullptr;
		decltype(&::SetForegroundWindow)	SetForegroundWindow		= nullptr;
		decltype(&::GetMessageW)			GetMessageW				= nullptr;
		decltype(&::GetKeyState)			GetKeyState				= nullptr;
		decltype(&::GetNextDlgTabItem)		GetNextDlgTabItem		= nullptr;
		decltype(&::PostMessageW)			PostMessageW			= nullptr;
		decltype(&::IsDialogMessageW)		IsDialogMessageW		= nullptr;
		decltype(&::TranslateMessage)		TranslateMessage		= nullptr;
		decltype(&::DispatchMessageW)		DispatchMessageW		= nullptr;
		decltype(&::IsWindow)				IsWindow				= nullptr;
		decltype(&::InvalidateRect)			InvalidateRect			= nullptr;
		decltype(&::GetWindowRect)			GetWindowRect			= nullptr;
		decltype(&::CreateFontW)			CreateFontW				= nullptr;
		decltype(&::DeleteObject)			DeleteObject			= nullptr;
		decltype(&::GetDeviceCaps)			GetDeviceCaps			= nullptr;
		decltype(&::SetBkMode)				SetBkMode				= nullptr;
		bool								Loaded					= false;
	};

	template <typename Function>
	bool LoadFunction(HMODULE module, const char* name, Function& function)
	{
		function = module != nullptr ? reinterpret_cast<Function>(reinterpret_cast<void*>(GetProcAddress(module, name))) : nullptr;
		return function != nullptr;
	}

	const Win32Api& Api()
	{
		static const Win32Api api = []
		{
			Win32Api a;
			HMODULE user32	= LoadLibraryW(L"user32.dll");
			HMODULE gdi32	= LoadLibraryW(L"gdi32.dll");
			bool ok = true;
			#define TATANKA_LOAD(module, name) ok &= LoadFunction(module, #name, a.name)
			TATANKA_LOAD(user32, OpenClipboard);		TATANKA_LOAD(user32, GetClipboardData);
			TATANKA_LOAD(user32, CloseClipboard);		TATANKA_LOAD(user32, GetWindowLongPtrW);
			TATANKA_LOAD(user32, SetWindowLongPtrW);	TATANKA_LOAD(user32, GetDC);
			TATANKA_LOAD(user32, ReleaseDC);			TATANKA_LOAD(user32, CreateWindowExW);
			TATANKA_LOAD(user32, SendMessageW);			TATANKA_LOAD(user32, SetWindowTextW);
			TATANKA_LOAD(user32, SetFocus);				TATANKA_LOAD(user32, MoveWindow);
			TATANKA_LOAD(user32, GetClientRect);		TATANKA_LOAD(user32, GetSysColorBrush);
			TATANKA_LOAD(user32, GetWindowTextLengthW);	TATANKA_LOAD(user32, GetWindowTextW);
			TATANKA_LOAD(user32, DestroyWindow);		TATANKA_LOAD(user32, PostQuitMessage);
			TATANKA_LOAD(user32, DefWindowProcW);		TATANKA_LOAD(user32, LoadCursorW);
			TATANKA_LOAD(user32, RegisterClassExW);		TATANKA_LOAD(user32, ShowWindow);
			TATANKA_LOAD(user32, SetForegroundWindow);	TATANKA_LOAD(user32, GetMessageW);
			TATANKA_LOAD(user32, GetKeyState);			TATANKA_LOAD(user32, GetNextDlgTabItem);
			TATANKA_LOAD(user32, PostMessageW);			TATANKA_LOAD(user32, IsDialogMessageW);
			TATANKA_LOAD(user32, TranslateMessage);		TATANKA_LOAD(user32, DispatchMessageW);
			TATANKA_LOAD(user32, IsWindow);				TATANKA_LOAD(user32, InvalidateRect);
			TATANKA_LOAD(user32, GetWindowRect);		TATANKA_LOAD(gdi32, CreateFontW);
			TATANKA_LOAD(gdi32, DeleteObject);			TATANKA_LOAD(gdi32, GetDeviceCaps);
			TATANKA_LOAD(gdi32, SetBkMode);
			#undef TATANKA_LOAD
			a.Loaded = ok;
			return a;
		}();
		return api;
	}

	std::wstring Widen(const std::string& utf8)
	{
		if (utf8.empty())
			return std::wstring();
		const int length = MultiByteToWideChar(CP_UTF8, 0, utf8.data(), (int)utf8.size(), nullptr, 0);
		std::wstring wide((size_t)length, L'\0');
		MultiByteToWideChar(CP_UTF8, 0, utf8.data(), (int)utf8.size(), &wide[0], length);
		return wide;
	}

	std::string Narrow(const std::wstring& wide)
	{
		if (wide.empty())
			return std::string();
		const int length = WideCharToMultiByte(CP_UTF8, 0, wide.data(), (int)wide.size(), nullptr, 0, nullptr, nullptr);
		std::string utf8((size_t)length, '\0');
		WideCharToMultiByte(CP_UTF8, 0, wide.data(), (int)wide.size(), &utf8[0], length, nullptr, nullptr);
		return utf8;
	}

	// \n line ends (how the study stores text) to and from \r\n (what an edit control wants).
	std::string EditorLineEnds(const std::string& text, bool toCrLf)
	{
		std::string result;
		for (size_t i = 0; i < text.size(); i++)
		{
			const char c = text[i];
			if (c == '\r')
			{
				if (i + 1 < text.size() && text[i + 1] == '\n')
					i++;
				result += toCrLf ? "\r\n" : "\n";
			}
			else if (c == '\n')
				result += toCrLf ? "\r\n" : "\n";
			else
				result += c;
		}
		return result;
	}

	// What the editor window says and how its text box behaves; each study passes its own.
	struct EditorTexts
	{
		const wchar_t*	ClassName		= L"TatankaTextEditor";
		const wchar_t*	Title			= L"";
		const wchar_t*	Intro			= L"";
		const wchar_t*	Help			= L"";
		const wchar_t*	OkButton		= L"OK";
		const char*		SavedMessage	= "";	// Message Log line once saved text is applied
		const char*		OpenFailed		= "";	// Message Log line if the window can't open
		int				IntroHeight		= 40;	// DIPs
		int				HelpHeight		= 112;	// DIPs
		bool			WordWrap		= false;
		bool			Monospace		= true;
	};

	struct EditorState
	{
		SRWLOCK		Lock	= SRWLOCK_INIT;
		HWND		Window	= nullptr;
		bool		Done	= false;
		bool		Saved	= false;
		std::string	Text;				// in: the current text; out: the saved text (UTF-8, \n line ends)
		RECT		Owner	= {};		// the chart window, to center the editor on
		HWND		Chart	= nullptr;	// repainted on OK, so the saved text shows right away
		EditorTexts	Texts;
	};

	struct EditorHandle
	{
		std::shared_ptr<EditorState>	State;
		HANDLE							Thread = nullptr;
	};

	// Saved editor text the study function hasn't applied yet, so the chart can draw it
	// before that next call.
	bool PendingEditorText(SCStudyInterfaceRef sc, int pointerKey, std::string& text)
	{
		const EditorHandle* handle = (const EditorHandle*)sc.GetPersistentPointer(pointerKey);
		if (handle == nullptr)
			return false;
		AcquireSRWLockExclusive(&handle->State->Lock);
		const bool pending = handle->State->Done && handle->State->Saved;
		if (pending)
			text = handle->State->Text;
		ReleaseSRWLockExclusive(&handle->State->Lock);
		return pending;
	}

	enum EditorControl { EC_INTRO = 101, EC_EDIT, EC_HELP };

	struct EditorWindow
	{
		EditorState*	State		= nullptr;
		HWND			Intro		= nullptr;
		HWND			Edit		= nullptr;
		HWND			Help		= nullptr;
		HWND			Ok			= nullptr;
		HWND			Cancel		= nullptr;
		HFONT			UiFont		= nullptr;
		HFONT			EditFont	= nullptr;
		int				Dpi			= 96;
	};

	int Scale(const EditorWindow* w, int dips)
	{
		return MulDiv(dips, w->Dpi, 96);
	}

	void LayoutEditor(HWND hwnd, EditorWindow* w)
	{
		RECT client;
		Api().GetClientRect(hwnd, &client);
		const int margin = Scale(w, 16), gap = Scale(w, 10);
		const int width = client.right - 2 * margin;
		const int introHeight = Scale(w, w->State->Texts.IntroHeight), helpHeight = Scale(w, w->State->Texts.HelpHeight);
		const int buttonHeight = Scale(w, 30), buttonWidth = Scale(w, 100);

		const int buttonTop = client.bottom - margin - buttonHeight;
		const int helpTop = buttonTop - gap - helpHeight;
		const int editTop = margin + introHeight + gap;

		Api().MoveWindow(w->Intro, margin, margin, width, introHeight, TRUE);
		Api().MoveWindow(w->Edit, margin, editTop, width, (std::max)(Scale(w, 60), helpTop - gap - editTop), TRUE);
		Api().MoveWindow(w->Help, margin, helpTop, width, helpHeight, TRUE);
		Api().MoveWindow(w->Cancel, client.right - margin - buttonWidth, buttonTop, buttonWidth, buttonHeight, TRUE);
		Api().MoveWindow(w->Ok, client.right - margin - 2 * buttonWidth - Scale(w, 8), buttonTop, buttonWidth, buttonHeight, TRUE);
	}

	LRESULT CALLBACK EditorProc(HWND hwnd, UINT message, WPARAM wParam, LPARAM lParam)
	{
		EditorWindow* w = (EditorWindow*)Api().GetWindowLongPtrW(hwnd, GWLP_USERDATA);
		switch (message)
		{
			case WM_NCCREATE:
			{
				EditorWindow* created = (EditorWindow*)((CREATESTRUCTW*)lParam)->lpCreateParams;
				Api().SetWindowLongPtrW(hwnd, GWLP_USERDATA, (LONG_PTR)created);
				break;
			}

			case WM_CREATE:
			{
				const EditorTexts& texts = w->State->Texts;
				HDC dc = Api().GetDC(hwnd);
				w->Dpi = Api().GetDeviceCaps(dc, LOGPIXELSY);
				Api().ReleaseDC(hwnd, dc);
				w->UiFont = Api().CreateFontW(-MulDiv(10, w->Dpi, 72), 0, 0, 0, FW_NORMAL, FALSE, FALSE, FALSE, DEFAULT_CHARSET,
					OUT_DEFAULT_PRECIS, CLIP_DEFAULT_PRECIS, CLEARTYPE_QUALITY, DEFAULT_PITCH, L"Segoe UI");
				w->EditFont = texts.Monospace
					? Api().CreateFontW(-MulDiv(10, w->Dpi, 72), 0, 0, 0, FW_NORMAL, FALSE, FALSE, FALSE, DEFAULT_CHARSET,
						OUT_DEFAULT_PRECIS, CLIP_DEFAULT_PRECIS, CLEARTYPE_QUALITY, FIXED_PITCH, L"Consolas")
					: nullptr;

				const DWORD editStyle = WS_CHILD | WS_VISIBLE | WS_TABSTOP | WS_VSCROLL | ES_MULTILINE | ES_AUTOVSCROLL | ES_WANTRETURN | ES_NOHIDESEL
					| (texts.WordWrap ? 0 : WS_HSCROLL | ES_AUTOHSCROLL);

				HINSTANCE instance = (HINSTANCE)Api().GetWindowLongPtrW(hwnd, GWLP_HINSTANCE);
				w->Intro = Api().CreateWindowExW(0, L"STATIC", texts.Intro,
					WS_CHILD | WS_VISIBLE | SS_LEFT, 0, 0, 0, 0, hwnd, (HMENU)(INT_PTR)EC_INTRO, instance, nullptr);
				w->Edit = Api().CreateWindowExW(WS_EX_CLIENTEDGE, L"EDIT", L"", editStyle,
					0, 0, 0, 0, hwnd, (HMENU)(INT_PTR)EC_EDIT, instance, nullptr);
				w->Help = Api().CreateWindowExW(0, L"STATIC", texts.Help,
					WS_CHILD | WS_VISIBLE | SS_LEFT, 0, 0, 0, 0, hwnd, (HMENU)(INT_PTR)EC_HELP, instance, nullptr);
				w->Ok = Api().CreateWindowExW(0, L"BUTTON", texts.OkButton, WS_CHILD | WS_VISIBLE | WS_TABSTOP | BS_DEFPUSHBUTTON,
					0, 0, 0, 0, hwnd, (HMENU)(INT_PTR)IDOK, instance, nullptr);
				w->Cancel = Api().CreateWindowExW(0, L"BUTTON", L"Cancel", WS_CHILD | WS_VISIBLE | WS_TABSTOP | BS_PUSHBUTTON,
					0, 0, 0, 0, hwnd, (HMENU)(INT_PTR)IDCANCEL, instance, nullptr);

				for (HWND child : {w->Intro, w->Help, w->Ok, w->Cancel})
					Api().SendMessageW(child, WM_SETFONT, (WPARAM)w->UiFont, TRUE);
				Api().SendMessageW(w->Edit, WM_SETFONT, (WPARAM)(w->EditFont != nullptr ? w->EditFont : w->UiFont), TRUE);
				Api().SendMessageW(w->Edit, EM_SETLIMITTEXT, 0, 0);

				std::string text;
				AcquireSRWLockExclusive(&w->State->Lock);
				text = w->State->Text;
				ReleaseSRWLockExclusive(&w->State->Lock);
				Api().SetWindowTextW(w->Edit, Widen(EditorLineEnds(text, true)).c_str());

				LayoutEditor(hwnd, w);
				Api().SetFocus(w->Edit);
				Api().SendMessageW(w->Edit, EM_SETSEL, (WPARAM)-1, (LPARAM)-1);
				return 0;
			}

			case WM_SIZE:
				if (w != nullptr && w->Edit != nullptr)
					LayoutEditor(hwnd, w);
				return 0;

			case WM_GETMINMAXINFO:
			{
				const int dpi = w != nullptr ? w->Dpi : 96;
				((MINMAXINFO*)lParam)->ptMinTrackSize.x = MulDiv(520, dpi, 96);
				((MINMAXINFO*)lParam)->ptMinTrackSize.y = MulDiv(420, dpi, 96);
				return 0;
			}

			case WM_CTLCOLORSTATIC:
				Api().SetBkMode((HDC)wParam, TRANSPARENT);
				return (LRESULT)Api().GetSysColorBrush(COLOR_BTNFACE);

			case WM_COMMAND:
				if (LOWORD(wParam) == IDOK)
				{
					const int length = Api().GetWindowTextLengthW(w->Edit);
					std::wstring wide((size_t)length + 1, L'\0');
					Api().GetWindowTextW(w->Edit, &wide[0], length + 1);
					wide.resize((size_t)length);

					AcquireSRWLockExclusive(&w->State->Lock);
					w->State->Text	= EditorLineEnds(Narrow(wide), false);
					w->State->Saved	= true;
					ReleaseSRWLockExclusive(&w->State->Lock);
					Api().DestroyWindow(hwnd);  // ends the message loop, which marks the state Done
					return 0;
				}
				if (LOWORD(wParam) == IDCANCEL)
				{
					Api().DestroyWindow(hwnd);
					return 0;
				}
				break;

			case WM_CLOSE:
				Api().DestroyWindow(hwnd);
				return 0;

			case WM_DESTROY:
				Api().PostQuitMessage(0);
				return 0;
		}
		return Api().DefWindowProcW(hwnd, message, wParam, lParam);
	}

	DWORD WINAPI EditorThread(LPVOID parameter)
	{
		std::shared_ptr<EditorState>* owned = (std::shared_ptr<EditorState>*)parameter;
		const std::shared_ptr<EditorState> state = *owned;
		delete owned;
		const EditorTexts& texts = state->Texts;

		HINSTANCE instance = nullptr;
		GetModuleHandleExW(GET_MODULE_HANDLE_EX_FLAG_FROM_ADDRESS | GET_MODULE_HANDLE_EX_FLAG_UNCHANGED_REFCOUNT,
			(LPCWSTR)(void*)&EditorProc, &instance);

		WNDCLASSEXW windowClass = {};
		windowClass.cbSize			= sizeof(windowClass);
		windowClass.lpfnWndProc		= EditorProc;
		windowClass.hInstance		= instance;
		windowClass.hCursor			= Api().LoadCursorW(nullptr, MAKEINTRESOURCEW(32512));  // IDC_ARROW
		windowClass.hbrBackground	= Api().GetSysColorBrush(COLOR_BTNFACE);
		windowClass.lpszClassName	= texts.ClassName;
		Api().RegisterClassExW(&windowClass);  // fails harmlessly if another chart already registered it

		EditorWindow window;
		window.State = state.get();

		// NinjaTrader's editor size, centered on the chart.
		HDC screen = Api().GetDC(nullptr);
		const int dpi = Api().GetDeviceCaps(screen, LOGPIXELSY);
		Api().ReleaseDC(nullptr, screen);
		const int width = MulDiv(760, dpi, 96), height = MulDiv(570, dpi, 96);
		const RECT owner = state->Owner;
		const int x = owner.right > owner.left ? owner.left + (owner.right - owner.left - width) / 2 : CW_USEDEFAULT;
		const int y = owner.bottom > owner.top ? owner.top + (owner.bottom - owner.top - height) / 2 : CW_USEDEFAULT;

		HWND hwnd = Api().CreateWindowExW(WS_EX_CONTROLPARENT | WS_EX_TOPMOST, texts.ClassName, texts.Title,
			WS_OVERLAPPEDWINDOW, (std::max)(0, x), (std::max)(0, y), width, height, nullptr, nullptr, instance, &window);

		AcquireSRWLockExclusive(&state->Lock);
		state->Window = hwnd;
		ReleaseSRWLockExclusive(&state->Lock);

		if (hwnd != nullptr)
		{
			Api().ShowWindow(hwnd, SW_SHOW);
			Api().SetForegroundWindow(hwnd);

			MSG message;
			while (Api().GetMessageW(&message, nullptr, 0, 0) > 0)
			{
				// A multi-line edit control keeps every key, so handle the dialog keys here:
				// Ctrl+A selects all, Tab moves to the buttons, Esc cancels.
				if (message.message == WM_KEYDOWN && message.hwnd == window.Edit)
				{
					const bool control = (Api().GetKeyState(VK_CONTROL) & 0x8000) != 0;
					if (message.wParam == 'A' && control)
					{
						Api().SendMessageW(window.Edit, EM_SETSEL, 0, -1);
						continue;
					}
					if (message.wParam == VK_TAB && !control)
					{
						Api().SetFocus(Api().GetNextDlgTabItem(hwnd, window.Edit, (Api().GetKeyState(VK_SHIFT) & 0x8000) != 0));
						continue;
					}
					if (message.wParam == VK_ESCAPE)
					{
						Api().PostMessageW(hwnd, WM_COMMAND, IDCANCEL, 0);
						continue;
					}
				}
				if (!Api().IsDialogMessageW(hwnd, &message))
				{
					Api().TranslateMessage(&message);
					Api().DispatchMessageW(&message);
				}
			}
		}

		if (window.UiFont != nullptr)
			Api().DeleteObject(window.UiFont);
		if (window.EditFont != nullptr)
			Api().DeleteObject(window.EditFont);

		AcquireSRWLockExclusive(&state->Lock);
		state->Window	= nullptr;
		state->Done		= true;
		const bool saved = state->Saved;
		const HWND chart = state->Chart;
		ReleaseSRWLockExclusive(&state->Lock);

		if (saved && chart != nullptr && Api().IsWindow(chart))
			Api().InvalidateRect(chart, nullptr, FALSE);
		return 0;
	}

	// Opens the editor on currentText, or brings it to the front if it's already open.
	void OpenEditor(SCStudyInterfaceRef sc, int pointerKey, const EditorTexts& texts, const char* currentText)
	{
		if (!Api().Loaded)
		{
			sc.AddMessageToLog(texts.OpenFailed, 1);
			return;
		}

		void*& slot = sc.GetPersistentPointer(pointerKey);
		EditorHandle* handle = (EditorHandle*)slot;
		if (handle != nullptr)
		{
			AcquireSRWLockExclusive(&handle->State->Lock);
			HWND hwnd = handle->State->Window;
			ReleaseSRWLockExclusive(&handle->State->Lock);
			if (hwnd != nullptr)
			{
				Api().ShowWindow(hwnd, SW_RESTORE);
				Api().SetForegroundWindow(hwnd);
			}
			return;
		}

		handle = new EditorHandle;
		handle->State = std::make_shared<EditorState>();
		handle->State->Text = currentText != nullptr ? currentText : "";
		handle->State->Texts = texts;
		if (sc.ChartWindowHandle != nullptr)
		{
			handle->State->Chart = (HWND)sc.ChartWindowHandle;
			Api().GetWindowRect(handle->State->Chart, &handle->State->Owner);
		}

		std::shared_ptr<EditorState>* parameter = new std::shared_ptr<EditorState>(handle->State);
		handle->Thread = CreateThread(nullptr, 0, EditorThread, parameter, 0, nullptr);
		if (handle->Thread == nullptr)
		{
			delete parameter;
			delete handle;
			sc.AddMessageToLog(texts.OpenFailed, 1);
			return;
		}
		slot = handle;
		sc.UpdateAlways = 1;
	}

	// Once the editor closes, writes saved text into sc.Input[inputIndex]. With closing set
	// (the study is being removed or the DLL released), closes the editor first and
	// discards its edits.
	void PollEditor(SCStudyInterfaceRef sc, int pointerKey, int inputIndex, bool closing)
	{
		void*& slot = sc.GetPersistentPointer(pointerKey);
		EditorHandle* handle = (EditorHandle*)slot;
		if (handle == nullptr)
			return;

		if (closing)
		{
			AcquireSRWLockExclusive(&handle->State->Lock);
			HWND hwnd = handle->State->Window;
			ReleaseSRWLockExclusive(&handle->State->Lock);
			if (hwnd != nullptr)
				Api().PostMessageW(hwnd, WM_CLOSE, 0, 0);
			WaitForSingleObject(handle->Thread, 3000);
		}

		AcquireSRWLockExclusive(&handle->State->Lock);
		const bool done		= handle->State->Done;
		const bool saved	= handle->State->Saved;
		const std::string text = handle->State->Text;
		ReleaseSRWLockExclusive(&handle->State->Lock);

		if (!done && !closing)
		{
			sc.UpdateAlways = 1;
			return;
		}

		if (saved && !closing)
		{
			sc.Input[inputIndex].SetString(text.c_str());
			sc.AddMessageToLog(handle->State->Texts.SavedMessage, 0);
		}

		WaitForSingleObject(handle->Thread, 1000);
		CloseHandle(handle->Thread);
		delete handle;
		slot = nullptr;
		sc.UpdateAlways = 0;
	}
	// ==== End of shared multi-line editor ====

	// ---- The levels editor, the clipboard and Discord in the study (spec B.4.9, D) ----

	const char* const EDIT_MENU_TEXT	= "Tatanka AMT: Edit Levels...";
	const char* const PASTE_MENU_TEXT	= "Tatanka AMT: Paste Levels from Clipboard";

	// NinjaTrader's paste box is a large text area; "Edit Levels..." opens the shared editor with Pine's
	// instructions (PINE:204).
	EditorTexts LevelsEditorTexts()
	{
		EditorTexts t;
		t.ClassName		= L"TatankaAmtLevelsEditor";
		t.Title			= L"Tatanka AMT - Daily Levels";
		t.Intro			= L"Paste the one-line paste line or the Pivot Level / Resistance Levels / Support Levels block.";
		t.Help			= L"Paste the one-line paste line:\r\n"
						  L"2026-09-30, 5500, 5510, 5525, 5490, 5475\r\n"
						  L"(date, pivot, then prices; above the pivot = resistance, below = support)\r\n\r\n"
						  L"or the three-line block:\r\n"
						  L"Pivot Level: 5500\r\n"
						  L"Resistance Levels: 5510, 5525, 5540\r\n"
						  L"Support Levels: 5490, 5475, 5460\r\n\r\n"
						  L"If both are pasted, the paste line wins. Prices are comma-separated decimals.";
		t.OkButton		= L"Save";
		t.SavedMessage	= "Tatanka AMT: levels saved.";
		t.OpenFailed	= "Tatanka AMT: the editor could not be opened.";
		t.IntroHeight	= 40;
		t.HelpHeight	= 200;
		t.WordWrap		= true;
		t.Monospace		= true;
		return t;
	}

	// The clipboard's text, UTF-8 (If/Then's).
	bool ReadClipboardUtf8(std::string& text)
	{
		if (!Api().Loaded)
			return false;
		if (!Api().OpenClipboard(nullptr))
			return false;

		bool ok = false;
		HANDLE handle = Api().GetClipboardData(CF_UNICODETEXT);
		if (handle != nullptr)
		{
			const wchar_t* wide = (const wchar_t*)GlobalLock(handle);
			if (wide != nullptr)
			{
				const int bytes = WideCharToMultiByte(CP_UTF8, 0, wide, -1, nullptr, 0, nullptr, nullptr);
				if (bytes > 1)
				{
					std::vector<char> buffer((size_t)bytes);
					WideCharToMultiByte(CP_UTF8, 0, wide, -1, buffer.data(), bytes, nullptr, nullptr);
					text.assign(buffer.data());
					ok = true;
				}
				GlobalUnlock(handle);
			}
		}
		Api().CloseClipboard();
		return ok;
	}

	// How "Paste Levels from Clipboard" reads the clipboard (the tests give their own text).
	std::function<bool(std::string&)>& ClipboardReader()
	{
		static std::function<bool(std::string&)> reader = ReadClipboardUtf8;
		return reader;
	}

	// The two menu items (added once, again after a chartbook reload), their events and the editor
	// (spec B.4.9; If/Then's pattern). Saved or pasted text goes into the paste box input, which the
	// study reads at once: the engine is built again with the new levels.
	void LevelsMenu(SCStudyInterfaceRef sc)
	{
		int& editMenuId		= sc.GetPersistentInt(PI_EDIT_MENU_ID);
		int& pasteMenuId	= sc.GetPersistentInt(PI_PASTE_MENU_ID);
		if (editMenuId <= 0)
			editMenuId = sc.AddACSChartShortcutMenuItem(sc.ChartNumber, EDIT_MENU_TEXT);
		if (pasteMenuId <= 0)
			pasteMenuId = sc.AddACSChartShortcutMenuItem(sc.ChartNumber, PASTE_MENU_TEXT);
		if (editMenuId > 0 && sc.MenuEventID == editMenuId)
			OpenEditor(sc, PP_EDITOR, LevelsEditorTexts(), StringInput(sc, IN_LEVELS_TEXT).c_str());
		// Saved text is applied here, on the next call (the engine is built from it); the shared block's
		// PendingEditorText (a drawing callback's early look at it) has no use in this study.
		static_cast<void>(&PendingEditorText);
		PollEditor(sc, PP_EDITOR, IN_LEVELS_TEXT, false);
		if (pasteMenuId > 0 && sc.MenuEventID == pasteMenuId)
		{
			std::string clipboard, error;
			LevelsDocument document;
			if (!ClipboardReader()(clipboard) || TrimNet(Utf16Of(clipboard)).empty())
				error = "The clipboard holds no text.";
			else if (LevelsDocument::Parse(clipboard, true, document, error) && document.Levels.empty())
				error = "No levels found.";
			if (error.empty())
			{
				sc.Input[IN_LEVELS_TEXT].SetString(EditorLineEnds(clipboard, false).c_str());
				sc.AddMessageToLog("Tatanka AMT: levels pasted from the clipboard.", 0);
			}
			else
				sc.AddMessageToLog(("Tatanka AMT: the clipboard has no levels (" + error + ")").c_str(), 1);
		}
	}

	bool EditorOpen(SCStudyInterfaceRef sc)
	{
		return sc.GetPersistentPointer(PP_EDITOR) != nullptr;
	}

	// Sierra Chart's HTTP POST (spec D.3): JSON with NinjaTrader's User-Agent; the answer comes on a later
	// call with sc.HTTPRequestID.
	struct SierraHttp final : DiscordTransport
	{
		s_sc* Sc = nullptr;

		int Post(const std::string& url, const std::string& body) override
		{
			n_ACSIL::s_HTTPHeader headers[2];
			headers[0].Name		= "Content-Type";
			headers[0].Value	= "application/json";
			headers[1].Name		= "User-Agent";
			headers[1].Value	= (std::string("TatankaAMTToolkit/") + BRAND_VERSION).c_str();
			return Sc->MakeHTTPPOSTRequest != nullptr ? Sc->MakeHTTPPOSTRequest(url.c_str(), body.c_str(), headers, 2) : 0;
		}
	};

	// The Discord switch and URL (NT:1714-1718): a sender for a valid URL, NinjaTrader's setup notice for
	// an invalid one, nothing when off (the default). A changed URL drops the old sender and its queue; the
	// new one waits for the answer to a request the old one still has open (one request at a time).
	void UpdateDiscord(SCStudyInterfaceRef sc, StudyState& st)
	{
		const bool enabled = sc.Input[IN_DISCORD_ENABLE].GetYesNo() != 0;
		const std::string url = StringInput(sc, IN_DISCORD_URL);
		const uint64_t key = enabled ? Fnv1a64Text(FNV64_BASIS, url) | 1u : 0;
		if (key == st.DiscordKey)
			return;
		st.DiscordKey = key;
		const std::unique_ptr<DiscordSender> old = std::move(st.Discord);
		st.DiscordSetupWarning.clear();
		if (!enabled)
			return;
		std::string endpoint, error;
		if (ValidateDiscordEndpoint(url, endpoint, error))
		{
			st.Discord.reset(new DiscordSender(DiscordRequestUrl(endpoint)));
			if (old)
				st.Discord->Adopt(*old);
		}
		else
			st.DiscordSetupWarning = "Discord disabled: " + error;
	}

	// One pump of the Discord sender per study call: its response, its timeout, its next post.
	void PumpDiscord(SCStudyInterfaceRef sc, StudyState& st)
	{
		if (!st.Discord)
			return;
		SierraHttp http;
		http.Sc = &sc;
		st.Discord->Pump(st.NowMs(), sc.HTTPRequestID, sc.HTTPRequestID != 0 ? std::string(sc.HTTPResponse.GetChars()) : std::string(), http);
	}

	// ---- Defaults (spec A.2, A.3, C.1) ----

	void SetSubgraph(SCStudyInterfaceRef sc, int k, const char* name, uint32_t color, int width, int style, bool visible, bool tag)
	{
		SCSubgraphRef g = sc.Subgraph[k];
		g.Name				= name;
		g.PrimaryColor		= color;
		g.LineWidth			= (uint16_t)width;
		g.LineStyle			= (SubgraphLineStyles)style;
		g.DrawStyle			= visible ? DRAWSTYLE_SUBGRAPH_NAME_AND_VALUE_LABELS_ONLY : DRAWSTYLE_HIDDEN;
		g.DrawZeros			= 0;
		g.LineLabel			= tag ? LL_DISPLAY_VALUE | LL_VALUE_ALIGN_VALUES_SCALE | LL_VALUE_ALIGN_CENTER : 0;
		g.DisplayNameValueInWindowsFlags = 0;
		// Sierra shows every subgraph on the Region Data Line by default; most of these hold 0 (they
		// carry line settings, not values), so "PIVOT: 0.00 RES: 0.00 ..." would fill the line.
		g.DisplayNameValueInDataLine = 0;
		g.UseLabelsColor	= 0;
		g.SecondaryColorUsed = 0;
	}

	void SetDefaults(SCStudyInterfaceRef sc)
	{
		sc.GraphName		= "Tatanka AMT Toolkit";
		sc.GraphShortName	= "Tatanka AMT";
		sc.StudyDescription	= "Tatanka AMT Toolkit v1.0.0: a complete Auction Market Theory read on one chart. Value, balance vs trend, trapped inventory, "
							  "unfinished business and reference prices. Free and open source (MPL 2.0). tatankatrading.com";
		sc.AutoLoop			= 0;
		sc.GraphRegion		= 0;
		sc.ScaleRangeType	= SCALE_SAMEASREGION;
		sc.ValueFormat		= VALUEFORMAT_INHERITED;
		sc.DrawStudyUnderneathMainPriceGraph = 0;	// over the bars, as NinjaTrader draws (ranges need it)
		sc.DisplayStudyName	= 1;
		sc.DisplayStudyInputValues = 0;
		sc.UpdateAlways		= 0;
		sc.MaintainAdditionalChartDataArrays = 0;

		const uint32_t WHITE = RGB(255, 255, 255);
		SetSubgraph(sc, SG_PIVOT, "PIVOT", RGB(0xFD, 0xD8, 0x35), 1, LINESTYLE_DOT, true, false);
		SetSubgraph(sc, SG_RES, "RES", RGB(0xF2, 0x36, 0x45), 1, LINESTYLE_DOT, true, false);
		SetSubgraph(sc, SG_SUPP, "SUPP", RGB(0x4C, 0xAF, 0x50), 1, LINESTYLE_DOT, true, false);
		SetSubgraph(sc, SG_LEVEL_ZONE_BORDER, "Level Zone Border", RGB(0x78, 0x7B, 0x86), 1, LINESTYLE_SOLID, true, false);
		SetSubgraph(sc, SG_PD_HIGH, "pdHigh", WHITE, 1, LINESTYLE_SOLID, true, true);
		SetSubgraph(sc, SG_PD_LOW, "pdLow", WHITE, 1, LINESTYLE_SOLID, true, true);
		SetSubgraph(sc, SG_PD_OPEN, "pdOpen", RGB(0x21, 0x96, 0xF3), 1, LINESTYLE_SOLID, false, false);
		SetSubgraph(sc, SG_PD_POC, "pdPOC", WHITE, 1, LINESTYLE_SOLID, true, false);
		SetSubgraph(sc, SG_PD_VAH, "pdVAH", RGB(0x9C, 0x27, 0xB0), 1, LINESTYLE_SOLID, true, false);
		SetSubgraph(sc, SG_PD_VAL, "pdVAL", RGB(0x9C, 0x27, 0xB0), 1, LINESTYLE_SOLID, true, false);
		SetSubgraph(sc, SG_FILL80, "80% Rule Fill", RGB(0x9C, 0x27, 0xB0), 1, LINESTYLE_SOLID, true, false);
		sc.Subgraph[SG_FILL80].SecondaryColor		= RGB(0xEA, 0x80, 0xFC);
		sc.Subgraph[SG_FILL80].SecondaryColorUsed	= 1;
		SetSubgraph(sc, SG_OVN_HIGH, "OVN High", WHITE, 1, LINESTYLE_SOLID, true, false);
		sc.Subgraph[SG_OVN_HIGH].UseLabelsColor	= 1;
		sc.Subgraph[SG_OVN_HIGH].LabelsColor	= WHITE;
		SetSubgraph(sc, SG_OVN_LOW, "OVN Low", WHITE, 1, LINESTYLE_SOLID, true, false);
		sc.Subgraph[SG_OVN_LOW].UseLabelsColor	= 1;
		sc.Subgraph[SG_OVN_LOW].LabelsColor		= WHITE;
		SetSubgraph(sc, SG_IB_HIGH, "IB High", RGB(0xFF, 0xCC, 0x80), 1, LINESTYLE_SOLID, true, true);
		SetSubgraph(sc, SG_IB_LOW, "IB Low", RGB(0xFF, 0xCC, 0x80), 1, LINESTYLE_SOLID, true, true);
		SetSubgraph(sc, SG_IB_MID, "IB Midpoint", RGB(0xFF, 0xCC, 0x80), 1, LINESTYLE_DOT, false, false);
		SetSubgraph(sc, SG_VWAP, "RTH VWAP", WHITE, 2, LINESTYLE_SOLID, false, false);
		SetSubgraph(sc, SG_DOPEN, "dOpen", RGB(0x21, 0x96, 0xF3), 1, LINESTYLE_SOLID, false, false);
		SetSubgraph(sc, SG_WK_OPEN, "wkOpen", WHITE, 2, LINESTYLE_SOLID, true, false);
		SetSubgraph(sc, SG_PW_HIGH, "pwHigh", WHITE, 2, LINESTYLE_SOLID, true, true);
		sc.Subgraph[SG_PW_HIGH].UseLabelsColor	= 1;
		sc.Subgraph[SG_PW_HIGH].LabelsColor		= WHITE;
		SetSubgraph(sc, SG_PW_LOW, "pwLow", WHITE, 2, LINESTYLE_SOLID, true, true);
		sc.Subgraph[SG_PW_LOW].UseLabelsColor	= 1;
		sc.Subgraph[SG_PW_LOW].LabelsColor		= WHITE;
		SetSubgraph(sc, SG_PM_VAH, "pmVAH", WHITE, 3, LINESTYLE_SOLID, true, true);
		SetSubgraph(sc, SG_PM_VAL, "pmVAL", WHITE, 3, LINESTYLE_SOLID, true, true);
		SetSubgraph(sc, SG_PM_POC, "pmPOC", WHITE, 3, LINESTYLE_SOLID, true, true);
		SetSubgraph(sc, SG_PM_HIGH, "pmHigh", WHITE, 3, LINESTYLE_SOLID, true, true);
		SetSubgraph(sc, SG_PM_LOW, "pmLow", WHITE, 3, LINESTYLE_SOLID, true, true);
		SetSubgraph(sc, SG_VA_HIST, "VA Histogram", RGB(0x78, 0x90, 0x9C), 1, LINESTYLE_SOLID, true, false);
		SetSubgraph(sc, SG_OUT_HIST, "Outer Histogram", RGB(0x78, 0x7B, 0x86), 1, LINESTYLE_SOLID, true, false);
		SetSubgraph(sc, SG_DEV_POC, "Developing POC", RGB(0x78, 0x90, 0x9C), 2, LINESTYLE_SOLID, true, true);
		SetSubgraph(sc, SG_DEV_VAH, "Developing VAH", RGB(0x78, 0x7B, 0x86), 2, LINESTYLE_SOLID, true, false);
		SetSubgraph(sc, SG_DEV_VAL, "Developing VAL", RGB(0x78, 0x7B, 0x86), 2, LINESTYLE_SOLID, true, false);
		SetSubgraph(sc, SG_WALL, "Wall", RGB(0xE6, 0xB3, 0x00), 1, LINESTYLE_SOLID, false, false);
		SetSubgraph(sc, SG_SP, "Single Print", RGB(0xFF, 0x98, 0x00), 1, LINESTYLE_SOLID, true, false);
		SetSubgraph(sc, SG_SP_BORDER, "Single Print Border", RGB(0xFF, 0x98, 0x00), 1, LINESTYLE_SOLID, false, false);
		SetSubgraph(sc, SG_POOR_HIGH, "Poor High", RGB(0xF2, 0x36, 0x45), 2, LINESTYLE_DOT, true, false);
		SetSubgraph(sc, SG_POOR_LOW, "Poor Low", RGB(0x4C, 0xAF, 0x50), 2, LINESTYLE_DOT, true, false);
		SetSubgraph(sc, SG_NPOC_DAILY, "Daily nPOC", RGB(0xFF, 0xC0, 0xCB), 1, LINESTYLE_SOLID, true, false);
		SetSubgraph(sc, SG_NPOC_WEEKLY, "Weekly nPOC", RGB(0xFF, 0xC0, 0xCB), 2, LINESTYLE_SOLID, true, false);
		SetSubgraph(sc, SG_NPOC_MONTHLY, "Monthly nPOC", RGB(0xFF, 0xC0, 0xCB), 3, LINESTYLE_SOLID, true, false);
		SetSubgraph(sc, SG_SETTLE, "SETTLE", RGB(0x78, 0x7B, 0x86), 1, LINESTYLE_DASH, true, false);
		SetSubgraph(sc, SG_TRAP, "TRAP ACTIVE", RGB(0x00, 0xFF, 0x00), 1, LINESTYLE_DASH, true, false);
		SetSubgraph(sc, SG_SPIKE_SUP, "Spike Base (Supp)", RGB(0x4C, 0xAF, 0x50), 1, LINESTYLE_SOLID, true, false);
		SetSubgraph(sc, SG_SPIKE_RES, "Spike Base (Res)", RGB(0xF2, 0x36, 0x45), 1, LINESTYLE_SOLID, true, false);

		auto choice = [&sc](int i, const char* name, const char* list, int index, const char* description = nullptr)
		{
			sc.Input[i].Name = name;
			sc.Input[i].SetCustomInputStrings(list);
			sc.Input[i].SetCustomInputIndex(index);
			if (description != nullptr)
				sc.Input[i].SetDescription(description);
		};
		auto yesNo = [&sc](int i, const char* name, int value, const char* description = nullptr)
		{
			sc.Input[i].Name = name;
			sc.Input[i].SetYesNo(value);
			if (description != nullptr)
				sc.Input[i].SetDescription(description);
		};
		auto integer = [&sc](int i, const char* name, int value, int lo, int hi, const char* description = nullptr)
		{
			sc.Input[i].Name = name;
			sc.Input[i].SetInt(value);
			if (lo <= hi)
				sc.Input[i].SetIntLimits(lo, hi);
			if (description != nullptr)
				sc.Input[i].SetDescription(description);
		};
		auto number = [&sc](int i, const char* name, double value, double lo, double hi, const char* description = nullptr)
		{
			sc.Input[i].Name = name;
			sc.Input[i].SetDouble(value);
			if (lo <= hi)
				sc.Input[i].SetDoubleLimits(lo, hi);
			if (description != nullptr)
				sc.Input[i].SetDescription(description);
		};
		auto text = [&sc](int i, const char* name, const char* value, const char* description = nullptr)
		{
			sc.Input[i].Name = name;
			sc.Input[i].SetString(value);
			if (description != nullptr)
				sc.Input[i].SetDescription(description);
		};
		auto time = [&sc](int i, const char* name, int seconds, const char* description = nullptr)
		{
			sc.Input[i].Name = name;
			sc.Input[i].SetTime(seconds);
			if (description != nullptr)
				sc.Input[i].SetDescription(description);
		};
		const int NONE = 1;		// with hi = 0 (lo > hi): no limits
		const char* const LABELS_4 = "Tiny;Small;Normal;Large;Off";
		const char* const LABELS_5 = "Tiny;Small;Normal;Large;Huge;Off";

		// 1. Global
		choice(IN_ROW_SCALE, "1. Global: Profile Row Scale", "Auto;1x;2x;5x;10x;20x;50x;100x", 0,
			"Ticks per profile row, naked POC bin and single-print block. Auto keeps rows near 0.0035% of price: ES, RTY, CL, GC 1x; YM 2x; NQ 5x. "
			"Pick a fixed scale if a symbol loads slowly. Row Size is a floor.");
		number(IN_MANUAL_TICK, "1. Global: Manual Tick Size (0 = Auto)", 0, 0, 1e9,
			"0 = Auto: auto-detects a sensible base tick for the current instrument. ES/NQ/MES/MNQ use mintick (0.25). CL=0.05, NG=0.005, GC=0.50. "
			"Otherwise the base tick for zones, profiles, TPO, and OVN.");
		choice(IN_FORCE_ON_TOP, "1. Global: Force on Top", "Daily Levels (All);Profile POC;Profile VAH;Profile VAL;IB Midpoint;IB High;IB Low;pdPOC;"
			"Prev Day High;Prev Day Low;OVN High;OVN Low;Prev Month VAH;Prev Month VAL;Spike Base", 0,
			"Select which line draws ON TOP of everything else to prevent visual clutter.");
		yesNo(IN_HIDE_ALL_LABELS, "1. Global: Hide All Labels & Price Tags", 0,
			"Master switch. Hides every label, including IB and OVN labels, and the price-axis tags. Lines stay.");
		yesNo(IN_SHOW_TAGS, "1. Global: Show Price-Axis Tags", 1);
		yesNo(IN_TZ_GUARD, "1. Global: Warn if Session Times Were Changed", 1,
			"Every session field and hour input in this indicator is CME EXCHANGE TIME (Central) and should be left at its default. Retyping them in "
			"your local timezone silently shifts every level. To see times on your own clock, change the chart's time zone (Chart Settings) - not these "
			"fields. This warning prints on the chart if any session field no longer matches its exchange-time default.");
		// 2. Levels (Stage 4)
		sc.Input[IN_LEVELS_FILE].Name = "2. Levels: Levels File (full path; supports {root})";
		sc.Input[IN_LEVELS_FILE].SetPathAndFileName("");
		sc.Input[IN_LEVELS_FILE].SetDescription("Read daily prices from a local text file. Leave blank to use Paste levels here. {root} becomes the "
			"chart's root symbol; micros use the parent (MES reads ES, MNQ reads NQ, MCL reads CL, MGC reads GC). This does not connect to Discord.");
		text(IN_LEVELS_TEXT, "2. Levels: Paste Levels Here", "",
			"Paste daily prices here when Levels file is blank. Accepts the one-line Discord paste line (2026-09-30, pivot, resistance..., "
			"support...) or the three-line Pivot Level / Resistance Levels / Support Levels block. If both are pasted, the paste line wins. No Discord "
			"connection is needed. Right-click the chart: Tatanka AMT: Edit Levels... or Paste Levels from Clipboard.");
		yesNo(IN_LVL_FLIP, "2. Levels: Flip Colors on Break (Res <-> Supp)", 1,
			"Changes resistance levels to support colors if price is above them, and vice versa.");
		number(IN_LVL_FLIP_ATR, "2. Levels: Flip ATR Buffer", 0.05, -1e9, 1e9, "Price must pass the level by this many ATRs to flip.");
		yesNo(IN_LVL_SHOW_ZONES, "2. Levels: Show Zones", 1, "Draws a shaded zone above and below each level.");
		choice(IN_LVL_ZONE_MODE, "2. Levels: Zone Size Mode", "ATR %;Ticks", 0,
			"ATR % sizes the zone as a percentage of the 14-day ATR. Ticks uses a fixed number of ticks.");
		number(IN_LVL_ZONE_ATR_PCT, "2. Levels: Zone Width (ATR %)", 0.02, 0.01, 0.50,
			"Zone extends this percentage of the 14-day ATR above and below each level. 0.05 = 5%.");
		integer(IN_LVL_ZONE_TICKS, "2. Levels: Zone Width (ticks above & below)", 8, 1, 200, "Only used when Zone Size Mode is set to Ticks.");
		integer(IN_LVL_ZONE_TRANSP, "2. Levels: Zone Transparency (0=solid, 100=clear)", 85, 0, 100);
		choice(IN_LVL_LABELS, "2. Levels: Show Labels / Label Size", "auto;tiny;small;normal;large;huge;Off", 4, "Off hides the level labels.");
		integer(IN_LVL_LABEL_OFFSET, "2. Levels: Label Offset", 40, -10000, 10000, "How far to the right the labels appear.");
		yesNo(IN_LVL_ALERTS, "2. Levels: Enable Level Alerts", 0,
			"Enable alerts for the pasted or file-loaded daily levels. Other structural groups have their own alert switches.");
		yesNo(IN_LVL_ALERT_PIVOT, "2. Levels: Pivot Alerts", 1);
		yesNo(IN_LVL_ALERT_RES, "2. Levels: Resistance Alerts", 1);
		yesNo(IN_LVL_ALERT_SUPP, "2. Levels: Support Alerts", 1);
		// 3. Prev Day (Stage 2)
		yesNo(IN_PD_USE_RTH, "3. Prev Day: Use Custom Session for High/Low", 1,
			"On: high and low of the Custom Session (RTH). Off: of the whole trading day.");
		text(IN_PD_SESSION, "3. Prev Day: Custom Session Time (CT)", "0830-1500",
			"Session for pdHigh, pdLow and pdOpen. The 80% Rule only counts bars inside it.");
		choice(IN_PD_LABELS, "3. Prev Day: Show Labels / Label Size", LABELS_4, 2, "Off hides the labels.");
		integer(IN_PD_LABEL_OFFSET, "3. Prev Day: Label Offset", 2, NONE, 0);
		yesNo(IN_PD_ALERT_HL, "3. Prev Day: Alert High/Low Break", 1, "Alerts when price breaks yesterday's High or Low.");
		// 4. Prev Value
		yesNo(IN_CC_ENABLE, "4. Prev Value: Enable Prev Day Value & 80% Rule", 1);
		number(IN_CC_VA_PCT, "4. Prev Value: Value Area %", 0.68, 0.01, 1.0);
		text(IN_CC_SESSION, "4. Prev Value: RTH Session for VA (CT)", "0830-1500:23456",
			"Bars in this session build the prior-day value (pdPOC, pdVAH, pdVAL). Its first bar is the RTH open used by OPEN, the gap test and the "
			"80% Rule.");
		choice(IN_CC_LABELS, "4. Prev Value: Show Labels / Label Size", LABELS_4, 2, "Off hides the labels.");
		integer(IN_CC_LABEL_OFFSET, "4. Prev Value: Label Offset", 2, NONE, 0);
		integer(IN_CC_VA_OPACITY, "4. Prev Value: pdVAH/pdVAL Opacity (%)", 50, 0, 100, "NinjaTrader's pdVAH/pdVAL colors are 50% transparent. 100 = solid.");
		integer(IN_CC_FILL_TRANSP, "4. Prev Value: 80% Rule Fill Transparency", 93, 0, 100,
			"0 = solid, 100 = invisible. Colors: the 80% Rule Fill subgraph (primary = active, secondary = confirmed).");
		yesNo(IN_CC_ALERT_VA, "4. Prev Value: Alert pdVAH/pdVAL/pdPOC Cross", 0,
			"Alerts when price crosses Previous Day's Value Area High, Low, or POC.");
		yesNo(IN_CC_ALERT_80, "4. Prev Value: Alert 80% Rule Confirmed", 1,
			"Fire alert when the 80% Rule setup is confirmed (price held inside value area for 60 minutes).");
		// 5. OVN (Stage 2; the session also feeds the dashboard's SESSION row)
		yesNo(IN_OVN_ENABLE, "5. OVN: Enable OVN High/Low", 1, "Tracks the High and Low of the Globex session (5pm - 8:30am).");
		text(IN_OVN_SESSION, "5. OVN: OVN Session Time (CT)", "1700-0830:123456");
		text(IN_OVN_DELETE, "5. OVN: Delete OVN Lines At (CT)", "1500-1505", "Time to remove OVN lines from the chart to clean up.");
		choice(IN_OVN_LABELS, "5. OVN: Show Labels / Label Size", LABELS_4, 2);
		integer(IN_OVN_LABEL_OFFSET, "5. OVN: Label Offset", 2, NONE, 0);
		yesNo(IN_OVN_ALERT, "5. OVN: Alert OVN Break", 1, "Alerts when price breaks the OVN High or Low during RTH.");
		// 6. IB (Stage 2)
		yesNo(IN_IB_ENABLE, "6. IB: Enable IB", 1, "Master toggle for Initial Balance levels.");
		text(IN_IB_SESSION, "6. IB: IB Calc Period (CT)", "0830-0930", "First hour of RTH (typically).");
		choice(IN_IB_EXTEND, "6. IB: Extend IB Levels", "Right;Left;Both;None", 3);
		yesNo(IN_IB_LIMIT_EXT, "6. IB: Stop Extension at Time", 1);
		text(IN_IB_STOP_TIME, "6. IB: Stop Time (CT)", "0830-1515");
		choice(IN_IB_LABELS, "6. IB: Show Labels / Label Size", "Auto;Huge;Large;Normal;Small;Tiny;Off", 3);
		choice(IN_IB_LABEL_LOC, "6. IB: Label Location", "Left;Right", 1);
		integer(IN_IB_LABEL_OFFSET, "6. IB: Label Offset", 0, NONE, 0);
		yesNo(IN_IB_ALERT_HIGH, "6. IB: Alert IB High Cross", 1, "Fire alerts when price crosses IB High (up or down).");
		yesNo(IN_IB_ALERT_LOW, "6. IB: Alert IB Low Cross", 1, "Fire alerts when price crosses IB Low (up or down).");
		text(IN_IB_ALERT_WINDOW, "6. IB: Alert Window (CT)", "0830-1500", "Only fire IB alerts during this time window.");
		// 7. VWAP
		time(IN_VWAP_START, "7. VWAP: Start Time (CT)", 8 * 3600 + 30 * 60);
		time(IN_VWAP_END, "7. VWAP: End Time (CT)", 15 * 3600);
		yesNo(IN_VWAP_ALERT, "7. VWAP: Alert VWAP Cross", 0);
		// 8. Opens (Stage 3)
		choice(IN_OPEN_LABELS, "8. Opens: Show Labels / RTH Open Label Size", LABELS_5, 2, "Off hides the dOpen label.");
		integer(IN_OPEN_LABEL_OFFSET, "8. Opens: RTH Open Label Offset", 3, NONE, 0);
		choice(IN_WK_OPEN_LABELS, "8. Opens: Show Labels / Weekly Open Label Size", LABELS_5, 2, "Off hides the wkOpen label.");
		integer(IN_WK_OPEN_LABEL_OFFSET, "8. Opens: Weekly Open Label Offset", 2, NONE, 0);
		yesNo(IN_WK_OPEN_ALERT, "8. Opens: Alert Weekly Open Cross", 1, "Alerts when price crosses the weekly (Sunday Globex) open.");
		// 9. Prev Week (Stage 3)
		choice(IN_PW_LABELS, "9. Prev Week: Show Labels / Label Size", LABELS_4, 2);
		integer(IN_PW_LABEL_OFFSET, "9. Prev Week: Label Offset", 2, NONE, 0);
		yesNo(IN_PW_ALERT, "9. Prev Week: Alert High/Low Break", 1, "Alerts when price crosses the prior week High or Low.");
		// 10. Prev Month
		choice(IN_PM_LABELS, "10. Prev Month: Show Labels / Label Size", LABELS_4, 2);
		integer(IN_PM_LABEL_OFFSET, "10. Prev Month: Label Offset", 2, NONE, 0);
		yesNo(IN_PM_ALERT, "10. Prev Month: Alert Prev Month Cross", 1, "Trigger an alert when price crosses Previous Month VAH, VAL, or POC.");
		// 11. Profile
		yesNo(IN_MVP_ENABLE, "11. Profile: Enable Volume Profile", 1,
			"Developing and completed profiles and the Developing lines. Profile alerts keep working when it is off.");
		choice(IN_MVP_PERIOD, "11. Profile: Profile Period", "Session;Weekly;Monthly;Yearly", 1,
			"Defines the timeframe for the main volume profile (e.g., Monthly Profile).");
		text(IN_MVP_SESSION, "11. Profile: Session Time (CT)", "0830-1500");
		number(IN_MVP_SESSION_DURATION, "11. Profile: Session Duration (Hours)", 6.5, 0, 1e9, "Times the wall threshold in Session mode.");
		integer(IN_MVP_CALC_PRECISION, "11. Profile: Calc Precision", 1, 1, 30, "Minutes per sub-bar used to build the profile.");
		number(IN_MVP_ROW_SIZE, "11. Profile: Row Size", 0.25, 0.25, 1e9,
			"Smallest row size of the volume profiles, in price. Profile Row Scale can make rows larger on symbols that move many ticks per bar.");
		number(IN_MVP_VA_PCT, "11. Profile: Value Area %", 68.0, 0, 100);
		integer(IN_MVP_WIDTH, "11. Profile: Profile Width (Bars)", 50, 10, 500,
			"Maximum width of the volume profile in bars. Adjust based on your chart timeframe.");
		yesNo(IN_MVP_ALIGN_RIGHT, "11. Profile: Right Align", 1);
		integer(IN_MVP_OFFSET, "11. Profile: Profile Offset (Bars)", 50, -200, 200,
			"Shifts the profile histogram left or right. Positive = right, negative = left. Works with both alignments.");
		integer(IN_MVP_VA_TRANSP, "11. Profile: VA Transparency", 75, 0, 100);
		integer(IN_MVP_OUT_TRANSP, "11. Profile: Outer Transparency", 90, 0, 100);
		choice(IN_MVP_LABELS, "11. Profile: Show Labels / Label Size", LABELS_5, 2);
		yesNo(IN_MVP_ALERTS, "11. Profile: Enable Profile Alerts", 1, "Alerts when price touches the developing profile POC, VAH, or VAL.");
		text(IN_MVP_ALERT_WINDOW, "11. Profile: Alert Window (CT)", "0830-1500");
		// 12. Walls
		integer(IN_WALL_TRANSP, "12. Walls: Wall Transparency", 25, 0, 100);
		yesNo(IN_WALL_EXTEND, "12. Walls: Extend Walls", 1);
		integer(IN_WALL_SMOOTHING, "12. Walls: Smoothing", 2, 1, 1000);
		integer(IN_WALL_MIN_DISTANCE, "12. Walls: Min Wall Distance (rows)", 40, 0, 100000, "Minimum gap between walls, counted in profile rows.");
		yesNo(IN_WALL_AUTO_SCALE, "12. Walls: Use Auto-Scale Threshold", 1);
		number(IN_WALL_START_MULT, "12. Walls: Start Mult", 2.0, NONE, 0);
		number(IN_WALL_END_MULT, "12. Walls: End Mult", 1.5, NONE, 0);
		number(IN_WALL_FIXED_MULT, "12. Walls: Fixed Mult", 2.0, NONE, 0);
		// 13. TPO (Stage 3)
		text(IN_TPO_SESSION, "13. TPO: TPO Session (CT)", "0830-1500");
		integer(IN_TPO_MINUTES, "13. TPO: TPO Period (min)", 30, 1, 1440);
		integer(IN_TPO_TICKS_PER_BLOCK, "13. TPO: Ticks per Block", 1, 1, 100000);
		integer(IN_TPO_MIN_SINGLE_TICKS, "13. TPO: Min Single Print Size (ticks)", 1, 0, 100000,
			"Measured from the first to the last block of a single-print run, so the default of 1 needs at least two blocks: the Market Profile "
			"convention that a single print takes at least two TPO prices.");
		yesNo(IN_TPO_FILTER_TAILS, "13. TPO: Filter Tails", 1);
		integer(IN_TPO_MAX_TAIL, "13. TPO: Max Tail Size", 15, NONE, 0);
		integer(IN_TPO_MAX_DAYS, "13. TPO: Max History Days", 10, 1, 100000);
		integer(IN_SP_TRANSP, "13. TPO: Single Print Transparency", 90, 0, 100, "0 = solid, 100 = invisible. Color: the Single Print subgraph.");
		choice(IN_POOR_LABELS, "13. TPO: Show Poor H/L Labels / Label Size", LABELS_5, 1);
		// 14. nPOC (Stage 3)
		yesNo(IN_NPOC_ENABLE, "14. nPOC: Enable nPOCs", 1, "Tracks untouched POCs from previous days/weeks/months.");
		number(IN_NPOC_BIN, "14. nPOC: Manual Bin Size (0 = Auto)", 0, 0, 1e9,
			"0 = Auto: POC bin = base tick times the row scale. Otherwise your bin size (times the row scale).");
		choice(IN_NPOC_LABELS, "14. nPOC: Show Labels / Label Size", LABELS_5, 1);
		integer(IN_NPOC_LABEL_OFFSET, "14. nPOC: Label Offset", 2, -50, 200);
		yesNo(IN_NPOC_ALERT, "14. nPOC: Alert nPOC Touch", 1);
		// 15. Inventory (Stage 2)
		yesNo(IN_INV_ENABLE, "15. Inventory: Enable Inventory Trap Logic", 1,
			"Detects if market positioning is 100% net long or short relative to the settlement price.");
		time(IN_INV_GLOBEX_START, "15. Inventory: Globex Start Time (CT)", 17 * 3600, "Start of the overnight count.");
		time(IN_INV_RTH_OPEN, "15. Inventory: RTH Open Time (CT)", 8 * 3600 + 30 * 60, "End of the count; the trap alert can fire in the 30 minutes after.");
		choice(IN_INV_LABELS, "15. Inventory: Show Labels / Label Size", LABELS_4, 2);
		integer(IN_INV_LABEL_OFFSET, "15. Inventory: Label Offset", 40, NONE, 0);
		yesNo(IN_INV_ALERT, "15. Inventory: Alert Trap Detected", 1);
		// 16. Spike (Stage 2)
		text(IN_SPIKE_WINDOW, "16. Spike: Spike Window (CT)", "1430-1500");
		choice(IN_SPIKE_LABELS, "16. Spike: Show Labels / Label Size", LABELS_4, 2);
		integer(IN_SPIKE_LABEL_OFFSET, "16. Spike: Label Offset", 15, NONE, 0);
		yesNo(IN_SPIKE_ALERT, "16. Spike: Alert Spike Base Test", 1, "Alerts when price retests the base of the spike.");
		// 17. Dashboard
		yesNo(IN_TBL_SHOW, "17. Dashboard: Show Dashboard", 1);
		choice(IN_TBL_POSITION, "17. Dashboard: Position", "Top Right;Top Left;Bottom Right;Bottom Left;Middle Right;Middle Left", 0);
		choice(IN_TBL_TEXT_SIZE, "17. Dashboard: Text Size", "Tiny;Small;Normal;Large", 2);
		text(IN_TBL_SESSION, "17. Dashboard: Table RTH Session (CT)", "0830-1500",
			"Sets when the dashboard's RTH rows are live and where ATR USED starts.");
		text(IN_CONTEXT_SESSION, "17. Dashboard: Context Tracking Session (CT)", "0815-1500", "Used for background calculations (highs/lows/ATR).");
		integer(IN_ATR_PERIOD, "17. Dashboard: Daily ATR Period", 14, 1, 1000,
			"Daily ATR Period feeds the dashboard, the Normal Day test and the pivot band; zones and flips always use a 14-day ATR.");
		// 18. Alerts
		yesNo(IN_CAP_ENABLE, "18. Alerts: Enable Alert Storm Cap", 1,
			"Soft cap on total alerts within a rolling window to prevent webhook flooding. When the cap is hit, one warning alert fires and further "
			"alerts are suppressed until the window rolls forward.");
		integer(IN_CAP_MAX, "18. Alerts: Max Alerts per Window", 30, 5, 200);
		integer(IN_CAP_WINDOW, "18. Alerts: Window (minutes)", 60, 5, 1440);
		choice(IN_ALERT_MODE, "18. Alerts: Level Alert Mode", "Cross;Zone Entry;Both", 0,
			"Choose crosses, entries into a price band, or both. This applies to enabled level-cross alert categories. Touch, inventory and 80% rule "
			"alerts keep their own behavior.");
		integer(IN_ALERT_ZONE_TICKS, "18. Alerts: Structure Alert Zone Half-Width (ticks)", 4, 1, 1000,
			"Half-width for structural level alert bands in actual instrument ticks. Pasted/file daily levels use their own configured ATR/tick zone "
			"width.");
		sc.Input[IN_ALERT_SOUND].Name = "18. Alerts: Alert Sound";
		sc.Input[IN_ALERT_SOUND].SetAlertSoundNumber(2);	// Alert Sound 1
		sc.Input[IN_ALERT_SOUND].SetDescription("No Alert = no Sierra Chart alerts (Discord follows its own switch); No Sound = Alerts Log only.");
		// 19. Discord (Stage 4)
		yesNo(IN_DISCORD_ENABLE, "19. Discord: Send Chart Alerts to Discord", 0,
			"Optional. Sends enabled live chart alerts to the Discord channel below. Leave off for Sierra Chart-only alerts. Does not import levels. "
			"Historical loading and Replay are excluded.");
		text(IN_DISCORD_URL, "19. Discord: Discord Webhook URL", "",
			"In Discord: Server Settings > Integrations > Create Webhook. Choose the receiving channel and copy its Webhook URL here. A server invite "
			"or channel link will not work. Configure mobile notifications in Discord. Sierra Chart saves this URL in the chartbook in plain text: "
			"don't share a chartbook that holds it, and recreate the webhook if it leaks.");
	}

	// Sierra Chart's Session Times in CT hold both 03:00 and 12:00 (the full Globex session).
	bool SessionTimesCoverGlobex(SCStudyInterfaceRef sc)
	{
		const int date = sc.ArraySize > 0 ? sc.BaseDateTimeIn[sc.ArraySize - 1].GetDate() : sc.CurrentSystemDateTime.GetDate();
		auto ct = [&sc, date](int clock)
		{
			const SCDateTime t(date, clock);
			return sc.ConvertDateTimeFromChartTimeZone(t, TIMEZONE_CHICAGO).GetTimeInSeconds();
		};
		int starts[2] = {ct(sc.StartTime1), ct(sc.StartTime2)}, ends[2] = {ct(sc.EndTime1), ct(sc.EndTime2)};
		return CoversGlobex(starts, ends, sc.UseSecondStartEndTimes ? 2 : 1);
	}
}

SCSFExport scsf_TatankaAmtToolkit(SCStudyInterfaceRef sc)
{
	if (sc.SetDefaults)
	{
		SetDefaults(sc);
		return;
	}

	if (sc.LastCallToFunction)
	{
		// The study is removed (or the chart closed): the levels editor closes (its edits are dropped), the
		// two menu items, the ranges, the Discord queue and the heap state go. The hidden charts stay:
		// other charts and studies of the symbol read them.
		PollEditor(sc, PP_EDITOR, IN_LEVELS_TEXT, true);
		int& editMenuId		= sc.GetPersistentInt(PI_EDIT_MENU_ID);
		int& pasteMenuId	= sc.GetPersistentInt(PI_PASTE_MENU_ID);
		if (editMenuId > 0)
			sc.RemoveACSChartShortcutMenuItem(sc.ChartNumber, editMenuId);
		if (pasteMenuId > 0)
			sc.RemoveACSChartShortcutMenuItem(sc.ChartNumber, pasteMenuId);
		editMenuId	= 0;
		pasteMenuId	= 0;
		if (StudyState* state = PeekState(sc))
			DeleteRanges(sc, *state);
		DeleteState(sc);
		return;
	}

	// Set on every call, after SetDefaults, so it survives a DLL reload.
	sc.p_GDIFunction = DrawAmtToolkit;

	// The levels menu items, their events and the editor (spec C.1 step 4), before the inputs are read, so
	// text saved or pasted now is read in this call.
	LevelsMenu(sc);

	StudyState& state = GetState(sc);
	// The settings are read in place: the engine points at them, so a display edit applies at once.
	state.Core.Cfg = ReadSettings(sc);
	std::string warning;
	std::string error = ValidateSettings(state.Core.Cfg, warning);
	state.SettingsWarning = warning;
	if (error.empty())
	{
		n_ACSIL::s_BarPeriod period;
		sc.GetBarPeriodParameters(period);
		error = ChartError(period.ChartDataType, period.IntradayChartBarPeriodType, sc.SecondsPerBar);
	}
	if (error.empty() && !SessionTimesCoverGlobex(sc))
		error = TEXT_NOT_GLOBEX;
	// Sierra Chart only: NinjaTrader's instruments always have a tick size; a symbol without one
	// would leave the profiles without rows.
	if (error.empty() && !(DecimalTickSize(sc.TickSize) > 0))
		error = "The symbol's Tick Size is 0. Set it in Chart Settings >> Symbol.";
	// Logged once per error (NinjaTrader prints and logs its fault once, NT:1746).
	int& logged = sc.GetPersistentInt(PI_ERROR_LOGGED);
	const int errorKey = error.empty() ? 0 : (int)(Fnv1a(2166136261u, error.data(), error.size()) | 1u);
	if (errorKey != 0 && errorKey != logged)
		sc.AddMessageToLog(LogText(error).c_str(), 0);
	logged = errorKey;
	state.Error = error;
	// The Discord switch and URL (a change drops the old sender).
	UpdateDiscord(sc, state);

	if (!error.empty())
	{
		// Only the fault text is drawn. Once the cause is gone the engine is built again. Discord messages
		// already queued still go (NinjaTrader's sender runs on after a fault).
		state.Core.Reset();
		state.Built = false;
		DeleteRanges(sc, state);
		WriteTags(sc, state, true);
		PumpDiscord(sc, state);
		sc.UpdateAlways = EditorOpen(sc) || (state.Discord && state.Discord->Busy()) ? 1 : 0;
		return;
	}

	const int rebuilds = state.Rebuilds;
	ProcessCall(sc, state);
	WriteTags(sc, state, sc.IsFullRecalculation != 0 || state.Rebuilds != rebuilds || state.Waiting);
	UpdateRanges(sc, state);
	PumpDiscord(sc, state);
	// Sierra Chart calls again at the chart update interval while the data is not there yet, while the
	// editor is open (its saved text is picked up) and while Discord messages are queued or in flight.
	sc.UpdateAlways = state.Waiting || EditorOpen(sc) || (state.Discord && state.Discord->Busy()) ? 1 : 0;
}


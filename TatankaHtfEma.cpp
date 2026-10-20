// Copyright (c) 2026 Tatanka Trading LLC.
// This Source Code Form is subject to the Mozilla Public License, v. 2.0.
// If a copy of the MPL was not distributed with this file, obtain one at https://mozilla.org/MPL/2.0/.
// Tatanka 1hr 21 EMA (HTF EMA) v1.0.0 for Sierra Chart - tatankatrading.com

#include "sierrachart.h"

SCDLLName("Tatanka HTF EMA")

namespace
{
	enum HtfUnit
	{
		UNIT_SECONDS,
		UNIT_MINUTES,
		UNIT_DAYS,
		UNIT_WEEKS,
		UNIT_MONTHS
	};

	enum HtfEmaMode
	{
		MODE_LIVE_HTF,
		MODE_EXACT_HTF,
		MODE_SMOOTH_SCALED
	};

	// Same table as the NinjaTrader version's GetPeriodSeconds.
	double UnitSeconds(int unit)
	{
		switch (unit)
		{
			case UNIT_SECONDS:	return 1.0;
			case UNIT_MINUTES:	return 60.0;
			case UNIT_DAYS:		return 86400.0;
			case UNIT_WEEKS:	return 604800.0;
			case UNIT_MONTHS:	return 2592000.0;
		}
		return 0.0;
	}

	// Seconds per chart bar, or 0 when bars aren't time based (tick, volume, range, renko...).
	double ChartBarSeconds(SCStudyInterfaceRef sc)
	{
		n_ACSIL::s_BarPeriod barPeriod;
		sc.GetBarPeriodParameters(barPeriod);

		if (barPeriod.ChartDataType == INTRADAY_DATA)
			return barPeriod.IntradayChartBarPeriodType == IBPT_DAYS_MINS_SECS ? (double)sc.SecondsPerBar : 0.0;

		if (barPeriod.ChartDataType == DAILY_DATA)
		{
			switch (barPeriod.HistoricalChartBarPeriodType)
			{
				case HISTORICAL_CHART_PERIOD_DAYS:		return 86400.0 * (barPeriod.HistoricalChartDaysPerBar > 0 ? barPeriod.HistoricalChartDaysPerBar : 1);
				case HISTORICAL_CHART_PERIOD_WEEKLY:	return 604800.0;
				case HISTORICAL_CHART_PERIOD_MONTHLY:	return 2592000.0;
				case HISTORICAL_CHART_PERIOD_QUARTERLY:	return 3.0 * 2592000.0;
				case HISTORICAL_CHART_PERIOD_YEARLY:	return 31536000.0;
				default:								break;
			}
		}
		return 0.0;
	}

	// Which HTF unit a bar falls in. Seconds and minutes are buckets of `period`
	// units counted from the trading day's start, so on an ETH chart 60 minutes
	// lands on the hour and 240 minutes on the session open, like NinjaTrader and
	// TradingView bars. Days, weeks and months use the bar's trading day, so the
	// Sunday evening session counts as Monday.
	int64_t UnitKey(SCStudyInterfaceRef sc, const SCDateTime& barTime, int unit, int period)
	{
		if (unit == UNIT_SECONDS || unit == UNIT_MINUTES)
		{
			const int64_t bucketSeconds	= (int64_t)period * (unit == UNIT_MINUTES ? 60 : 1);
			const int64_t dayStart		= sc.GetTradingDayStartDateTimeOfBar(barTime).GetSecondsSinceBaseDate();
			int64_t elapsed				= barTime.GetSecondsSinceBaseDate() - dayStart;
			if (elapsed < 0)
				elapsed = 0;
			return dayStart + (elapsed / bucketSeconds) * bucketSeconds;
		}

		const int tradingDate = sc.GetTradingDayDate(barTime);
		if (unit == UNIT_DAYS)
			return tradingDate;

		const SCDateTime tradingDay(tradingDate, 0);
		if (unit == UNIT_WEEKS)
			return tradingDate - tradingDay.GetDayOfWeek();  // the week's Sunday

		return (int64_t)tradingDay.GetYear() * 12 + tradingDay.GetMonth();
	}

	// Subgraph arrays are float. EMA state is kept as a double split across two
	// arrays (value + rounding remainder) so long EMAs don't drift on NQ-size prices.
	double GetDouble(SCFloatArrayRef hi, SCFloatArrayRef lo, int index)
	{
		return (double)hi[index] + (double)lo[index];
	}

	void SetDouble(SCFloatArrayRef hi, SCFloatArrayRef lo, int index, double value)
	{
		const float rounded = (float)value;
		hi[index] = rounded;
		lo[index] = (float)(value - rounded);
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
		sc.StudyDescription	= "Tatanka HTF EMA v1.0.0: the 1-hour 21-period EMA (by default) on any chart timeframe. "
							  "Live HTF = the developing HTF EMA. Exact HTF = the EMA through the last closed HTF bar, stepping on the bar that closes it (as on TradingView). "
							  "Smooth Scaled = a chart-timeframe EMA with the length scaled to match. "
							  "Free and open source (MPL 2.0). tatankatrading.com";
		sc.GraphRegion		= 0;
		sc.ValueFormat		= VALUEFORMAT_INHERITED;
		sc.AutoLoop			= 0;

		Subgraph_HtfEma.Name			= "HTF EMA";
		Subgraph_HtfEma.DrawStyle		= DRAWSTYLE_LINE;
		Subgraph_HtfEma.PrimaryColor	= RGB(128, 128, 128);
		Subgraph_HtfEma.LineWidth		= 2;
		Subgraph_HtfEma.DrawZeros		= 0;

		Input_HtfUnit.Name = "Source Timeframe Unit";
		Input_HtfUnit.SetCustomInputStrings("Seconds;Minutes;Days;Weeks;Months");
		Input_HtfUnit.SetCustomInputIndex(UNIT_MINUTES);
		Input_HtfUnit.SetDescription("Pine input.timeframe type. Minutes + 60 = 1 hour.");

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
		Input_Mode.SetDescription("Live HTF = developing HTF EMA. Exact HTF = last closed HTF EMA. Smooth Scaled = chart-TF EMA with scaled length.");

		return;
	}

	const int unit		= Input_HtfUnit.GetIndex();
	const int period	= Input_HtfPeriod.GetInt();
	const int length	= Input_EmaLength.GetInt();
	const int mode		= Input_Mode.GetIndex();
	const double alpha	= 2.0 / (length + 1.0);

	// Smooth Scaled: EMA length x chart bars per HTF bar (21 x 12 = 252 on a 5 minute chart).
	// Bars that aren't time based keep the plain length, as on NinjaTrader.
	const double htfSeconds		= period * UnitSeconds(unit);
	const double chartSeconds	= ChartBarSeconds(sc);
	int scaledLength = length;
	if (htfSeconds > 0 && chartSeconds > 0)
	{
		scaledLength = (int)(length * (htfSeconds / chartSeconds) + 0.5);
		if (scaledLength < 1)
			scaledLength = 1;
	}
	const double smoothAlpha = 2.0 / (scaledLength + 1.0);

	// Seconds and minutes already bucket `period` units in UnitKey. Days, weeks and
	// months count `period` unit changes per HTF bar.
	const int unitsPerHtfBar = unit >= UNIT_DAYS ? period : 1;

	// For the live bar: a time-based bar whose end reaches its seconds/minutes bucket's
	// end is the bar that closes the HTF bar.
	const int64_t bucketSeconds	= unit == UNIT_SECONDS || unit == UNIT_MINUTES ? (int64_t)period * (unit == UNIT_MINUTES ? 60 : 1) : 0;
	const bool timeBasedBars	= chartSeconds > 0 && sc.SecondsPerBar > 0;

	// Per-bar state, so any bar can be recalculated from the bar before it
	// (the live bar is recalculated on every tick).
	SCFloatArrayRef ClosedEmaHi		= Subgraph_HtfEma.Arrays[0];  // EMA through the last closed HTF bar
	SCFloatArrayRef ClosedEmaLo		= Subgraph_HtfEma.Arrays[1];
	SCFloatArrayRef SmoothEmaHi		= Subgraph_HtfEma.Arrays[2];  // chart-timeframe EMA for Smooth Scaled
	SCFloatArrayRef SmoothEmaLo		= Subgraph_HtfEma.Arrays[3];
	SCFloatArrayRef ClosedHtfBars	= Subgraph_HtfEma.Arrays[4];  // closed HTF bars so far
	SCFloatArrayRef UnitsIntoHtfBar	= Subgraph_HtfEma.Arrays[5];  // day/week/month changes since the HTF bar opened

	const int startIndex = sc.UpdateStartIndex > 0 ? sc.UpdateStartIndex : 0;
	int64_t priorKey	= startIndex > 0 ? UnitKey(sc, sc.BaseDateTimeIn[startIndex - 1], unit, period) : 0;
	int64_t key			= startIndex < sc.ArraySize ? UnitKey(sc, sc.BaseDateTimeIn[startIndex], unit, period) : 0;

	for (int index = startIndex; index < sc.ArraySize; index++)
	{
		const double barClose	= sc.Close[index];
		const bool hasNext		= index + 1 < sc.ArraySize;
		const int64_t nextKey	= hasNext ? UnitKey(sc, sc.BaseDateTimeIn[index + 1], unit, period) : 0;

		if (index == 0)
		{
			SetDouble(ClosedEmaHi, ClosedEmaLo, index, 0.0);
			SetDouble(SmoothEmaHi, SmoothEmaLo, index, barClose);
			ClosedHtfBars[index]	= 0;
			UnitsIntoHtfBar[index]	= 0;
		}
		else
		{
			double closedEma	= GetDouble(ClosedEmaHi, ClosedEmaLo, index - 1);
			int closedBars		= (int)ClosedHtfBars[index - 1];
			int unitsInto		= (int)UnitsIntoHtfBar[index - 1];

			bool opensHtfBar = false;
			if (key != priorKey)
			{
				unitsInto++;
				if (unitsInto >= unitsPerHtfBar)
				{
					opensHtfBar	= true;
					unitsInto	= 0;
				}
			}

			// This bar opens a new HTF bar, so the prior bar's close was the HTF close.
			// The first HTF close seeds the EMA, as NinjaTrader's EMA does.
			if (opensHtfBar)
			{
				const double htfClose = sc.Close[index - 1];
				closedEma = closedBars == 0 ? htfClose : alpha * htfClose + (1.0 - alpha) * closedEma;
				closedBars++;
			}

			SetDouble(ClosedEmaHi, ClosedEmaLo, index, closedEma);
			SetDouble(SmoothEmaHi, SmoothEmaLo, index,
				smoothAlpha * barClose + (1.0 - smoothAlpha) * GetDouble(SmoothEmaHi, SmoothEmaLo, index - 1));
			ClosedHtfBars[index]	= (float)closedBars;
			UnitsIntoHtfBar[index]	= (float)unitsInto;
		}
		// Does this bar close its HTF bar? On history the next bar says so; on the live
		// bar, a time-based bar's end time does.
		bool closesHtfBar;
		if (hasNext)
			closesHtfBar = nextKey != key && (int)UnitsIntoHtfBar[index] + 1 >= unitsPerHtfBar;
		else
			closesHtfBar = timeBasedBars && bucketSeconds > 0
				&& sc.BaseDateTimeIn[index].GetSecondsSinceBaseDate() + sc.SecondsPerBar >= key + bucketSeconds;

		priorKey	= key;
		key			= nextKey;

		// Same plot rules as NinjaTrader: the HTF modes wait for `length` closed HTF
		// bars, Smooth Scaled for `scaledLength` chart bars. Zero isn't drawn.
		const int closedBars	= (int)ClosedHtfBars[index];
		const double closedEma	= GetDouble(ClosedEmaHi, ClosedEmaLo, index);
		const bool htfReady		= closedBars >= length;
		double value = 0.0;

		if (mode == MODE_EXACT_HTF)
		{
			// Like TradingView's request.security with lookahead off: the HTF EMA steps on
			// the chart bar that closes the HTF bar, where it equals the Live value, and
			// holds through the next HTF bar. (NinjaTrader's version steps one bar later.)
			if (closesHtfBar)
			{
				if (closedBars + 1 >= length)
					value = closedBars == 0 ? barClose : alpha * barClose + (1.0 - alpha) * closedEma;
			}
			else if (htfReady)
				value = closedEma;
		}
		else if (mode == MODE_SMOOTH_SCALED)
		{
			if (index >= scaledLength - 1)
				value = GetDouble(SmoothEmaHi, SmoothEmaLo, index);
		}
		else if (htfReady)
		{
			// The developing HTF EMA, with this bar's close as the forming HTF bar's close.
			// (TradingView's Live adds the current close twice on the HTF closing bar and on
			// realtime bars; this follows the formula its comments describe.)
			value = alpha * barClose + (1.0 - alpha) * closedEma;
		}

		Subgraph_HtfEma[index] = (float)value;
	}
}

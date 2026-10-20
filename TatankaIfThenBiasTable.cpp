// Copyright (c) 2026 Tatanka Trading LLC.
// This Source Code Form is subject to the Mozilla Public License, v. 2.0.
// If a copy of the MPL was not distributed with this file, obtain one at https://mozilla.org/MPL/2.0/.
// Tatanka If/Then Bias Table v1.0.0 for Sierra Chart - tatankatrading.com
// Sierra Chart port of the NinjaTrader 8 / Pine v6 "If/Then Bias Table".
//
// Sierra Chart's text inputs are single-line, so the rows are edited from the chart's
// right-click menu: "Tatanka If/Then: Edit Rows..." opens a multi-line editor like
// NinjaTrader's, and "Tatanka If/Then: Paste Rows from Clipboard" loads a copied block
// in one click.
//
// Lines, labels and the table are drawn in a drawing callback. The ATR zones are
// transparent Rectangle Highlight drawings, since the callback can't draw
// transparency; the other translucent colors are blended over the background.
// The daily ATR comes from a hidden daily chart, opened only when Position
// coloring or ATR zones are on.

#include "sierrachart.h"

#include <algorithm>
#include <cmath>
#include <limits>
#include <memory>
#include <string>
#include <vector>

SCDLLName("Tatanka If/Then")

namespace
{
	enum InputIndex
	{
		IN_INSTRUMENT_LABEL,
		IN_PRICE_SOURCE,
		IN_INPUT_DATA,
		IN_TABLE_POSITION,
		IN_TEXT_SIZE,
		IN_SHOW_LINES,
		IN_LINE_WIDTH,
		IN_LINE_STYLE,
		IN_LINE_COLOR_MODE,
		IN_ATR_LENGTH,
		IN_ATR_PERCENT,
		IN_SHOW_ZONES,
		IN_ZONE_PERCENT,
		IN_ZONE_TRANSPARENCY,
		IN_ABOVE_COLOR,
		IN_BELOW_COLOR,
		IN_WITHIN_COLOR,
		IN_LINE_LABELS,
		IN_LABEL_CONTENT,
		IN_WRAP_CHARACTERS,
		IN_LABEL_OFFSET,
		IN_LABEL_BACKGROUND,
		IN_SHOW_TABLE,
		IN_BACKGROUND_COLOR,
		IN_BACKGROUND_OPACITY,
		IN_ACTIVE_ROW_OPACITY,
		IN_BORDER_COLOR,
		IN_ROWS
	};

	enum PriceSource { PS_CLOSE, PS_OPEN, PS_HIGH, PS_LOW, PS_HL2, PS_HLC3, PS_OHLC4, PS_HLCC4, PS_INPUT_DATA };
	enum LineStyleOption { LS_SOLID, LS_DASHED, LS_DOTTED };
	enum LineColorMode { LCM_BIAS, LCM_POSITION };
	enum LabelContent { LC_TEXT, LC_PRICE, LC_PRICE_AND_TEXT };
	enum TextSize { TS_TINY, TS_SMALL, TS_NORMAL, TS_LARGE };

	// Persistent variable keys
	const int PD_PRICE				= 1;
	const int PD_ATR				= 2;
	const int PI_DAILY_CHART		= 1;
	const int PI_PASTE_MENU_ID		= 2;
	const int PI_ZONE_COUNT			= 3;
	const int PI_ZONE_SIGNATURE		= 4;
	const int PI_EDIT_MENU_ID		= 5;
	const int PI_ZONE_LINE_BASE		= 100;  // 100..199: zone drawing line numbers
	const int PP_EDITOR				= 1;

	const int MAX_LEVELS = 100;  // Pine garbage-collects the oldest shapes beyond max_*_count = 100

	const char* const EDIT_MENU_TEXT	= "Tatanka If/Then: Edit Rows...";
	const char* const PASTE_MENU_TEXT	= "Tatanka If/Then: Paste Rows from Clipboard";

	// Pine's color.gray, color.silver and color.white (NinjaTrader approximates the first two).
	const uint32_t PINE_GRAY	= RGB(120, 123, 134);
	const uint32_t PINE_SILVER	= RGB(178, 181, 190);
	const uint32_t PINE_WHITE	= RGB(255, 255, 255);

	// UTF-8 escapes keep these bytes the same whatever the compiler's source charset.
	#define TATANKA_ARROW	"\xE2\x86\x92"	// →
	#define TATANKA_EMDASH	"\xE2\x80\x94"	// —
	#define TATANKA_ENDASH	"\xE2\x80\x93"	// –
	#define TATANKA_POINTER	"\xE2\x96\xBA"	// ►

	const char* const DEFAULT_BLOCK =
		"U|5050|9999999|Accepts above 5050 " TATANKA_ARROW " continuation, next target 5085\n"
		"V|5005|5050|Above pivot, holding value " TATANKA_ARROW " grind higher\n"
		"P|4995|5005|Pivot ~5000 " TATANKA_EMDASH " the day's reference\n"
		"D|4960|4995|Below pivot, no reclaim " TATANKA_ARROW " 4960 support in play\n"
		"D|0|4960|Below 4960 " TATANKA_ARROW " range break, downside opens up";

	// ---- Logic (no Sierra Chart calls, so it can be unit tested) ----

	struct BiasRow
	{
		std::string	Bias;
		double		Low		= 0;
		double		High	= 0;
		std::string	Text;
	};

	bool IsFinite(double value)
	{
		return value == value && value != std::numeric_limits<double>::infinity() && value != -std::numeric_limits<double>::infinity();
	}

	std::string ReplaceAll(std::string text, const std::string& from, const std::string& to)
	{
		size_t pos = 0;
		while ((pos = text.find(from, pos)) != std::string::npos)
		{
			text.replace(pos, from.size(), to);
			pos += to.size();
		}
		return text;
	}

	std::vector<std::string> Split(const std::string& text, char separator)
	{
		std::vector<std::string> parts;
		size_t start = 0;
		for (;;)
		{
			const size_t pos = text.find(separator, start);
			if (pos == std::string::npos)
			{
				parts.push_back(text.substr(start));
				return parts;
			}
			parts.push_back(text.substr(start, pos - start));
			start = pos + 1;
		}
	}

	// Culture-invariant number, like .NET double.TryParse with NumberStyles.Float:
	// optional surrounding whitespace and sign, digits with an optional decimal point,
	// optional exponent. No thousands separators. Independent of the PC's locale.
	bool ParseNumber(const std::string& text, double& result)
	{
		size_t i = text.find_first_not_of(" \t\r\n\f\v");
		size_t end = text.find_last_not_of(" \t\r\n\f\v");
		if (i == std::string::npos)
			return false;
		end++;

		bool negative = false;
		if (text[i] == '+' || text[i] == '-')
			negative = text[i++] == '-';

		double mantissa = 0;
		int digits = 0, fractionDigits = 0;
		while (i < end && text[i] >= '0' && text[i] <= '9')
		{
			mantissa = mantissa * 10 + (text[i++] - '0');
			digits++;
		}
		if (i < end && text[i] == '.')
		{
			i++;
			while (i < end && text[i] >= '0' && text[i] <= '9')
			{
				mantissa = mantissa * 10 + (text[i++] - '0');
				digits++;
				fractionDigits++;
			}
		}
		if (digits == 0)
			return false;

		int exponent = 0;
		if (i < end && (text[i] == 'e' || text[i] == 'E'))
		{
			i++;
			bool negativeExponent = false;
			if (i < end && (text[i] == '+' || text[i] == '-'))
				negativeExponent = text[i++] == '-';
			int exponentDigits = 0;
			while (i < end && text[i] >= '0' && text[i] <= '9')
			{
				if (exponent < 10000)
					exponent = exponent * 10 + (text[i] - '0');
				i++;
				exponentDigits++;
			}
			if (exponentDigits == 0)
				return false;
			if (negativeExponent)
				exponent = -exponent;
		}
		if (i != end)
			return false;

		// Dividing by an exact power of ten keeps prices like 62.45 at the nearest double.
		const int scale = exponent - fractionDigits;
		double value = mantissa;
		if (scale < 0)
		{
			double divisor = 1;
			for (int k = 0; k < -scale && divisor < 1e308; k++)
				divisor *= 10;
			value /= divisor;
		}
		else
		{
			for (int k = 0; k < scale && value < 1e308; k++)
				value *= 10;
		}
		if (!(value <= 1e308))
			return false;

		result = negative ? -value : value;
		return true;
	}

	// NinjaTrader's Number(): spaces anywhere are ignored, the result must be finite.
	bool ParseLevel(const std::string& text, double& value)
	{
		return ParseNumber(ReplaceAll(text, " ", ""), value) && IsFinite(value);
	}

	// Length in UTF-16 code units, as .NET's string.Length counts it, so wrapping
	// matches NinjaTrader and TradingView for arrows, dashes and emoji.
	int TextLength(const std::string& text)
	{
		int length = 0;
		for (unsigned char c : text)
		{
			if ((c & 0xC0) != 0x80)
				length++;
			if (c >= 0xF0)
				length++;
		}
		return length;
	}

	// One row per line: BIAS|LO|HI|TEXT. Blank lines and lines starting with # are
	// skipped. Bias and text aren't trimmed and rows aren't sorted, as on NinjaTrader.
	std::vector<BiasRow> ParseRows(const std::string& block)
	{
		std::vector<BiasRow> rows;
		const std::string normalized = ReplaceAll(ReplaceAll(block, "\r\n", "\n"), "\r", "\n");
		for (const std::string& line : Split(normalized, '\n'))
		{
			if (line.empty() || line[0] == '#')
				continue;

			const std::vector<std::string> parts = Split(line, '|');
			BiasRow row;
			if (parts.size() < 4 || !ParseLevel(parts[1], row.Low) || !ParseLevel(parts[2], row.High))
				continue;

			// The first character, upper-cased; "N" when the bias is empty.
			const std::string& raw = parts[0];
			if (raw.empty())
				row.Bias = "N";
			else
			{
				size_t charLength = 1;
				const unsigned char lead = (unsigned char)raw[0];
				if (lead >= 0xF0) charLength = 4;
				else if (lead >= 0xE0) charLength = 3;
				else if (lead >= 0xC0) charLength = 2;
				row.Bias = raw.substr(0, (std::min)(charLength, raw.size()));
				if (row.Bias.size() == 1 && row.Bias[0] >= 'a' && row.Bias[0] <= 'z')
					row.Bias[0] = (char)(row.Bias[0] - 'a' + 'A');
			}

			std::string text = parts[3];
			for (size_t k = 4; k < parts.size(); k++)
				text += "|" + parts[k];
			row.Text = ReplaceAll(text, "\\n", "\n");

			rows.push_back(row);
		}
		return rows;
	}

	// The row whose LO..HI band is nearest the price (0 when price is inside it). First wins ties.
	int ActiveRow(const std::vector<BiasRow>& rows, double price)
	{
		int active = -1;
		double best = 1e18;
		for (int i = 0; i < (int)rows.size(); i++)
		{
			const double distance = price > rows[i].High ? price - rows[i].High
				: price < rows[i].Low ? rows[i].Low - price : 0;
			if (distance < best)
			{
				best = distance;
				active = i;
			}
		}
		return active;
	}

	// Pine's #.##: at most two decimals; prices are not rounded to tick size.
	// Rounds like .NET Framework's Math.Round(value, 2, MidpointRounding.AwayFromZero).
	std::string FormatPrice(double value)
	{
		if (!IsFinite(value))
			return "NaN";

		char buffer[64];
		if (std::fabs(value) >= 1e16)
		{
			snprintf(buffer, sizeof(buffer), "%.0f", value);
			return buffer;
		}

		double scaled = value * 100.0;
		const double whole = std::trunc(scaled);
		const double fraction = scaled - whole;
		scaled = whole;
		if (std::fabs(fraction) >= 0.5)
			scaled += fraction > 0 ? 1 : -1;

		if (scaled == 0)
			return "0";

		const bool negative = scaled < 0;
		const unsigned long long cents = (unsigned long long)std::fabs(scaled);
		const unsigned long long units = cents / 100;
		const unsigned int hundredths = (unsigned int)(cents % 100);

		if (hundredths == 0)
			snprintf(buffer, sizeof(buffer), "%s%llu", negative ? "-" : "", units);
		else if (hundredths % 10 == 0)
			snprintf(buffer, sizeof(buffer), "%s%llu.%u", negative ? "-" : "", units, hundredths / 10);
		else
			snprintf(buffer, sizeof(buffer), "%s%llu.%02u", negative ? "-" : "", units, hundredths);
		return buffer;
	}

	std::string RangeText(const BiasRow& row)
	{
		return row.High > 1000000 ? FormatPrice(row.Low) + "+"
			: row.Low <= 0 ? "<" + FormatPrice(row.High)
			: FormatPrice(row.Low) + TATANKA_ENDASH + FormatPrice(row.High);
	}

	// Word wrap at maxChars (0 = off), keeping literal \n breaks. Long words stay whole.
	// A line-for-line translation of the source, including its empty-line/space behavior.
	std::string Wrap(const std::string& text, int maxChars)
	{
		std::string output;
		for (const std::string& segment : Split(ReplaceAll(text, "\\n", "\n"), '\n'))
		{
			std::string segmentOutput;
			if (maxChars <= 0)
				segmentOutput = segment;
			else
			{
				std::string current;
				for (const std::string& word : Split(segment, ' '))
				{
					if (current.empty())
						current = word;
					else if (TextLength(current) + TextLength(word) + 1 <= maxChars)
						current += " " + word;
					else
					{
						segmentOutput += (segmentOutput.empty() ? "" : "\n") + current;
						current = word;
					}
				}
				segmentOutput += (segmentOutput.empty() ? "" : "\n") + current;
			}
			output += (output.empty() ? "" : "\n") + segmentOutput;
		}
		return output;
	}

	uint32_t BiasColor(const std::string& bias)
	{
		if (bias == "U") return RGB(99, 153, 34);
		if (bias == "V") return RGB(186, 117, 23);
		if (bias == "D") return RGB(168, 68, 64);
		if (bias == "P") return RGB(235, 208, 52);
		return RGB(136, 135, 128);
	}

	struct PositionColors
	{
		int			Mode		= LCM_BIAS;
		double		AtrPercent	= 10;
		uint32_t	Above		= 0;
		uint32_t	Below		= 0;
		uint32_t	Within		= 0;
	};

	uint32_t LevelColor(const BiasRow& row, double price, double atr, const PositionColors& p)
	{
		if (row.Bias == "P" || p.Mode == LCM_BIAS)
			return BiasColor(row.Bias);
		const double buffer = atr * p.AtrPercent / 100.0;
		// NaN comparisons are false, reproducing Pine's neutral fallback.
		return row.Low > price + buffer ? p.Above : row.Low < price - buffer ? p.Below : p.Within;
	}

	// Pine ta.atr = RMA(true range), seeded with an SMA after `length` days. Returns the
	// previous day's ATR: the value one daily bar before the last (developing) one.
	double PreviousDailyAtr(const std::vector<double>& high, const std::vector<double>& low, const std::vector<double>& close, int length)
	{
		length = (std::max)(1, length);
		const int count = (int)close.size();
		if (count < 2)
			return std::numeric_limits<double>::quiet_NaN();

		double sum = 0;
		double value = std::numeric_limits<double>::quiet_NaN();
		double previous = value;
		for (int i = 0; i < count; i++)
		{
			const double tr = i == 0 ? high[i] - low[i]
				: (std::max)(high[i] - low[i], (std::max)(std::fabs(high[i] - close[i - 1]), std::fabs(low[i] - close[i - 1])));
			sum += tr;
			previous = value;
			value = i < length - 1 ? std::numeric_limits<double>::quiet_NaN()
				: i == length - 1 ? sum / length
				: (1.0 / length) * tr + (1.0 - 1.0 / length) * value;
		}
		return previous;
	}

	// The rows that get a line, label and zone: positive LO, the last MAX_LEVELS of them.
	std::vector<int> LevelRows(const std::vector<BiasRow>& rows)
	{
		std::vector<int> levels;
		for (int i = 0; i < (int)rows.size(); i++)
			if (rows[i].Low > 0)
				levels.push_back(i);
		if ((int)levels.size() > MAX_LEVELS)
			levels.erase(levels.begin(), levels.end() - MAX_LEVELS);
		return levels;
	}

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

	// ---- Rendering ----

	// On/off run lengths in multiples of the line width, matching NinjaTrader's Direct2D
	// styles: Dash = 2 on, 2 off; Dot = round dots one line width across, one width apart.
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

	void DrawRectOutline(SCStudyInterfaceRef sc, int left, int top, int right, int bottom, int thickness, uint32_t color)
	{
		FillRect(sc, left, top, right, top + thickness, color);
		FillRect(sc, left, bottom - thickness, right, bottom, color);
		FillRect(sc, left, top, left + thickness, bottom, color);
		FillRect(sc, right - thickness, top, right, bottom, color);
	}

	// NinjaTrader lays everything out in DIPs (1/96 inch), so its paddings and line widths
	// grow on a scaled display. This is that scale: the window's DPI, or, when the window
	// reports 96 on a scaled display, how much bigger the selected font drew than
	// GetTextSizeWithFont measured it. Call after SetTextFont(font).
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

	struct TextBlock
	{
		std::vector<std::string>	Lines;
		std::vector<int>			LineWidths;
		int							Width	= 0;
		int							Height	= 0;
	};

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

	TextBlock MeasureText(SCStudyInterfaceRef sc, const n_ACSIL::s_GraphicsFont& font, int lineHeight, const std::string& text)
	{
		TextBlock block;
		block.Lines = Split(text, '\n');
		for (const std::string& line : block.Lines)
		{
			const int width = line.empty() ? 0 : MeasureLine(sc, font, line).Width;
			block.LineWidths.push_back(width);
			block.Width = (std::max)(block.Width, width);
		}
		block.Height = lineHeight * (int)block.Lines.size();
		return block;
	}

	enum Align { ALIGN_LEFT, ALIGN_CENTER, ALIGN_RIGHT };

	// Draws each line aligned between left and right, starting at top.
	void DrawTextBlock(SCStudyInterfaceRef sc, const TextBlock& block, int lineHeight, int left, int right, int top, Align align, uint32_t color)
	{
		sc.Graphics.SetTextColor(GraphicsColor(color));
		for (size_t i = 0; i < block.Lines.size(); i++)
		{
			if (block.Lines[i].empty())
				continue;
			const int width = block.LineWidths[i];
			const int x = align == ALIGN_LEFT ? left
				: align == ALIGN_RIGHT ? right - width
				: left + (right - left - width) / 2;
			sc.Graphics.DrawTextAt(SCString(block.Lines[i].c_str()), x, top + (int)i * lineHeight);
		}
	}

	PositionColors ReadPositionColors(SCStudyInterfaceRef sc)
	{
		PositionColors p;
		p.Mode			= sc.Input[IN_LINE_COLOR_MODE].GetIndex();
		p.AtrPercent	= sc.Input[IN_ATR_PERCENT].GetDouble();
		p.Above			= sc.Input[IN_ABOVE_COLOR].GetColor();
		p.Below			= sc.Input[IN_BELOW_COLOR].GetColor();
		p.Within		= sc.Input[IN_WITHIN_COLOR].GetColor();
		return p;
	}

	bool PendingEditorText(SCStudyInterfaceRef sc, int pointerKey, std::string& text);

	void DrawIfThen(HWND, HDC, SCStudyInterfaceRef sc)
	{
		if (sc.HideStudy || sc.ArraySize <= 0)
			return;

		const int panelLeft		= sc.StudyRegionLeftCoordinate;
		const int panelRight	= sc.StudyRegionRightCoordinate;
		const int panelTop		= sc.StudyRegionTopCoordinate;
		const int panelBottom	= sc.StudyRegionBottomCoordinate;
		if (panelRight <= panelLeft || panelBottom <= panelTop)
			return;

		std::string rowsBlock = sc.Input[IN_ROWS].GetString();
		PendingEditorText(sc, PP_EDITOR, rowsBlock);
		const std::vector<BiasRow> rows	= ParseRows(rowsBlock);
		const double price				= sc.GetPersistentDouble(PD_PRICE);
		const double atr				= sc.GetPersistentDouble(PD_ATR);
		const int active				= ActiveRow(rows, price);
		const int barIndex				= sc.ArraySize - 1;
		const PositionColors position	= ReadPositionColors(sc);

		uint32_t chartBackground = 0, unusedWidth = 0;
		SubgraphLineStyles unusedStyle = LINESTYLE_SOLID;
		sc.GetGraphicsSetting(sc.ChartNumber, n_ACSIL::GRAPHICS_SETTING_CHART_BACKGROUND, chartBackground, unusedWidth, unusedStyle);

		// The Pine and NinjaTrader background color carries its own opacity; Sierra Chart
		// colors have none, so it's a separate input, blended over the chart background.
		const uint32_t background = Blend(sc.Input[IN_BACKGROUND_COLOR].GetColor(),
			sc.Input[IN_BACKGROUND_OPACITY].GetInt() / 100.0, chartBackground);

		// NinjaTrader's Arial 10/12/14/20 DIPs are 7.5/9/10.5/15 points; Sierra Chart fonts
		// take whole points, so the half sizes round up.
		static const int FONT_POINTS[] = {8, 9, 11, 15};
		n_ACSIL::s_GraphicsFont font;
		font.m_FaceName	= "Arial";
		font.m_Height	= FONT_POINTS[(std::max)(0, (std::min)(3, (int)sc.Input[IN_TEXT_SIZE].GetIndex()))];
		font.m_Weight	= FW_NORMAL;

		n_ACSIL::s_GraphicsRectangle clip;
		clip.Left	= panelLeft;
		clip.Top	= panelTop;
		clip.Right	= panelRight;
		clip.Bottom	= panelBottom;
		sc.Graphics.SetClippingRegionFromRectangle(clip);
		sc.Graphics.SetTextFont(font);  // before any measuring: see MeasureLine
		sc.Graphics.SetBackgroundMode(TRANSPARENT);
		sc.Graphics.SetTextAlign(TA_NOUPDATECP | TA_LEFT | TA_TOP);

		const int lineHeight = (std::max)(1, (std::max)(MeasureLine(sc, font, "Ag").Height, (int)sc.Graphics.GetTextHeight()));

		// NinjaTrader's paddings are in DIPs (1/96 inch); scale them to this display.
		const double scale = DipScale(sc, font);
		auto dip = [scale](int dips) { return (std::max)(1, (int)(dips * scale + 0.5)); };

		const std::vector<int> levels = LevelRows(rows);

		if (sc.Input[IN_SHOW_LINES].GetYesNo())
		{
			const int width	= dip(sc.Input[IN_LINE_WIDTH].GetInt());  // NinjaTrader widths are DIPs too
			const int style	= sc.Input[IN_LINE_STYLE].GetIndex();
			for (int i : levels)
			{
				const int y = sc.RegionValueToYPixelCoordinate((float)rows[i].Low, sc.GraphRegion);
				if (y < panelTop || y > panelBottom)
					continue;
				const uint32_t color = LevelColor(rows[i], price, atr, position);
				DrawHorizontalLine(sc, panelLeft, panelRight, y, width, style,
					Blend(color, i == active ? 1.0 : 0.55, chartBackground));
			}
		}

		if (sc.Input[IN_LINE_LABELS].GetYesNo())
		{
			// Extrapolate from the visible bar spacing. Don't clamp the label to the
			// viewport: Pine permits future labels to be off-screen.
			const int index		= (std::max)(0, (std::min)(sc.IndexOfLastVisibleBar, barIndex));
			const int x			= sc.BarIndexToXPixelCoordinate(index);
			const int step		= index > 0 ? x - sc.BarIndexToXPixelCoordinate(index - 1) : (int)sc.ChartBarSpacing;
			const int anchor	= x + (barIndex - index + sc.Input[IN_LABEL_OFFSET].GetInt()) * (std::max)(1, step);
			const int content	= sc.Input[IN_LABEL_CONTENT].GetIndex();
			const int wrapChars	= sc.Input[IN_WRAP_CHARACTERS].GetInt();
			const bool plate	= sc.Input[IN_LABEL_BACKGROUND].GetYesNo() != 0;

			for (int i : levels)
			{
				const BiasRow& row = rows[i];
				const std::string text = content == LC_PRICE ? FormatPrice(row.Low)
					: (content == LC_PRICE_AND_TEXT ? FormatPrice(row.Low) + " - " : std::string()) + Wrap(row.Text, wrapChars);

				const TextBlock block	= MeasureText(sc, font, lineHeight, text);
				const int width			= (std::max)(1, block.Width);
				const int top			= sc.RegionValueToYPixelCoordinate((float)row.Low, sc.GraphRegion) - block.Height - dip(4);
				const int plateLeft		= anchor - width - dip(8);
				const int plateTop		= top - dip(2);
				const int plateRight	= anchor;
				const int plateBottom	= top + block.Height + dip(2);
				if (plateRight < panelLeft || plateLeft > panelRight || plateBottom < panelTop || plateTop > panelBottom)
					continue;

				if (plate)
					FillRect(sc, plateLeft, plateTop, plateRight, plateBottom, background);

				const uint32_t color = LevelColor(row, price, atr, position);
				DrawTextBlock(sc, block, lineHeight, anchor - width - dip(4), anchor - dip(4), top, ALIGN_RIGHT,
					Blend(color, i == active ? 1.0 : 0.70, plate ? background : chartBackground));
			}
		}

		if (sc.Input[IN_SHOW_TABLE].GetYesNo())
		{
			const int count = (int)rows.size() + 1;
			std::vector<TextBlock> cells((size_t)count * 3);
			int widths[3] = {0, 0, 0};
			std::vector<int> heights((size_t)count, 0);
			const std::string header = std::string(sc.Input[IN_INSTRUMENT_LABEL].GetString()) + "  if / then";

			for (int r = 0; r < count; r++)
			{
				const std::string text[3] =
				{
					r == 0 ? std::string() : (r - 1 == active ? std::string(TATANKA_POINTER) : std::string()),
					r == 0 ? FormatPrice(price) : RangeText(rows[(size_t)r - 1]),
					r == 0 ? header : rows[(size_t)r - 1].Text
				};
				for (int c = 0; c < 3; c++)
				{
					TextBlock& cell = cells[(size_t)r * 3 + c];
					cell = MeasureText(sc, font, lineHeight, text[c]);
					widths[c] = (std::max)(widths[c], cell.Width + dip(16));
					heights[(size_t)r] = (std::max)(heights[(size_t)r], cell.Height + dip(8));
				}
			}

			int totalWidth = widths[0] + widths[1] + widths[2], totalHeight = 0;
			for (int h : heights)
				totalHeight += h;

			const int positionIndex	= sc.Input[IN_TABLE_POSITION].GetIndex();  // Top/Middle/Bottom Right, then Left
			const bool onRight		= positionIndex < 3;
			const int vertical		= positionIndex % 3;
			const int left			= onRight ? panelRight - totalWidth : panelLeft;
			const int top			= vertical == 0 ? panelTop
				: vertical == 2 ? panelBottom - totalHeight
				: panelTop + (panelBottom - panelTop - totalHeight) / 2;

			const uint32_t border		= sc.Input[IN_BORDER_COLOR].GetColor();
			const double activeOpacity	= sc.Input[IN_ACTIVE_ROW_OPACITY].GetInt() / 100.0;

			int cellY = top;
			for (int r = 0; r < count; r++)
			{
				const bool isActive	= r > 0 && r - 1 == active;
				const uint32_t bias	= r == 0 ? (active >= 0 ? BiasColor(rows[(size_t)active].Bias) : PINE_GRAY)
					: BiasColor(rows[(size_t)r - 1].Bias);
				const uint32_t rowBackground = isActive ? Blend(bias, activeOpacity, chartBackground) : background;

				int cellX = left;
				for (int c = 0; c < 3; c++)
				{
					const uint32_t fill = r == 0 && c == 1 ? bias : rowBackground;
					FillRect(sc, cellX, cellY, cellX + widths[c], cellY + heights[(size_t)r], fill);

					const Align align = c == 0 || (r == 0 && c == 1) ? ALIGN_CENTER : c == 1 ? ALIGN_RIGHT : ALIGN_LEFT;
					const uint32_t foreground = r == 0 ? PINE_WHITE : c < 2 ? bias
						: isActive ? PINE_WHITE : Blend(PINE_SILVER, 0.70, fill);
					const TextBlock& cell = cells[(size_t)r * 3 + c];
					DrawTextBlock(sc, cell, lineHeight, cellX + dip(8), cellX + widths[c] - dip(8),
						cellY + (heights[(size_t)r] - cell.Height) / 2, align, foreground);
					cellX += widths[c];
				}
				cellY += heights[(size_t)r];
			}

			// One-DIP frame and shared cell edges.
			const int edge = dip(1);
			DrawRectOutline(sc, left, top, left + totalWidth, top + totalHeight, edge, border);
			int edgeX = left;
			for (int c = 0; c < 2; c++)
			{
				edgeX += widths[c];
				FillRect(sc, edgeX, top, edgeX + edge, top + totalHeight, border);
			}
			int edgeY = top;
			for (int r = 0; r < count - 1; r++)
			{
				edgeY += heights[(size_t)r];
				FillRect(sc, left, edgeY, left + totalWidth, edgeY + edge, border);
			}
		}

		sc.Graphics.ResetTextAlign();
		sc.Graphics.ResetBackgroundMode();
		sc.Graphics.ResetTextColor();
		sc.Graphics.ResetTextFont();
		sc.Graphics.ResetClippingRegion();
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

	// ---- Study function helpers ----

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

	// ---- Rows editor ----
	// NinjaTrader edits the rows in a multi-line editor; "Edit Rows..." opens the shared one.
	EditorTexts RowsEditorTexts()
	{
		EditorTexts t;
		t.ClassName		= L"TatankaIfThenRowsEditor";
		t.Title			= L"If/Then - Rows (BIAS|LO|HI|TEXT)";
		t.Intro			= L"Paste or type the afternoon review's if/then block below, one row per line, top band first:  BIAS|LO|HI|TEXT\r\n"
						  L"Click OK to update the chart. Cancel discards your edits.";
		t.Help			= L"BIAS:  U = up (green)   V = value (amber)   N = neutral (gray)   D = down (red)   P = pivot (yellow)\r\n"
						  L"LO / HI:  the band's bottom and top.  9999999 = open top (\"above X\").  0 = open bottom (\"below X\").\r\n"
						  L"TEXT:  the plan for that band. Type \\n (backslash, n) to start a new line in the label and table.\r\n"
						  L"Don't put | inside the text. A line starting with # is a comment.\r\n\r\n"
						  L"Example:  U|5050|9999999|Accepts above 5050 \x2192 continuation, next target 5085";
		t.OkButton		= L"OK";
		t.SavedMessage	= "Tatanka If/Then: rows saved from the editor.";
		t.OpenFailed	= "Tatanka If/Then: couldn't open the rows editor.";
		t.IntroHeight	= 40;
		t.HelpHeight	= 112;
		t.WordWrap		= false;
		t.Monospace		= true;
		return t;
	}

	double ReadPrice(SCStudyInterfaceRef sc)
	{
		const int i = sc.ArraySize - 1;
		if (i < 0)
			return std::numeric_limits<double>::quiet_NaN();

		const double open	= sc.BaseDataIn[SC_OPEN][i];
		const double high	= sc.BaseDataIn[SC_HIGH][i];
		const double low	= sc.BaseDataIn[SC_LOW][i];
		const double close	= sc.BaseDataIn[SC_LAST][i];
		switch (sc.Input[IN_PRICE_SOURCE].GetIndex())
		{
			case PS_OPEN:		return open;
			case PS_HIGH:		return high;
			case PS_LOW:		return low;
			case PS_HL2:		return (high + low) / 2.0;
			case PS_HLC3:		return (high + low + close) / 3.0;
			case PS_OHLC4:		return (open + high + low + close) / 4.0;
			case PS_HLCC4:		return (high + low + close + close) / 4.0;
			case PS_INPUT_DATA:	return sc.BaseDataIn[sc.Input[IN_INPUT_DATA].GetInputDataIndex()][i];
			default:			return close;
		}
	}

	// Previous daily ATR from a hidden daily chart of the same symbol, like
	// NinjaTrader's separate daily series: works on a chart loading only a few days.
	double DailyAtr(SCStudyInterfaceRef sc)
	{
		int& chartNumber = sc.GetPersistentInt(PI_DAILY_CHART);
		if (sc.IsFullRecalculation || chartNumber == 0)
		{
			s_ACSOpenChartParameters params;
			params.PriorChartNumber						= chartNumber;
			params.ChartDataType						= DAILY_DATA;
			params.Symbol								= sc.GetRealTimeSymbol();
			params.HistoricalChartBarPeriod				= HISTORICAL_CHART_PERIOD_DAYS;
			params.HistoricalChartBarPeriodLengthInDays	= 1;
			params.DaysToLoad							= 3000;  // about NinjaTrader's 2,048 daily bars
			params.ContinuousFuturesContractOption		= sc.ContinuousFuturesContractOption;
			params.HideNewChart							= 1;
			params.UpdatePriorChartNumberParametersToMatch = 1;
			chartNumber = sc.OpenChartOrGetChartReference(params);
		}
		if (chartNumber == 0)
			return std::numeric_limits<double>::quiet_NaN();

		SCGraphData daily;
		sc.GetChartBaseData(chartNumber, daily);
		const int count = daily[SC_LAST].GetArraySize();
		std::vector<double> high((size_t)count), low((size_t)count), close((size_t)count);
		for (int i = 0; i < count; i++)
		{
			high[(size_t)i]		= daily[SC_HIGH][i];
			low[(size_t)i]		= daily[SC_LOW][i];
			close[(size_t)i]	= daily[SC_LAST][i];
		}
		return PreviousDailyAtr(high, low, close, sc.Input[IN_ATR_LENGTH].GetInt());
	}

	uint32_t Fnv1a(uint32_t hash, const void* data, size_t size)
	{
		const unsigned char* bytes = (const unsigned char*)data;
		for (size_t i = 0; i < size; i++)
			hash = (hash ^ bytes[i]) * 16777619u;
		return hash;
	}

	void DeleteZones(SCStudyInterfaceRef sc, int fromIndex)
	{
		int& zoneCount = sc.GetPersistentInt(PI_ZONE_COUNT);
		for (int k = fromIndex; k < zoneCount; k++)
		{
			int& lineNumber = sc.GetPersistentInt(PI_ZONE_LINE_BASE + k);
			if (lineNumber != 0)
				sc.DeleteACSChartDrawing(sc.ChartNumber, TOOL_DELETE_CHARTDRAWING, lineNumber);
			lineNumber = 0;
		}
		zoneCount = (std::min)(zoneCount, fromIndex);
	}

	// ATR zones: a band on each side of every positive LO, as transparent Rectangle
	// Highlight drawings. Redrawn only when a zone's price, size, color or fill changes.
	void UpdateZones(SCStudyInterfaceRef sc, const std::vector<BiasRow>& rows, double price, double atr)
	{
		int& signature = sc.GetPersistentInt(PI_ZONE_SIGNATURE);

		const double band = IsFinite(atr) ? atr * sc.Input[IN_ZONE_PERCENT].GetDouble() / 100.0 : 0;
		if (sc.LastCallToFunction || sc.HideStudy || !sc.Input[IN_SHOW_ZONES].GetYesNo() || !(band > 0) || sc.ArraySize <= 0)
		{
			DeleteZones(sc, 0);
			signature = 0;
			return;
		}

		const PositionColors position	= ReadPositionColors(sc);
		const int active				= ActiveRow(rows, price);
		const int transparency			= (std::max)(0, (std::min)(100, sc.Input[IN_ZONE_TRANSPARENCY].GetInt()));
		const std::vector<int> levels	= LevelRows(rows);

		struct Zone { double Top, Bottom; uint32_t Color; int Transparency; };
		std::vector<Zone> zones;
		uint32_t hash = 2166136261u;
		for (int i : levels)
		{
			// Inactive rows are 8 points more transparent, as on NinjaTrader.
			Zone zone = {rows[(size_t)i].Low + band, rows[(size_t)i].Low - band,
				LevelColor(rows[(size_t)i], price, atr, position),
				i == active ? transparency : (std::min)(100, transparency + 8)};
			hash = Fnv1a(hash, &zone.Top, sizeof(zone.Top));
			hash = Fnv1a(hash, &zone.Bottom, sizeof(zone.Bottom));
			hash = Fnv1a(hash, &zone.Color, sizeof(zone.Color));
			hash = Fnv1a(hash, &zone.Transparency, sizeof(zone.Transparency));
			zones.push_back(zone);
		}

		int& zoneCount = sc.GetPersistentInt(PI_ZONE_COUNT);
		bool missing = false;
		for (int k = 0; k < zoneCount && !missing; k++)
		{
			const int lineNumber = sc.GetPersistentInt(PI_ZONE_LINE_BASE + k);
			missing = lineNumber == 0 || sc.ChartDrawingExists(sc.ChartNumber, lineNumber) == 0;
		}
		if (!sc.IsFullRecalculation && !missing && (int)hash == signature && zoneCount == (int)zones.size())
			return;

		for (int k = 0; k < (int)zones.size(); k++)
		{
			int& lineNumber = sc.GetPersistentInt(PI_ZONE_LINE_BASE + k);
			if (lineNumber != 0 && sc.ChartDrawingExists(sc.ChartNumber, lineNumber) == 0)
				lineNumber = 0;

			s_UseTool tool;
			tool.Clear();
			tool.ChartNumber				= sc.ChartNumber;
			tool.DrawingType				= DRAWING_RECTANGLEHIGHLIGHT;
			tool.AddMethod					= UTAM_ADD_OR_ADJUST;
			if (lineNumber != 0)
				tool.LineNumber				= lineNumber;
			tool.Region						= sc.GraphRegion;
			tool.BeginIndex					= 0;
			tool.EndIndex					= sc.ArraySize - 1;
			tool.BeginValue					= (float)zones[(size_t)k].Top;
			tool.EndValue					= (float)zones[(size_t)k].Bottom;
			tool.Color						= zones[(size_t)k].Color;
			tool.SecondaryColor				= zones[(size_t)k].Color;
			tool.LineWidth					= 0;
			tool.TransparencyLevel			= zones[(size_t)k].Transparency;
			tool.ExtendLeft					= 1;
			tool.ExtendRight				= 1;
			tool.DrawUnderneathMainGraph	= 0;  // over the bars, as NinjaTrader renders them
			tool.AddAsUserDrawnDrawing		= 0;
			if (sc.UseTool(tool) > 0)
				lineNumber = tool.LineNumber;
		}

		DeleteZones(sc, (int)zones.size());
		zoneCount	= (int)zones.size();
		signature	= (int)hash;
	}
}

SCSFExport scsf_TatankaIfThenBiasTable(SCStudyInterfaceRef sc)
{
	if (sc.SetDefaults)
	{
		sc.GraphName		= "Tatanka If/Then Bias Table";
		sc.StudyDescription	= "Tatanka If/Then Bias Table v1.0.0: the afternoon review's if/then bias for the zone price is in. "
							  "Right-click the chart and choose \"Tatanka If/Then: Edit Rows...\" to paste or edit the review's block, "
							  "or copy the block and choose \"Tatanka If/Then: Paste Rows from Clipboard\". "
							  "Free and open source (MPL 2.0). tatankatrading.com";
		sc.GraphRegion		= 0;
		sc.AutoLoop			= 0;
		sc.ValueFormat		= VALUEFORMAT_INHERITED;

		sc.Input[IN_INSTRUMENT_LABEL].Name = "Instrument Label";
		sc.Input[IN_INSTRUMENT_LABEL].SetString("ES");
		sc.Input[IN_INSTRUMENT_LABEL].SetDescription("Header instrument label; independent of the chart instrument.");

		sc.Input[IN_PRICE_SOURCE].Name = "Price Source";
		sc.Input[IN_PRICE_SOURCE].SetCustomInputStrings("Close;Open;High;Low;HL2;HLC3;OHLC4;HLCC4;Input Data");
		sc.Input[IN_PRICE_SOURCE].SetCustomInputIndex(PS_CLOSE);
		sc.Input[IN_PRICE_SOURCE].SetDescription("Close updates live each tick. Input Data uses the Input Data setting below, including another study when the study is Based On it.");

		sc.Input[IN_INPUT_DATA].Name = "Input Data (for Price Source = Input Data)";
		sc.Input[IN_INPUT_DATA].SetInputDataIndex(SC_LAST);

		sc.Input[IN_TABLE_POSITION].Name = "Table Position";
		sc.Input[IN_TABLE_POSITION].SetCustomInputStrings("Top Right;Middle Right;Bottom Right;Top Left;Middle Left;Bottom Left");
		sc.Input[IN_TABLE_POSITION].SetCustomInputIndex(1);
		sc.Input[IN_TABLE_POSITION].SetDescription("Anchor the table to one of six chart-region positions.");

		sc.Input[IN_TEXT_SIZE].Name = "Text Size";
		sc.Input[IN_TEXT_SIZE].SetCustomInputStrings("Tiny;Small;Normal;Large");
		sc.Input[IN_TEXT_SIZE].SetCustomInputIndex(TS_NORMAL);

		sc.Input[IN_SHOW_LINES].Name = "Plot Boundary Lines on Chart";
		sc.Input[IN_SHOW_LINES].SetYesNo(1);
		sc.Input[IN_SHOW_LINES].SetDescription("Draw a horizontal line at each positive Lo.");

		sc.Input[IN_LINE_WIDTH].Name = "Boundary Line Width";
		sc.Input[IN_LINE_WIDTH].SetInt(2);
		sc.Input[IN_LINE_WIDTH].SetIntLimits(1, 5);

		sc.Input[IN_LINE_STYLE].Name = "Boundary Line Style";
		sc.Input[IN_LINE_STYLE].SetCustomInputStrings("Solid;Dashed;Dotted");
		sc.Input[IN_LINE_STYLE].SetCustomInputIndex(LS_SOLID);

		sc.Input[IN_LINE_COLOR_MODE].Name = "Line/Label Color";
		sc.Input[IN_LINE_COLOR_MODE].SetCustomInputStrings("Bias;Position");
		sc.Input[IN_LINE_COLOR_MODE].SetCustomInputIndex(LCM_BIAS);
		sc.Input[IN_LINE_COLOR_MODE].SetDescription("Position: above price = resistance; below = support; within the ATR band = neutral. Pivot remains yellow.");

		sc.Input[IN_ATR_LENGTH].Name = "ATR Length (Position Band, Daily)";
		sc.Input[IN_ATR_LENGTH].SetInt(14);
		sc.Input[IN_ATR_LENGTH].SetIntLimits(1, 10000);
		sc.Input[IN_ATR_LENGTH].SetDescription("Daily Wilder ATR length. Uses the previous daily ATR, irrespective of chart timeframe.");

		sc.Input[IN_ATR_PERCENT].Name = "ATR Band Threshold (%)";
		sc.Input[IN_ATR_PERCENT].SetDouble(10);
		sc.Input[IN_ATR_PERCENT].SetDoubleLimits(0, 1e9);
		sc.Input[IN_ATR_PERCENT].SetDescription("Distance from price as a percentage of daily ATR that remains neutral.");

		sc.Input[IN_SHOW_ZONES].Name = "Plot ATR Zones Around Lines";
		sc.Input[IN_SHOW_ZONES].SetYesNo(0);
		sc.Input[IN_SHOW_ZONES].SetDescription("Band on each side of a positive Lo, sized by daily ATR.");

		sc.Input[IN_ZONE_PERCENT].Name = "Zone ATR % (Each Side)";
		sc.Input[IN_ZONE_PERCENT].SetDouble(2);
		sc.Input[IN_ZONE_PERCENT].SetDoubleLimits(0, 1e9);
		sc.Input[IN_ZONE_PERCENT].SetDescription("Zone half-width = daily ATR times this percentage.");

		sc.Input[IN_ZONE_TRANSPARENCY].Name = "Zone Fill Transparency";
		sc.Input[IN_ZONE_TRANSPARENCY].SetInt(75);
		sc.Input[IN_ZONE_TRANSPARENCY].SetIntLimits(0, 100);
		sc.Input[IN_ZONE_TRANSPARENCY].SetDescription("100 = invisible; 0 = solid. Inactive rows add 8. (NinjaTrader calls this Zone fill opacity.)");

		sc.Input[IN_ABOVE_COLOR].Name = "Position: Above Price (Resistance)";
		sc.Input[IN_ABOVE_COLOR].SetColor(RGB(242, 54, 69));

		sc.Input[IN_BELOW_COLOR].Name = "Position: Below Price (Support)";
		sc.Input[IN_BELOW_COLOR].SetColor(RGB(76, 175, 80));

		sc.Input[IN_WITHIN_COLOR].Name = "Position: Within ATR Band (Neutral)";
		sc.Input[IN_WITHIN_COLOR].SetColor(RGB(255, 235, 59));

		sc.Input[IN_LINE_LABELS].Name = "Label Boundary Lines";
		sc.Input[IN_LINE_LABELS].SetYesNo(1);
		sc.Input[IN_LINE_LABELS].SetDescription("Print right-aligned text above each positive Lo.");

		sc.Input[IN_LABEL_CONTENT].Name = "Line Label Content";
		sc.Input[IN_LABEL_CONTENT].SetCustomInputStrings("Text;Price;Price + Text");
		sc.Input[IN_LABEL_CONTENT].SetCustomInputIndex(LC_PRICE_AND_TEXT);

		sc.Input[IN_WRAP_CHARACTERS].Name = "Line Label Wrap Width (chars, 0 = off)";
		sc.Input[IN_WRAP_CHARACTERS].SetInt(50);
		sc.Input[IN_WRAP_CHARACTERS].SetIntLimits(0, 120);
		sc.Input[IN_WRAP_CHARACTERS].SetDescription("Wrap at word boundaries; preserve literal backslash-n manual breaks. Long words remain whole.");

		sc.Input[IN_LABEL_OFFSET].Name = "Line Label Offset (bars right of last candle)";
		sc.Input[IN_LABEL_OFFSET].SetInt(75);
		sc.Input[IN_LABEL_OFFSET].SetIntLimits(0, 500);
		sc.Input[IN_LABEL_OFFSET].SetDescription("Future bar offset, independent of horizontal scrolling. Increase the chart's right-side fill space to see future labels.");

		sc.Input[IN_LABEL_BACKGROUND].Name = "Label Background";
		sc.Input[IN_LABEL_BACKGROUND].SetYesNo(1);
		sc.Input[IN_LABEL_BACKGROUND].SetDescription("Use the table background color behind line labels.");

		sc.Input[IN_SHOW_TABLE].Name = "Show Table";
		sc.Input[IN_SHOW_TABLE].SetYesNo(0);
		sc.Input[IN_SHOW_TABLE].SetDescription("Show or hide the table independently of lines, labels and zones.");

		sc.Input[IN_BACKGROUND_COLOR].Name = "Table Background Color";
		sc.Input[IN_BACKGROUND_COLOR].SetColor(RGB(6, 6, 6));
		sc.Input[IN_BACKGROUND_COLOR].SetDescription("Base table cell color and the optional label plate color.");

		sc.Input[IN_BACKGROUND_OPACITY].Name = "Table Background Opacity %";
		sc.Input[IN_BACKGROUND_OPACITY].SetInt(100);
		sc.Input[IN_BACKGROUND_OPACITY].SetIntLimits(0, 100);
		sc.Input[IN_BACKGROUND_OPACITY].SetDescription("The background color's opacity (the opacity slider in the TradingView and NinjaTrader color pickers). 100 = solid.");

		sc.Input[IN_ACTIVE_ROW_OPACITY].Name = "Active-Row Opacity";
		sc.Input[IN_ACTIVE_ROW_OPACITY].SetInt(25);
		sc.Input[IN_ACTIVE_ROW_OPACITY].SetIntLimits(0, 100);
		sc.Input[IN_ACTIVE_ROW_OPACITY].SetDescription("Active row fill strength: 0 = transparent, 100 = solid.");

		sc.Input[IN_BORDER_COLOR].Name = "Table Border Color";
		sc.Input[IN_BORDER_COLOR].SetColor(RGB(6, 6, 6));

		sc.Input[IN_ROWS].Name = "Rows (BIAS|LO|HI|TEXT)";
		sc.Input[IN_ROWS].SetString(DEFAULT_BLOCK);
		sc.Input[IN_ROWS].SetDescription("One row per line. U/V/N/D/P. 9999999 = open-top display, 0 = open-bottom display. "
			"Literal backslash-n creates text breaks; # at column 1 is a comment. This box is single-line: edit the rows from the chart's "
			"right-click menu, Tatanka If/Then: Edit Rows... (or Paste Rows from Clipboard).");

		return;
	}

	int& editMenuId		= sc.GetPersistentInt(PI_EDIT_MENU_ID);
	int& pasteMenuId	= sc.GetPersistentInt(PI_PASTE_MENU_ID);

	if (sc.LastCallToFunction)
	{
		PollEditor(sc, PP_EDITOR, IN_ROWS, true);
		if (editMenuId > 0)
			sc.RemoveACSChartShortcutMenuItem(sc.ChartNumber, editMenuId);
		if (pasteMenuId > 0)
			sc.RemoveACSChartShortcutMenuItem(sc.ChartNumber, pasteMenuId);
		editMenuId	= 0;
		pasteMenuId	= 0;
		UpdateZones(sc, std::vector<BiasRow>(), 0, 0);
		return;
	}

	// Set on every call, after SetDefaults, so it survives a DLL reload.
	sc.p_GDIFunction = DrawIfThen;

	if (editMenuId <= 0)
		editMenuId = sc.AddACSChartShortcutMenuItem(sc.ChartNumber, EDIT_MENU_TEXT);
	if (pasteMenuId <= 0)
		pasteMenuId = sc.AddACSChartShortcutMenuItem(sc.ChartNumber, PASTE_MENU_TEXT);

	if (editMenuId > 0 && sc.MenuEventID == editMenuId)
		OpenEditor(sc, PP_EDITOR, RowsEditorTexts(), sc.Input[IN_ROWS].GetString());
	PollEditor(sc, PP_EDITOR, IN_ROWS, false);

	if (pasteMenuId > 0 && sc.MenuEventID == pasteMenuId)
	{
		std::string clipboard;
		if (ReadClipboardUtf8(clipboard) && !ParseRows(clipboard).empty())
		{
			sc.Input[IN_ROWS].SetString(clipboard.c_str());
			sc.AddMessageToLog("Tatanka If/Then: rows pasted from the clipboard.", 0);
		}
		else
			sc.AddMessageToLog("Tatanka If/Then: the clipboard has no BIAS|LO|HI|TEXT rows. Copy the if/then block first.", 1);
	}

	const bool needsAtr = sc.Input[IN_LINE_COLOR_MODE].GetIndex() == LCM_POSITION || sc.Input[IN_SHOW_ZONES].GetYesNo();
	const double price	= ReadPrice(sc);
	const double atr	= needsAtr ? DailyAtr(sc) : std::numeric_limits<double>::quiet_NaN();

	sc.GetPersistentDouble(PD_PRICE)	= price;
	sc.GetPersistentDouble(PD_ATR)		= atr;

	UpdateZones(sc, ParseRows(sc.Input[IN_ROWS].GetString()), price, atr);
}

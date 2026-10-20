// Copyright (c) 2026 Tatanka Trading LLC.
// This Source Code Form is subject to the Mozilla Public License, v. 2.0.
// If a copy of the MPL was not distributed with this file, obtain one at https://mozilla.org/MPL/2.0/.
// Tatanka Level Lines v1.0.0 for Sierra Chart - tatankatrading.com

// TatankaLevelLines
// Labeled horizontal levels for Sierra Chart:
//   1. A range box: top, bottom, optional midpoint and shading.
//   2. Any number of custom lines, separated by commas, semicolons, or new lines, typed in the
//      Levels input or in the large editor (chart right-click menu: Edit Levels...):
//        price|label|color|style|width
//      Only the price is required. Colors by name (Orange, Magenta, Gray) or hex (#FF00FF).
//      Styles: Solid, Dash, Dot, DashDot, DashDotDot.
// Labels sit on the right edge above each line, with the price appended, and stack
// instead of overlapping when two lines are close.
//
// Line colors, styles and widths are on the Subgraphs tab. Lines and labels are drawn
// in a drawing callback, so they never stretch the price scale. The range shading is
// a transparent Rectangle Highlight drawing, since the callback can't draw transparency.

#include "sierrachart.h"

#include <algorithm>
#include <cmath>
#include <memory>
#include <string>
#include <vector>

SCDLLName("Tatanka Level Lines")

namespace
{
	// Persistent variable keys
	const int PI_SHADE_LINE		= 1;
	const int PI_EDIT_MENU_ID	= 2;
	const int PP_EDITOR			= 1;

	const char* const EDIT_MENU_TEXT = "Tatanka Level Lines: Edit Levels...";

	enum SubgraphIndex
	{
		SG_RANGE_LINE,
		SG_RANGE_MID_LINE,
		SG_RANGE_SHADE,
		SG_DEFAULT_LINE
	};

	enum InputIndex
	{
		IN_RANGE_TOP,
		IN_RANGE_BOTTOM,
		IN_RANGE_TOP_LABEL,
		IN_RANGE_BOTTOM_LABEL,
		IN_SHOW_RANGE_MID,
		IN_RANGE_MID_LABEL,
		IN_FILL_RANGE,
		IN_RANGE_FILL_OPACITY,
		IN_CUSTOM_LEVELS,
		IN_LABEL_FONT_NAME,
		IN_LABEL_FONT_SIZE,
		IN_LABEL_FONT_BOLD,
		IN_SHOW_PRICE_IN_LABEL,
		IN_LABELS_ON_RIGHT,
		IN_LABEL_ABOVE_LINE,
		IN_LABEL_BACKGROUND
	};

	struct LineStroke
	{
		uint32_t	Color	= 0;
		int			Style	= LINESTYLE_SOLID;
		float		Width	= 1;
		bool		Visible	= true;  // false for Transparent or a zero-alpha hex color
	};

	struct LevelLine
	{
		double		Price = 0;
		std::string	Label;
		LineStroke	Stroke;
	};

	// ---- Parsing ----

	std::string Trim(const std::string& text)
	{
		const char* whitespace = " \t\r\n\f\v";
		const size_t first = text.find_first_not_of(whitespace);
		if (first == std::string::npos)
			return std::string();
		const size_t last = text.find_last_not_of(whitespace);
		return text.substr(first, last - first + 1);
	}

	std::string Lower(std::string text)
	{
		for (char& c : text)
			if (c >= 'A' && c <= 'Z')
				c = (char)(c - 'A' + 'a');
		return text;
	}

	// Culture-invariant number, like .NET double.TryParse with NumberStyles.Float:
	// optional sign, digits with an optional decimal point, optional exponent.
	// No thousands separators. Independent of the PC's locale.
	bool ParseNumber(const std::string& rawText, double& result)
	{
		const std::string text = Trim(rawText);
		size_t i = 0;
		bool negative = false;
		if (i < text.size() && (text[i] == '+' || text[i] == '-'))
			negative = text[i++] == '-';

		double mantissa = 0;
		int digits = 0;
		int fractionDigits = 0;
		while (i < text.size() && text[i] >= '0' && text[i] <= '9')
		{
			mantissa = mantissa * 10 + (text[i++] - '0');
			digits++;
		}
		if (i < text.size() && text[i] == '.')
		{
			i++;
			while (i < text.size() && text[i] >= '0' && text[i] <= '9')
			{
				mantissa = mantissa * 10 + (text[i++] - '0');
				digits++;
				fractionDigits++;
			}
		}
		if (digits == 0)
			return false;

		int exponent = 0;
		if (i < text.size() && (text[i] == 'e' || text[i] == 'E'))
		{
			i++;
			bool negativeExponent = false;
			if (i < text.size() && (text[i] == '+' || text[i] == '-'))
				negativeExponent = text[i++] == '-';
			int exponentDigits = 0;
			while (i < text.size() && text[i] >= '0' && text[i] <= '9')
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
		if (i != text.size())
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

	struct NamedColor
	{
		const char*	Name;
		uint32_t	Rgb;  // 0xRRGGBB
	};

	// The WPF named colors NinjaTrader accepts (System.Windows.Media.Colors), lowercase.
	const NamedColor NAMED_COLORS[] =
	{
		{"aliceblue", 0xF0F8FF}, {"antiquewhite", 0xFAEBD7}, {"aqua", 0x00FFFF}, {"aquamarine", 0x7FFFD4},
		{"azure", 0xF0FFFF}, {"beige", 0xF5F5DC}, {"bisque", 0xFFE4C4}, {"black", 0x000000},
		{"blanchedalmond", 0xFFEBCD}, {"blue", 0x0000FF}, {"blueviolet", 0x8A2BE2}, {"brown", 0xA52A2A},
		{"burlywood", 0xDEB887}, {"cadetblue", 0x5F9EA0}, {"chartreuse", 0x7FFF00}, {"chocolate", 0xD2691E},
		{"coral", 0xFF7F50}, {"cornflowerblue", 0x6495ED}, {"cornsilk", 0xFFF8DC}, {"crimson", 0xDC143C},
		{"cyan", 0x00FFFF}, {"darkblue", 0x00008B}, {"darkcyan", 0x008B8B}, {"darkgoldenrod", 0xB8860B},
		{"darkgray", 0xA9A9A9}, {"darkgreen", 0x006400}, {"darkkhaki", 0xBDB76B}, {"darkmagenta", 0x8B008B},
		{"darkolivegreen", 0x556B2F}, {"darkorange", 0xFF8C00}, {"darkorchid", 0x9932CC}, {"darkred", 0x8B0000},
		{"darksalmon", 0xE9967A}, {"darkseagreen", 0x8FBC8F}, {"darkslateblue", 0x483D8B}, {"darkslategray", 0x2F4F4F},
		{"darkturquoise", 0x00CED1}, {"darkviolet", 0x9400D3}, {"deeppink", 0xFF1493}, {"deepskyblue", 0x00BFFF},
		{"dimgray", 0x696969}, {"dodgerblue", 0x1E90FF}, {"firebrick", 0xB22222}, {"floralwhite", 0xFFFAF0},
		{"forestgreen", 0x228B22}, {"fuchsia", 0xFF00FF}, {"gainsboro", 0xDCDCDC}, {"ghostwhite", 0xF8F8FF},
		{"gold", 0xFFD700}, {"goldenrod", 0xDAA520}, {"gray", 0x808080}, {"green", 0x008000},
		{"greenyellow", 0xADFF2F}, {"honeydew", 0xF0FFF0}, {"hotpink", 0xFF69B4}, {"indianred", 0xCD5C5C},
		{"indigo", 0x4B0082}, {"ivory", 0xFFFFF0}, {"khaki", 0xF0E68C}, {"lavender", 0xE6E6FA},
		{"lavenderblush", 0xFFF0F5}, {"lawngreen", 0x7CFC00}, {"lemonchiffon", 0xFFFACD}, {"lightblue", 0xADD8E6},
		{"lightcoral", 0xF08080}, {"lightcyan", 0xE0FFFF}, {"lightgoldenrodyellow", 0xFAFAD2}, {"lightgray", 0xD3D3D3},
		{"lightgreen", 0x90EE90}, {"lightpink", 0xFFB6C1}, {"lightsalmon", 0xFFA07A}, {"lightseagreen", 0x20B2AA},
		{"lightskyblue", 0x87CEFA}, {"lightslategray", 0x778899}, {"lightsteelblue", 0xB0C4DE}, {"lightyellow", 0xFFFFE0},
		{"lime", 0x00FF00}, {"limegreen", 0x32CD32}, {"linen", 0xFAF0E6}, {"magenta", 0xFF00FF},
		{"maroon", 0x800000}, {"mediumaquamarine", 0x66CDAA}, {"mediumblue", 0x0000CD}, {"mediumorchid", 0xBA55D3},
		{"mediumpurple", 0x9370DB}, {"mediumseagreen", 0x3CB371}, {"mediumslateblue", 0x7B68EE}, {"mediumspringgreen", 0x00FA9A},
		{"mediumturquoise", 0x48D1CC}, {"mediumvioletred", 0xC71585}, {"midnightblue", 0x191970}, {"mintcream", 0xF5FFFA},
		{"mistyrose", 0xFFE4E1}, {"moccasin", 0xFFE4B5}, {"navajowhite", 0xFFDEAD}, {"navy", 0x000080},
		{"oldlace", 0xFDF5E6}, {"olive", 0x808000}, {"olivedrab", 0x6B8E23}, {"orange", 0xFFA500},
		{"orangered", 0xFF4500}, {"orchid", 0xDA70D6}, {"palegoldenrod", 0xEEE8AA}, {"palegreen", 0x98FB98},
		{"paleturquoise", 0xAFEEEE}, {"palevioletred", 0xDB7093}, {"papayawhip", 0xFFEFD5}, {"peachpuff", 0xFFDAB9},
		{"peru", 0xCD853F}, {"pink", 0xFFC0CB}, {"plum", 0xDDA0DD}, {"powderblue", 0xB0E0E6},
		{"purple", 0x800080}, {"red", 0xFF0000}, {"rosybrown", 0xBC8F8F}, {"royalblue", 0x4169E1},
		{"saddlebrown", 0x8B4513}, {"salmon", 0xFA8072}, {"sandybrown", 0xF4A460}, {"seagreen", 0x2E8B57},
		{"seashell", 0xFFF5EE}, {"sienna", 0xA0522D}, {"silver", 0xC0C0C0}, {"skyblue", 0x87CEEB},
		{"slateblue", 0x6A5ACD}, {"slategray", 0x708090}, {"snow", 0xFFFAFA}, {"springgreen", 0x00FF7F},
		{"steelblue", 0x4682B4}, {"tan", 0xD2B48C}, {"teal", 0x008080}, {"thistle", 0xD8BFD8},
		{"tomato", 0xFF6347}, {"turquoise", 0x40E0D0}, {"violet", 0xEE82EE}, {"wheat", 0xF5DEB3},
		{"white", 0xFFFFFF}, {"whitesmoke", 0xF5F5F5}, {"yellow", 0xFFFF00}, {"yellowgreen", 0x9ACD32}
	};

	uint32_t RgbToColorref(uint32_t rgb)
	{
		return RGB((rgb >> 16) & 0xFF, (rgb >> 8) & 0xFF, rgb & 0xFF);
	}

	int HexDigit(char c)
	{
		if (c >= '0' && c <= '9') return c - '0';
		if (c >= 'a' && c <= 'f') return c - 'a' + 10;
		if (c >= 'A' && c <= 'F') return c - 'A' + 10;
		return -1;
	}

	// A color name or hex (#RGB, #ARGB, #RRGGBB, #AARRGGBB), like WPF's ColorConverter.
	// Returns false for anything else, so the default line color is used.
	// Transparent and zero-alpha hex colors parse as invisible.
	bool ParseColor(const std::string& text, LineStroke& stroke)
	{
		if (text.empty())
			return false;

		if (text[0] == '#')
		{
			const size_t n = text.size() - 1;
			if (n != 3 && n != 4 && n != 6 && n != 8)
				return false;

			std::vector<int> nibbles;
			for (size_t i = 1; i < text.size(); i++)
			{
				const int d = HexDigit(text[i]);
				if (d < 0)
					return false;
				nibbles.push_back(d);
			}

			int a = 255, r, g, b;
			if (n == 3 || n == 4)
			{
				const size_t o = n == 4 ? 1 : 0;
				if (n == 4)
					a = nibbles[0] * 17;
				r = nibbles[o] * 17;
				g = nibbles[o + 1] * 17;
				b = nibbles[o + 2] * 17;
			}
			else
			{
				const size_t o = n == 8 ? 2 : 0;
				if (n == 8)
					a = nibbles[0] * 16 + nibbles[1];
				r = nibbles[o] * 16 + nibbles[o + 1];
				g = nibbles[o + 2] * 16 + nibbles[o + 3];
				b = nibbles[o + 4] * 16 + nibbles[o + 5];
			}
			stroke.Color	= RGB(r, g, b);
			stroke.Visible	= a > 0;
			return true;
		}

		const std::string name = Lower(text);
		if (name == "transparent")
		{
			stroke.Color	= 0;
			stroke.Visible	= false;
			return true;
		}
		for (const NamedColor& c : NAMED_COLORS)
		{
			if (name == c.Name)
			{
				stroke.Color	= RgbToColorref(c.Rgb);
				stroke.Visible	= true;
				return true;
			}
		}
		return false;
	}

	int ParseDash(const std::string& text, int fallback)
	{
		std::string key;
		for (char c : text)
			if (c != ' ')
				key += c;
		key = Lower(key);

		if (key == "solid")							return LINESTYLE_SOLID;
		if (key == "dash" || key == "dashed")		return LINESTYLE_DASH;
		if (key == "dot" || key == "dotted")		return LINESTYLE_DOT;
		if (key == "dashdot")						return LINESTYLE_DASHDOT;
		if (key == "dashdotdot")					return LINESTYLE_DASHDOTDOT;
		return fallback;
	}

	std::vector<std::string> Split(const std::string& text, const char* separators)
	{
		std::vector<std::string> parts;
		std::string current;
		for (char c : text)
		{
			if (strchr(separators, c) != nullptr && c != '\0')
			{
				parts.push_back(current);
				current.clear();
			}
			else
				current += c;
		}
		parts.push_back(current);
		return parts;
	}

	// The custom levels box, parsed the same way as the NinjaTrader version.
	std::vector<LevelLine> ParseCustomLevels(const std::string& customLevels, const LineStroke& defaultStroke)
	{
		std::vector<LevelLine> lines;
		if (Trim(customLevels).empty())
			return lines;

		for (const std::string& raw : Split(customLevels, ",;\n\r"))
		{
			if (raw.empty())
				continue;

			const std::vector<std::string> f = Split(raw, "|");
			double price;
			if (!ParseNumber(f[0], price) || price <= 0)
				continue;

			LevelLine line;
			line.Price			= price;
			line.Label			= f.size() > 1 ? Trim(f[1]) : std::string();
			line.Stroke			= defaultStroke;
			if (f.size() > 2)
				ParseColor(Trim(f[2]), line.Stroke);  // leaves the default color if it doesn't parse
			line.Stroke.Style	= f.size() > 3 ? ParseDash(Trim(f[3]), defaultStroke.Style) : defaultStroke.Style;

			double width;
			if (f.size() < 5 || !ParseNumber(f[4], width) || width <= 0)
				width = defaultStroke.Width;
			line.Stroke.Width	= (float)width;

			lines.push_back(line);
		}
		return lines;
	}
	// ---- Label layout ----

	struct PendingLabel
	{
		int			Y			= 0;  // the line's pixel row
		std::string	Text;
		uint32_t	Color		= 0;
		float		LineWidth	= 1;
		int			TextWidth	= 0;
		int			TextHeight	= 0;
		int			Top			= 0;  // filled in by StackLabels
	};

	// Top to bottom, so a label that would overlap the one above it gets pushed down instead.
	// gap is NinjaTrader's 1 DIP in pixels.
	void StackLabels(std::vector<PendingLabel>& labels, bool labelAboveLine, float gap = 1.0f)
	{
		std::stable_sort(labels.begin(), labels.end(),
			[](const PendingLabel& a, const PendingLabel& b) { return a.Y < b.Y; });

		float lastBottom = -1e9f;
		for (PendingLabel& l : labels)
		{
			float top = labelAboveLine
				? (float)(l.Y - l.TextHeight) - l.LineWidth / 2.0f - gap
				: (float)l.Y + l.LineWidth / 2.0f + gap;
			if (top < lastBottom + gap)
				top = lastBottom + gap;

			l.Top		= (int)(top + 0.5f);
			lastBottom	= (float)(l.Top + l.TextHeight);
		}
	}

	// On/off run lengths in multiples of the line width, matching NinjaTrader's Direct2D
	// styles: dashes 2 widths long with 2-width gaps, dots one width across and one apart.
	// Drawn as filled rectangles, so styled lines keep their width (GDI pens draw wide
	// dashed lines solid).
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

	// ---- Levels editor ----
	// NinjaTrader's "Open large levels editor": the same instructions and examples.
	EditorTexts LevelsEditorTexts()
	{
		EditorTexts t;
		t.ClassName		= L"TatankaLevelLinesEditor";
		t.Title			= L"Level Lines - Custom levels";
		t.Intro			= L"Enter or paste your levels below. Separate LEVELS with commas, semicolons, or new lines.\r\n"
						  L"Press Enter for a new line. Only the price is required.";
		t.Help			= L"Price only: 7845.75, 7830, 7810\r\n"
						  L"With labels: 7845.75|VAH, 7830|POC, 7810|VAL\r\n\r\n"
						  L"Within ONE level, use | (pipe) between fields: price|label|color|style|width\r\n"
						  L"Full example: 7845.75|VAH|Magenta|Dash|2\r\n"
						  L"Optional color, style, and width use the Default Custom Line subgraph when omitted.\r\n\r\n"
						  L"Use decimal points; no thousands commas. Do not use commas or semicolons inside labels.\r\n"
						  L"Click Save levels to update the chart.";
		t.OkButton		= L"Save levels";
		t.SavedMessage	= "Tatanka Level Lines: levels saved from the editor.";
		t.OpenFailed	= "Tatanka Level Lines: couldn't open the levels editor.";
		t.IntroHeight	= 40;
		t.HelpHeight	= 170;
		t.WordWrap		= true;
		t.Monospace		= false;
		return t;
	}

	// ---- Rendering ----

	LineStroke StrokeFromSubgraph(SCSubgraphRef subgraph)
	{
		LineStroke stroke;
		stroke.Color	= subgraph.PrimaryColor;
		stroke.Style	= subgraph.LineStyle;
		stroke.Width	= subgraph.LineWidth > 0 ? (float)subgraph.LineWidth : 1.0f;
		return stroke;
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

	// Text size in the drawing font. Call after sc.Graphics.SetTextFont(font): GetTextSize
	// measures the selected font in the chart window, which is what DrawTextAt draws with.
	// GetTextSizeWithFont alone can come back several times too small on a scaled
	// (high-DPI) display, so the larger of the two is used and a label box is never
	// smaller than its text.
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

	// NinjaTrader lays everything out in DIPs (1/96 inch), so its line widths and paddings
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

	SCString BuildLabelText(SCStudyInterfaceRef sc, const std::string& label, double price, bool showPrice)
	{
		const std::string text = Trim(label);
		if (!showPrice)
			return SCString(text.c_str());

		const SCString formatted = sc.FormatGraphValue(price, sc.BaseGraphValueFormat);
		if (text.empty())
			return formatted;

		SCString result(text.c_str());
		result += "  ";
		result += formatted;
		return result;
	}

	void DrawLevelLines(HWND, HDC, SCStudyInterfaceRef sc)
	{
		if (sc.HideStudy)
			return;

		const int x0		= sc.StudyRegionLeftCoordinate;
		const int x1		= sc.StudyRegionRightCoordinate;
		const int yTop		= sc.StudyRegionTopCoordinate;
		const int yBottom	= sc.StudyRegionBottomCoordinate;
		if (x1 <= x0 || yBottom <= yTop)
			return;

		const double rangeTop		= sc.Input[IN_RANGE_TOP].GetDouble();
		const double rangeBottom	= sc.Input[IN_RANGE_BOTTOM].GetDouble();
		const bool hasTop			= rangeTop > 0;
		const bool hasBottom		= rangeBottom > 0;
		const bool showPrice		= sc.Input[IN_SHOW_PRICE_IN_LABEL].GetYesNo() != 0;

		// Every line: range lines first, then the custom list.
		std::vector<LevelLine> items;
		if (hasTop)
			items.push_back({rangeTop, sc.Input[IN_RANGE_TOP_LABEL].GetString(), StrokeFromSubgraph(sc.Subgraph[SG_RANGE_LINE])});
		if (hasBottom)
			items.push_back({rangeBottom, sc.Input[IN_RANGE_BOTTOM_LABEL].GetString(), StrokeFromSubgraph(sc.Subgraph[SG_RANGE_LINE])});
		if (sc.Input[IN_SHOW_RANGE_MID].GetYesNo() && hasTop && hasBottom)
			items.push_back({(rangeTop + rangeBottom) / 2.0, sc.Input[IN_RANGE_MID_LABEL].GetString(), StrokeFromSubgraph(sc.Subgraph[SG_RANGE_MID_LINE])});

		std::string customLevels = sc.Input[IN_CUSTOM_LEVELS].GetString();
		PendingEditorText(sc, PP_EDITOR, customLevels);
		const std::vector<LevelLine> customLines = ParseCustomLevels(customLevels, StrokeFromSubgraph(sc.Subgraph[SG_DEFAULT_LINE]));
		items.insert(items.end(), customLines.begin(), customLines.end());

		n_ACSIL::s_GraphicsRectangle clip;
		clip.Left	= x0;
		clip.Top	= yTop;
		clip.Right	= x1;
		clip.Bottom	= yBottom;
		sc.Graphics.SetClippingRegionFromRectangle(clip);

		n_ACSIL::s_GraphicsFont font;
		font.m_FaceName	= sc.Input[IN_LABEL_FONT_NAME].GetString();
		font.m_Height	= sc.Input[IN_LABEL_FONT_SIZE].GetInt();
		font.m_Weight	= sc.Input[IN_LABEL_FONT_BOLD].GetYesNo() ? FW_BOLD : FW_NORMAL;
		sc.Graphics.SetTextFont(font);  // before any measuring: see MeasureLine
		sc.Graphics.SetBackgroundMode(TRANSPARENT);
		sc.Graphics.SetTextAlign(TA_NOUPDATECP | TA_LEFT | TA_TOP);

		// NinjaTrader's line widths and paddings are DIPs; scale them to this display.
		const double scale = DipScale(sc, font);

		// Draw the lines, queue the labels. Lines outside the visible price range are skipped.
		std::vector<PendingLabel> labels;
		for (const LevelLine& item : items)
		{
			if (!item.Stroke.Visible)
				continue;

			const int y = sc.RegionValueToYPixelCoordinate((float)item.Price, sc.GraphRegion);
			if (y < yTop || y > yBottom)
				continue;

			const float width = item.Stroke.Width * (float)scale;
			DrawHorizontalLine(sc, x0, x1, y, (int)(width + 0.5f), item.Stroke.Style, item.Stroke.Color);

			const SCString text = BuildLabelText(sc, item.Label, item.Price, showPrice);
			if (text.GetLength() > 0)
			{
				PendingLabel label;
				label.Y			= y;
				label.Text		= text.GetChars();
				label.Color		= item.Stroke.Color;
				label.LineWidth	= width;
				labels.push_back(label);
			}
		}

		if (!labels.empty())
		{
			for (PendingLabel& l : labels)
			{
				const n_ACSIL::s_GraphicsSize size = MeasureLine(sc, font, l.Text);
				l.TextWidth		= size.Width;
				l.TextHeight	= size.Height;
			}
			StackLabels(labels, sc.Input[IN_LABEL_ABOVE_LINE].GetYesNo() != 0, (float)scale);

			// NinjaTrader's label box is black at 60% opacity. The drawing callback has no
			// transparency, so blend that over the chart background instead.
			uint32_t background = 0, unusedWidth = 0;
			SubgraphLineStyles unusedStyle = LINESTYLE_SOLID;
			sc.GetGraphicsSetting(sc.ChartNumber, n_ACSIL::GRAPHICS_SETTING_CHART_BACKGROUND, background, unusedWidth, unusedStyle);
			const uint32_t boxColor = RGB(GetRValue(background) * 2 / 5, GetGValue(background) * 2 / 5, GetBValue(background) * 2 / 5);

			const bool labelsOnRight	= sc.Input[IN_LABELS_ON_RIGHT].GetYesNo() != 0;
			const bool labelBackground	= sc.Input[IN_LABEL_BACKGROUND].GetYesNo() != 0;
			const int pad				= (std::max)(1, (int)(4 * scale + 0.5));

			for (const PendingLabel& l : labels)
			{
				const int tx = labelsOnRight ? x1 - l.TextWidth - pad * 2 : x0 + pad;
				if (labelBackground)
					FillRect(sc, tx - pad, l.Top, tx + l.TextWidth + pad, l.Top + l.TextHeight, boxColor);

				sc.Graphics.SetTextColor(GraphicsColor(l.Color));
				sc.Graphics.DrawTextAt(SCString(l.Text.c_str()), tx, l.Top);
			}
		}

		sc.Graphics.ResetTextAlign();
		sc.Graphics.ResetBackgroundMode();
		sc.Graphics.ResetTextColor();
		sc.Graphics.ResetTextFont();
		sc.Graphics.ResetClippingRegion();
	}
	// The range shading: a Rectangle Highlight drawing extended both ways.
	void UpdateRangeShade(SCStudyInterfaceRef sc)
	{
		int& lineNumber = sc.GetPersistentInt(PI_SHADE_LINE);

		const double rangeTop		= sc.Input[IN_RANGE_TOP].GetDouble();
		const double rangeBottom	= sc.Input[IN_RANGE_BOTTOM].GetDouble();
		const bool wantShade		= !sc.LastCallToFunction && !sc.HideStudy && sc.ArraySize > 0
									  && sc.Input[IN_FILL_RANGE].GetYesNo() && rangeTop > 0 && rangeBottom > 0;

		if (lineNumber != 0 && sc.ChartDrawingExists(sc.ChartNumber, lineNumber) == 0)
			lineNumber = 0;

		if (!wantShade)
		{
			if (lineNumber != 0)
				sc.DeleteACSChartDrawing(sc.ChartNumber, TOOL_DELETE_CHARTDRAWING, lineNumber);
			lineNumber = 0;
			return;
		}

		// Inputs and subgraph colors only change through a full recalculation.
		if (lineNumber != 0 && !sc.IsFullRecalculation)
			return;

		const uint32_t shadeColor	= sc.Subgraph[SG_RANGE_SHADE].PrimaryColor;
		const int opacity			= (std::max)(0, (std::min)(100, sc.Input[IN_RANGE_FILL_OPACITY].GetInt()));

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
		tool.BeginValue					= (float)(std::max)(rangeTop, rangeBottom);
		tool.EndValue					= (float)(std::min)(rangeTop, rangeBottom);
		tool.Color						= shadeColor;  // outline, under the range lines
		tool.SecondaryColor				= shadeColor;
		tool.LineWidth					= 1;
		tool.TransparencyLevel			= 100 - opacity;
		tool.ExtendLeft					= 1;
		tool.ExtendRight				= 1;
		tool.DrawUnderneathMainGraph	= 0;  // over the bars, as NinjaTrader renders it
		tool.AddAsUserDrawnDrawing		= 0;

		if (sc.UseTool(tool) > 0)
			lineNumber = tool.LineNumber;
	}
}

SCSFExport scsf_TatankaLevelLines(SCStudyInterfaceRef sc)
{
	if (sc.SetDefaults)
	{
		sc.GraphName		= "Tatanka Level Lines";
		sc.StudyDescription	= "Tatanka Level Lines v1.0.0: labeled horizontal levels. A range box (top, bottom, midpoint, shading) "
							  "plus any number of custom lines typed as price|label|color|style|width (right-click the chart for Edit Levels...). "
							  "Line colors, styles and widths are on the Subgraphs tab. Free and open source (MPL 2.0). tatankatrading.com";
		sc.GraphRegion		= 0;
		sc.AutoLoop			= 0;
		sc.ValueFormat		= VALUEFORMAT_INHERITED;

		SCSubgraphRef rangeLine = sc.Subgraph[SG_RANGE_LINE];
		rangeLine.Name			= "Range Top/Bottom Line";
		rangeLine.DrawStyle		= DRAWSTYLE_IGNORE;
		rangeLine.PrimaryColor	= RGB(255, 165, 0);
		rangeLine.LineStyle		= LINESTYLE_SOLID;
		rangeLine.LineWidth		= 2;

		SCSubgraphRef midLine = sc.Subgraph[SG_RANGE_MID_LINE];
		midLine.Name			= "Range Midpoint Line";
		midLine.DrawStyle		= DRAWSTYLE_IGNORE;
		midLine.PrimaryColor	= RGB(255, 165, 0);
		midLine.LineStyle		= LINESTYLE_DASH;
		midLine.LineWidth		= 1;

		SCSubgraphRef shade = sc.Subgraph[SG_RANGE_SHADE];
		shade.Name				= "Range Shade";
		shade.DrawStyle			= DRAWSTYLE_IGNORE;
		shade.PrimaryColor		= RGB(255, 165, 0);

		SCSubgraphRef defaultLine = sc.Subgraph[SG_DEFAULT_LINE];
		defaultLine.Name			= "Default Custom Line";
		defaultLine.DrawStyle		= DRAWSTYLE_IGNORE;
		defaultLine.PrimaryColor	= RGB(255, 0, 255);
		defaultLine.LineStyle		= LINESTYLE_SOLID;
		defaultLine.LineWidth		= 2;

		sc.Input[IN_RANGE_TOP].Name = "Range Top (0 = off)";
		sc.Input[IN_RANGE_TOP].SetDouble(0);

		sc.Input[IN_RANGE_BOTTOM].Name = "Range Bottom (0 = off)";
		sc.Input[IN_RANGE_BOTTOM].SetDouble(0);

		sc.Input[IN_RANGE_TOP_LABEL].Name = "Top Label";
		sc.Input[IN_RANGE_TOP_LABEL].SetString("TOP OF RANGE");

		sc.Input[IN_RANGE_BOTTOM_LABEL].Name = "Bottom Label";
		sc.Input[IN_RANGE_BOTTOM_LABEL].SetString("BOTTOM OF RANGE");

		sc.Input[IN_SHOW_RANGE_MID].Name = "Show Midpoint";
		sc.Input[IN_SHOW_RANGE_MID].SetYesNo(1);

		sc.Input[IN_RANGE_MID_LABEL].Name = "Midpoint Label";
		sc.Input[IN_RANGE_MID_LABEL].SetString("RANGE MID");

		sc.Input[IN_FILL_RANGE].Name = "Shade the Range";
		sc.Input[IN_FILL_RANGE].SetYesNo(1);

		sc.Input[IN_RANGE_FILL_OPACITY].Name = "Shade Opacity %";
		sc.Input[IN_RANGE_FILL_OPACITY].SetInt(6);
		sc.Input[IN_RANGE_FILL_OPACITY].SetIntLimits(0, 100);

		sc.Input[IN_CUSTOM_LEVELS].Name = "Levels (comma / semicolon separated)";
		sc.Input[IN_CUSTOM_LEVELS].SetString("");
		sc.Input[IN_CUSTOM_LEVELS].SetDescription(
			"For a roomy editor, right-click the chart and choose Tatanka Level Lines: Edit Levels... "
			"Separate LEVELS with commas, semicolons, or new lines. Example (3 levels): 7845.75|VAH, 7830|POC, 7810|VAL. "
			"Within each level, use pipes: price|label|color|style|width. Only price is required; 7845.75, 7830, 7810 also works. "
			"Use decimal points and no thousands separators. Commas and semicolons are separators, so do not use them inside labels. "
			"Colors: names or hex (#FF00FF). Styles: Solid, Dash, Dot, DashDot, DashDotDot. "
			"Full example: 7845.75|VAH|Magenta|Dash|2. Omitted fields use the Default Custom Line subgraph.");

		sc.Input[IN_LABEL_FONT_NAME].Name = "Label Font";
		sc.Input[IN_LABEL_FONT_NAME].SetString("Arial");
		sc.Input[IN_LABEL_FONT_NAME].SetDescription("Font name, as on NinjaTrader (Arial by default).");

		sc.Input[IN_LABEL_FONT_SIZE].Name = "Label Font Size";
		sc.Input[IN_LABEL_FONT_SIZE].SetDescription("Points. NinjaTrader's default Arial 11 is about 8 points.");
		sc.Input[IN_LABEL_FONT_SIZE].SetInt(8);
		sc.Input[IN_LABEL_FONT_SIZE].SetIntLimits(4, 72);

		sc.Input[IN_LABEL_FONT_BOLD].Name = "Label Font Bold";
		sc.Input[IN_LABEL_FONT_BOLD].SetYesNo(0);

		sc.Input[IN_SHOW_PRICE_IN_LABEL].Name = "Show Price in Label";
		sc.Input[IN_SHOW_PRICE_IN_LABEL].SetYesNo(1);

		sc.Input[IN_LABELS_ON_RIGHT].Name = "Labels on Right Edge";
		sc.Input[IN_LABELS_ON_RIGHT].SetYesNo(1);

		sc.Input[IN_LABEL_ABOVE_LINE].Name = "Label Above Line";
		sc.Input[IN_LABEL_ABOVE_LINE].SetYesNo(1);

		sc.Input[IN_LABEL_BACKGROUND].Name = "Label Background";
		sc.Input[IN_LABEL_BACKGROUND].SetYesNo(1);

		return;
	}

	int& editMenuId = sc.GetPersistentInt(PI_EDIT_MENU_ID);

	if (sc.LastCallToFunction)
	{
		PollEditor(sc, PP_EDITOR, IN_CUSTOM_LEVELS, true);
		if (editMenuId > 0)
			sc.RemoveACSChartShortcutMenuItem(sc.ChartNumber, editMenuId);
		editMenuId = 0;
		UpdateRangeShade(sc);
		return;
	}

	// Set on every call, after SetDefaults, so it survives a DLL reload.
	sc.p_GDIFunction = DrawLevelLines;

	if (editMenuId <= 0)
		editMenuId = sc.AddACSChartShortcutMenuItem(sc.ChartNumber, EDIT_MENU_TEXT);
	if (editMenuId > 0 && sc.MenuEventID == editMenuId)
		OpenEditor(sc, PP_EDITOR, LevelsEditorTexts(), sc.Input[IN_CUSTOM_LEVELS].GetString());
	PollEditor(sc, PP_EDITOR, IN_CUSTOM_LEVELS, false);

	UpdateRangeShade(sc);
}

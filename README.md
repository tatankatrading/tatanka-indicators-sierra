<p align="center"><img src="assets/logo.png" width="96" alt="Tatanka Trading logo"></p>

# Tatanka Indicators for Sierra Chart (beta)

Sierra Chart versions of the nine free, open-source Auction Market Theory indicators from [Tatanka Trading](https://tatankatrading.com), built as ACSIL custom studies. The originals for NinjaTrader 8 and TradingView live in [tatanka-indicators](https://github.com/tatankatrading/tatanka-indicators).

> [!WARNING]
> **Beta: not yet verified in Sierra Chart.** These studies were ported line by line from the NinjaTrader versions and checked against NinjaTrader's own calculations, but they haven't been run in a live Sierra Chart setup yet. Expect rough edges, especially in see-through shading, the hidden 1-minute and daily charts, and text on high-DPI displays. The NinjaTrader and TradingView versions remain the reference. If something looks wrong, slow or different, please [report it](#report-a-bug).
>
> For education and chart analysis only: no buy or sell signals, not financial advice, no warranty (see the [license](LICENSE)). Futures trading carries substantial risk of loss.

## What's here

| Indicator | What it does | Source | Study name in Sierra Chart |
| --- | --- | --- | --- |
| **AMT Toolkit** | A complete Auction Market Theory read on one chart: volume profiles, prior day and month value, RTH VWAP, initial balance, overnight inventory, day type, the 80% Rule, naked POCs, single prints, poor highs/lows, a paste-your-own levels box, alerts and optional Discord alerts. | `TatankaAmtToolkit.cpp` | Tatanka AMT Toolkit |
| **TPO Profile** | TPO (Market Profile) letters for each 30-minute period, with the POC and value area. Full letter detail for recent days, outlines for older ones. | `TatankaTpoProfile.cpp` | Tatanka TPO Profile |
| **If/Then** | Shows the afternoon review's if/then bias for the zone price is in. Paste the review's block and it updates as price moves between zones. | `TatankaIfThenBiasTable.cpp` | Tatanka If/Then Bias Table |
| **1hr 21 EMA** | The 1-hour 21-period EMA on any chart timeframe. | `TatankaHtfEma.cpp` | Tatanka HTF EMA (1hr 21 EMA) |
| **Gap Analysis** | Each RTH opening gap versus the prior RTH close, shaded until price fills it, with a table and alerts. | `TatankaGapAnalysis.cpp` | Tatanka Gap Analysis |
| **Level Lines** | A range box plus any number of labeled lines, typed into one large box. | `TatankaLevelLines.cpp` | Tatanka Level Lines |
| **Session Volume Profile** | A volume profile for a custom session window (08:30-15:00 by default) built from tick data. | `TatankaSessionVolumeProfile.cpp` | Tatanka Session Volume Profile |
| **Periodic Volume Profile** | Daily, weekly, monthly or yearly volume profiles from 1-minute data, with POC/VAH/VAL lines that extend until price touches them. | `TatankaPeriodicVolumeProfile.cpp` | Tatanka Periodic Volume Profile |
| **Auto Anchored Volume Profile** | One developing volume profile from a calendar anchor (session, week, month, quarter, year, decade or century) to the latest bar. | `TatankaAutoAnchoredVolumeProfile.cpp` | Tatanka Auto Anchored Volume Profile |

The indicators work like the NinjaTrader versions, so their guides apply here too:

- [Tatanka AMT Toolkit User Guide (PDF)](https://github.com/tatankatrading/tatanka-indicators/blob/main/docs/Tatanka-AMT-Toolkit-User-Guide.pdf)
- [AMT Toolkit on NinjaTrader](https://github.com/tatankatrading/tatanka-indicators/blob/main/docs/NinjaTrader-Guide.md)
- [TPO Profile, If/Then, 1hr 21 EMA, Gap Analysis, Level Lines and the volume profiles](https://github.com/tatankatrading/tatanka-indicators/blob/main/docs/Other-Indicators-Guide.md)

What's different in Sierra Chart is listed under [Differences from NinjaTrader](#differences-from-ninjatrader).

## Install

1. Download the `.cpp` files (or the zip from [Releases](../../releases)) and copy them into the `ACS_Source` folder in your Sierra Chart folder (usually `C:\SierraChart\ACS_Source`).
2. In Sierra Chart: **Analysis → Build Custom Studies DLL → File → Select Files**, and pick one file.
3. **Build → Remote Build - Standard.** Sierra Chart compiles it on its server, so you don't need Visual Studio. Repeat for each file.
4. On a chart: **Analysis → Studies → Add Custom Study**, open the Tatanka DLL and add the study.

If a build fails, copy all the text in the **Output** area into a [bug report](#report-a-bug).

## Chart setup

- **AMT Toolkit:** a 1 to 30 minute chart, **Session Times** (Chart Settings) covering the full Globex session (17:00-16:00 CT for CME) and **Days to Load** of about 60. Turn alerts on for one chart per symbol, or each alert fires twice.
- **Session Volume Profile:** set **Intraday Data Storage Time Unit** to **1 Tick** (Global Settings → Data/Trade Service Settings) and download tick history.
- **Periodic and Auto Anchored Volume Profiles:** raise **Days to Load** to cover the period (about 400 days for a yearly profile). A 1-minute chart loads fastest.
- **TPO Profile:** for see-through boxes, set **Box Drawing** to Transparent and **Box Transparency (0-100)** to about 75 (TradingView's look).

**Hidden charts are normal.** The AMT Toolkit and the Periodic and Auto Anchored Volume Profiles open a hidden 1-minute chart of the same symbol. The AMT Toolkit, TPO Profile and If/Then open a hidden daily chart. They appear in the **Window** menu: leave them open. Charts of the same symbol share them.

## AMT Toolkit: your daily levels

**Load them** from the chart's right-click menu:

- **Tatanka AMT: Edit Levels...** opens a large editor. Paste your levels and click **Save**.
- **Tatanka AMT: Paste Levels from Clipboard** loads copied levels in one click.

**Formats it reads:**

- The one-line paste line: date, pivot, then any prices. Prices above the pivot are resistance (RES1 nearest), below it support (SUPP1 nearest).

  ```
  2026-10-05, 7745.25, 7758.25, 7772.00, 7786.50, 7801.25, 7818.00, 7730.25, 7718.25, 7707.25, 7690.50, 7672.75
  ```

- The block with `Pivot Level:`, `Resistance Levels:` and `Support Levels:` lines (plus optional `Date:` and `Symbol:` lines).
- A whole Discord levels message. Titles, code fences and bold markers are skipped.

**If something's off,** the notice at the bottom of the chart says why: for example a thousands separator (`7,745.25`), or another symbol's levels. **STALE LEVELS** means the levels' date is older than the chart's trading date.

**Levels file (optional).** Instead of pasting, set **2. Levels: Levels File** to a text file with the same text. The study re-reads it every 5 seconds while live, so replacing the file each morning updates the chart. `{root}` becomes the chart's root symbol, and micros read their parent (MES reads ES). Use a full path, for example:

```
%USERPROFILE%\Documents\Tatanka\levels\{root}.txt
```

The last good levels are cached, so a reload without the file keeps them.

## AMT Toolkit: Discord alerts (optional)

1. In **your own** Discord server: **Server Settings → Integrations → Webhooks → New Webhook**, pick the channel and **Copy Webhook URL**.
2. In the study, set **19. Discord: Send Chart Alerts to Discord** to Yes and paste the URL into **19. Discord: Discord Webhook URL**.
3. Turn on push notifications for that channel on your phone.

Good to know:

- Only live alerts are sent. Loading history, recalculating and Replay send nothing.
- Only `https://discord.com/api/webhooks/...` URLs are accepted, and messages can't ping @everyone, users or roles.
- Sierra Chart's own alerts work whether or not Discord does.

> [!CAUTION]
> **Keep the webhook URL private.** Anyone who has it can post to your channel. Sierra Chart saves study settings in the chartbook as plain text, so don't share a chartbook or study settings file that contains it. If it leaks, delete the webhook in Discord and make a new one.

## Report a bug

Please [open an issue](../../issues/new/choose) with the **Bug report** form. The most useful reports include:

- your Sierra Chart version (**Help → About**), Windows display scale (for example 150%), whether OpenGL is on (**Global Settings → Graphics Settings**) and your **Intraday Data Storage Time Unit**;
- which study, the symbol and bar period, and any settings you changed;
- screenshots (zoomed-in crops are best) and anything red in **Window → Message Log**;
- for a build failure, all the text in the build window's **Output** area.

**Never post a Discord webhook URL** in an issue or a screenshot.

## Differences from NinjaTrader

The studies calculate the same values as NinjaTrader. What changes is mostly where settings live and how Sierra Chart draws things.

**For every study:**

- **Multi-line text** (If/Then rows, Level Lines levels, AMT levels): Sierra Chart's text boxes are single-line, so right-click the chart for a large editor, or paste from the clipboard.
- **Colors, line widths and line styles** are on the study's **Subgraphs** tab.
- **See-through shading** uses Sierra Chart's own translucent drawings. Other see-through colors, such as label backgrounds and tables, are blended with the chart background.
- **Session times are Chicago time** with daylight saving, whatever your chart's time zone (unless the study has its own time-zone setting).
- **Font sizes are in points**, about three quarters of NinjaTrader's numbers.
- **Alerts** use Sierra Chart's alert sound list, fire only on live data, and fire once.
- **Include Columns With No Data:** empty columns are skipped, since NinjaTrader has no such bars.

Click a study for its details.

<details>
<summary><b>AMT Toolkit</b></summary>

**Settings.** Sierra Chart allows 128 settings and the NinjaTrader toolkit has 276, so:

- Settings carry NinjaTrader's group number in their names, for example **11. Profile: Value Area %**.
- Each line's color, width, style and label color are on the **Subgraphs** tab, one subgraph per line, named like NinjaTrader's line.
- **Draw Style = Hidden** turns a line off (NinjaTrader's Show switch).
- A subgraph's **Name** is its label text, so you can rename any label.
- A group's Show Labels switch is the **Off** choice in its Label Size.
- **Manual Tick Size** and the nPOC **Manual Bin Size** use 0 for Auto.
- Session windows keep NinjaTrader's `HHmm-HHmm` text, always Chicago time.

**Data.**

- 1-minute data comes from the chart itself on a 1-minute chart, otherwise from the hidden 1-minute chart.
- The daily ATR uses the hidden daily chart's whole history, like TradingView (NinjaTrader starts at the chart's first loaded day).
- A trading day starts at 17:00 CT, as in NinjaTrader, whatever the chart's Session Times.
- In a Single Chart replay the hidden 1-minute chart isn't replayed, so the forming bar's profile stops at the replay time. Replay All Charts in Chartbook, or use a 1-minute chart, for exact replays.

**Drawing.**

- Completed profiles, the 80% Rule fill, single prints and level zones are see-through. Completed-profile rows are rounded to whole bars, as TradingView draws them.
- The developing profile is solid, so if you move it over the bars (negative Profile Offset or left alignment) it hides them.
- **Dotted lines show as dots.** NinjaTrader's Dotted style draws nothing at all, so there a dotted level shows only its label and zone. Set that subgraph to Hidden for NinjaTrader's look.
- After the close and over the weekend, single prints end at the session's last bar, as in NinjaTrader.
- PIVOT, RES and SUPP levels each have their own subgraph. Renaming RES renames RES1, RES2 and so on.

**NinjaTrader bugs fixed here.**

- A right-side IB label stays at the end of its line after 15:15 (NinjaTrader's drifts away overnight).
- With **Extend IB Levels** set to Both, the IB labels follow the IB's own label setting (NinjaTrader groups them with the daily levels).
- On an early-close day, the short last bar doesn't count minutes twice.
- Reloading never repeats an alert that already fired.
- A Discord message shows the alert's time (NinjaTrader shows the bar's end, so a 09:31 alert said 09:35:00).

**Alerts and Discord.**

- Levels are checked once per chart update instead of every tick, so a cross that reverses within one update can be missed.
- Discord messages go through Sierra Chart's own web request, to the same webhook at its API v10 address. A failed message is never resent.
- Messages read `[symbol] alert | close price | time CT`.
- **Hide Study** draws nothing but keeps alerts running.
- Changing colors, labels, the dashboard or the profile's position applies at once, without recalculating.

</details>

<details>
<summary><b>TPO Profile</b></summary>

- **Session Start Time** and **Session End Time** are time inputs, in the **Timezone** setting's zone (Chicago by default; choose Chart Time Zone for NinjaTrader's behavior). Equal times mean a 24-hour session.
- **Auto Row Height** uses the daily ATR(10) from the hidden daily chart, so it works even with only a few days loaded. On an RTH-only chart, rows come out a little taller than NinjaTrader's.
- Each session keeps the row height it started with.
- **Box Transparency (0-100)** defaults to 0 (solid boxes) like NinjaTrader. **Box Drawing = Solid** is faster but hides the bars under a profile.
- Letters are Arial 8 pt and always drawn on top of the boxes.
- The developing profile includes the bar that's forming (NinjaTrader shows closed bars only).
- On an RTH-only chart the day's profile appears right after the close, not the next morning.
- Daily, weekly and monthly charts show a message instead of a profile.
- On tick, volume and range charts, if bar end times aren't loaded, the study asks for **Chart → Reload and Recalculate**.

</details>

<details>
<summary><b>Session Volume Profile</b></summary>

- Built from the chart's tick data: set **Intraday Data Storage Time Unit** to **1 Tick** and download tick history.
- The tick file is read in small pieces, newest session first, so the chart stays responsive ("reading tick data..." shows meanwhile).
- Sessions that can't be read as single trades (older 1-second history, older contracts on a continuous chart, back-adjusted prices) use Sierra Chart's volume at price instead. The chart label says how many ("not from ticks").
- **Volume data = Volume at price** loads fastest, with no tick reading. It matches the session window exactly only on bars that divide it (1, 5, 15 or 30 minutes for 08:30-15:00).
- **Session start** and **Session end** are time inputs. ExchangeTemplate means Chicago time.
- Multi-day bars show a message.
- POC, VAH and VAL are exact on every bar and show on the price scale and in the Chart Values window.
- The chart label uses the study's Short Name, so a Short Name you type is replaced.
- The POC color setting is named **POC line**, and the histogram box has its own opacity setting (0 = none).
- Changing colors or display settings doesn't re-read the tick data.

</details>

<details>
<summary><b>Periodic Volume Profile</b></summary>

- Built from 1-minute bars: the chart's own on a 1-minute chart, otherwise a hidden 1-minute chart that stays in the chartbook.
- Periods follow the trading date from the chart's Session Times. For CME, start the trading day at 17:00 CT so Sunday evening belongs to Monday.
- Raise **Days to Load** for longer periods. "waiting for 1-minute history" shows while minutes load.
- In a Single Chart replay the profile stops at the replay time. Replay All Charts in Chartbook for exact replays.
- **Volume data** can use Sierra Chart's volume at price instead (the chart reloads once).
- POC, VAH and VAL show on the last bar only, as in NinjaTrader.
- Lines extended until touched stop at the first bar whose range reaches them.
- The POC color setting is named **POC line**, the histogram box has its own opacity setting, and the chart label uses the study's Short Name.

</details>

<details>
<summary><b>Auto Anchored Volume Profile</b></summary>

- Same engine and 1-minute data as the Periodic Volume Profile.
- Raise **Days to Load** to reach back before the anchor (about 400 days for Year), as in NinjaTrader.
- On a 1 Day chart the hidden 1-minute chart loads only the days the anchor needs.
- Weekly, monthly and multi-day charts show a message.
- For CME, start the trading day at 17:00 CT so Sunday evening belongs to Monday.
- Volume at price works on intraday charts only.
- The POC color setting is named **POC line**, the histogram box has its own opacity setting, and the chart label uses the study's Short Name.

</details>

<details>
<summary><b>Gap Analysis</b></summary>

- **RTH start** and **RTH end** are time inputs (Chicago time).
- Fonts are 9 and 10 pt (NinjaTrader's 12 and 13).
- Alerts use Sierra Chart's alert sound list, or a WAV file named in **Alert sound file**.
- Zone shading is drawn under the price bars so the outlines, labels and table stay on top. The bars inside a zone aren't tinted.
- A zone starts at the opening bar's center (NinjaTrader's starts half a bar earlier).
- A gap exactly at the minimum size always counts.
- **Hide Study** keeps tracking gaps and sending alerts.

</details>

<details>
<summary><b>If/Then</b></summary>

- Load rows from the chart's right-click menu: **Tatanka If/Then: Edit Rows...** or **Paste Rows from Clipboard**.
- **Table Background Opacity %** is its own setting.
- NinjaTrader's Zone fill opacity is **Zone Fill Transparency** here (100 = invisible).
- Position coloring and ATR zones open a hidden daily chart for the daily ATR.

</details>

<details>
<summary><b>Level Lines</b></summary>

- Type levels in the **Levels (comma / semicolon separated)** setting, or right-click the chart and choose **Tatanka Level Lines: Edit Levels...** for the large editor.
- Line colors, styles and widths are on the **Subgraphs** tab.
- The range shading is a see-through Sierra Chart drawing. Label backgrounds are blended with the chart background.

</details>

<details>
<summary><b>1hr 21 EMA</b></summary>

- Builds the hourly bars from the chart's own bars, so no second chart is needed.
- Hours start at the trading day's start from the chart's Session Times, so on an ETH chart each hour lands on the hour.
- **Exact HTF** mode steps on the bar that closes each hour, as on TradingView (NinjaTrader steps one bar later).
- **Live HTF** mode uses closed hourly bars plus the current price.

</details>

## License

[Mozilla Public License 2.0](LICENSE), the same license as the NinjaTrader and TradingView versions.

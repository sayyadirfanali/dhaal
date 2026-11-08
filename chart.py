#!/usr/bin/env python3
"""
Dhaal – Cliff Chart

Plots take-home pay relative to someone earning exactly ₹12,00,000,
for taxable incomes from ₹11.9L to ₹12.9L (new regime, Tax Year 2026-27).
Below zero means: you kept less than someone on ₹12L.

Outputs cliff_chart.png (for LinkedIn / policy note) and cliff_chart.svg (for README).
"""

from fractions import Fraction

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.ticker as ticker
from matplotlib import font_manager
from matplotlib.lines import Line2D
from matplotlib.transforms import Bbox

def income_in(lo, hi, x):
    return max(Fraction(0), min(x, hi) - lo)

def income_above(lo, x):
    return max(Fraction(0), x - lo)

def tax_before_rebate(x):
    return (
        Fraction(5, 100)  * income_in(400_000, 800_000, x)
      + Fraction(10, 100) * income_in(800_000, 1_200_000, x)
      + Fraction(15, 100) * income_in(1_200_000, 1_600_000, x)
      + Fraction(20, 100) * income_in(1_600_000, 2_000_000, x)
      + Fraction(25, 100) * income_in(2_000_000, 2_400_000, x)
      + Fraction(30, 100) * income_above(2_400_000, x)
    )

def rebate(x):
    t = tax_before_rebate(x)
    if x <= 1_200_000:
        return min(t, Fraction(60_000))           # s.156(2)(a)
    elif t > x - 1_200_000:
        return t - (x - 1_200_000)                # s.156(2)(b)
    return Fraction(0)

def tax_after_rebate(x):
    return tax_before_rebate(x) - rebate(x)

def tax_with_cess(x):
    return Fraction(104, 100) * tax_after_rebate(x)


BASE  = 1_200_000
X_MIN = 1_190_000
X_MAX = 1_290_000

incomes = range(X_MIN, X_MAX + 1, 250)
xs = [i / 1e5 for i in incomes]                                   # in lakh
with_cess = [float(i - tax_with_cess(Fraction(i))) - BASE for i in incomes]
no_cess   = [float(i - tax_after_rebate(Fraction(i))) - BASE for i in incomes]

# Worst point and recovery point, searched exactly at ₹1 resolution
worst_inc = min(range(BASE, X_MAX), key=lambda i: i - tax_with_cess(Fraction(i)))
worst_gap = float(worst_inc - tax_with_cess(Fraction(worst_inc))) - BASE
recovery_inc = next(i for i in range(BASE + 1, X_MAX)
                    if i - tax_with_cess(Fraction(i)) >= BASE)


SURFACE   = "#fcfcfb"
INK       = "#1f1f1e"   # primary text
INK_2     = "#52514e"   # secondary text
INK_3     = "#8a8984"   # muted text (source line)
GRID      = "#e6e5e1"
ZERO      = "#b5b4ae"
ENACTED   = "#c2502e"   # muted brick: the law as enacted (with cess)
RELIEF    = "#3a6ea5"   # muted steel blue: rebate relief alone (no cess)
BAND      = "#c2502e"

# Use Inter if installed; fall back silently otherwise.
for f in font_manager.findSystemFonts():
    if "Inter" in f:
        font_manager.fontManager.addfont(f)
family = "Inter" if any(f.name == "Inter" for f in font_manager.fontManager.ttflist) else "DejaVu Sans"

plt.rcParams.update({
    "font.family": family,
    "font.size": 10.5,
    "text.color": INK,
    "axes.labelcolor": INK_2,
    "xtick.color": INK_2,
    "ytick.color": INK_2,
    "axes.edgecolor": GRID,
    "svg.fonttype": "path",   # embed glyphs so the SVG looks right without Inter installed
})

def inr(n):
    """Indian digit grouping: 1270588 -> 12,70,588."""
    n = int(round(n))
    sign = "-" if n < 0 else ""
    s = str(abs(n))
    if len(s) <= 3:
        return sign + s
    head, tail = s[:-3], s[-3:]
    groups = []
    while len(head) > 2:
        groups.insert(0, head[-2:])
        head = head[:-2]
    if head:
        groups.insert(0, head)
    return sign + ",".join(groups) + "," + tail

def rupees(v, _=None):
    if abs(v) < 0.5:
        return "₹0"
    sign = "−" if v < 0 else "+"
    return f"{sign}₹{inr(abs(v))}"


fig, ax = plt.subplots(figsize=(9, 5.6))
fig.patch.set_facecolor(SURFACE)
ax.set_facecolor(SURFACE)

# Band where earning more leaves you worse off
ax.axvspan(BASE / 1e5, recovery_inc / 1e5, color=BAND, alpha=0.06, lw=0, zorder=0)

# Zero line: "same take-home as at ₹12L"
ax.axhline(0, color=ZERO, lw=1, zorder=1)

# Series
ax.plot(xs, no_cess,   color=RELIEF,  lw=2,   zorder=2, solid_capstyle="round")
ax.plot(xs, with_cess, color=ENACTED, lw=2.4, zorder=3, solid_capstyle="round")

# Legend (top-left, where the chart is empty)
leg = ax.legend(
    handles=[
        Line2D([], [], color=ENACTED, lw=2.4, label="Law as enacted (with 4% cess)"),
        Line2D([], [], color=RELIEF,  lw=2,   label="Rebate relief alone (no cess)"),
    ],
    loc="lower left", bbox_to_anchor=(-0.01, 1.01), ncol=2, frameon=False,
    fontsize=9.5, handlelength=1.8, columnspacing=2.2, borderaxespad=0.3,
)
for t in leg.get_texts():
    t.set_color(INK)

# The threshold itself
ax.plot([BASE / 1e5], [0], marker="o", ms=6, color=INK_2, mec=SURFACE, mew=1.5, zorder=5)
ax.annotate("₹12,00,000\nzero tax", xy=(BASE / 1e5, 0), xytext=(-8, 8),
            textcoords="offset points", ha="right", va="bottom",
            fontsize=9, color=INK_2, linespacing=1.25)

# Worst point
ax.plot([worst_inc / 1e5], [worst_gap], marker="o", ms=7, color=ENACTED,
        mec=SURFACE, mew=1.8, zorder=5)
ax.annotate(
    f"₹{inr(abs(worst_gap))} worse off\nat ₹{inr(worst_inc)} taxable income",
    xy=(worst_inc / 1e5, worst_gap),
    xytext=(worst_inc / 1e5 - 0.04, worst_gap - 3_000),
    ha="right", va="center", fontsize=9.5, color=INK, linespacing=1.3,
    arrowprops=dict(arrowstyle="-", color=INK_3, lw=0.8, shrinkA=2, shrinkB=6),
)

# Band label
band_mid = (BASE + recovery_inc) / 2e5
ax.text(band_mid, 15_600, "Earning more, keeping less",
        ha="center", va="center", fontsize=9, color=ENACTED, fontweight="medium")
ax.text(band_mid, 14_000, f"₹12,00,001 – ₹{inr(recovery_inc - 1)}",
        ha="center", va="center", fontsize=8.5, color=INK_2)

# Axes
ax.set_xlim(X_MIN / 1e5, X_MAX / 1e5)
ax.set_ylim(-11_000, 17_500)
ax.xaxis.set_major_locator(ticker.MultipleLocator(0.1))
ax.xaxis.set_major_formatter(ticker.FuncFormatter(lambda v, _: f"₹{v:.1f}L"))
ax.yaxis.set_major_locator(ticker.MultipleLocator(5_000))
ax.yaxis.set_major_formatter(ticker.FuncFormatter(rupees))
ax.set_xlabel("Taxable income", labelpad=8)
ax.set_ylabel("Take-home pay vs. earning exactly ₹12L", labelpad=10)

ax.grid(axis="y", color=GRID, lw=0.8, zorder=0)
ax.tick_params(length=0, pad=6)
for side in ("top", "right", "left"):
    ax.spines[side].set_visible(False)
ax.spines["bottom"].set_color(GRID)

# Title, subtitle, source
fig.text(0.075, 0.955, f"Earn ₹{inr(worst_inc - BASE)} more, keep ₹{inr(abs(worst_gap))} less",
         fontsize=17, fontweight="semibold", color=INK, ha="left", va="top")
fig.text(0.075, 0.895,
         "India, new regime, Tax Year 2026-27. The rebate's marginal relief removes the cliff at ₹12 lakh;\n"
         "the 4% cess, charged on top, brings it back with a marginal rate of 104%.",
         fontsize=10, color=INK_2, ha="left", va="top", linespacing=1.4)
fig.text(0.075, 0.02,
         "Source: Income-tax Act 2025, ss. 156 & 202(1); Finance Act 2026, s. 2(6). "
         "Rounding and surcharge ignored. Cliff proved in Lean 4 (Dhaal).",
         fontsize=8, color=INK_3, ha="left", va="bottom")

fig.subplots_adjust(left=0.13, right=0.95, top=0.73, bottom=0.17)


MARGIN = 0.4                      # inches, on every side
W, H = fig.get_size_inches()
outer = Bbox.from_bounds(-MARGIN, -MARGIN, W + 2 * MARGIN, H + 2 * MARGIN)

fig.savefig("cliff_chart.svg", facecolor=SURFACE, bbox_inches=outer)
print(f"Saved cliff_chart.svg (font: {family})")

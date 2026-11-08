#!/usr/bin/env python3
"""
Dhaal – Validation Script
Computes personal income tax under India's new regime (Tax Year 2026-27)
using the same formulas as the Lean model, for comparison with the
official calculator at incometax.gov.in.

Sections referenced:
  - Income-tax Act 2025, s.202(1): slab rates
  - Income-tax Act 2025, s.156:    rebate and marginal relief
  - Finance Act 2026, s.2(6):      4% Health & Education Cess
"""

from fractions import Fraction
from typing import NamedTuple


def income_in(lo: Fraction, hi: Fraction, x: Fraction) -> Fraction:
    """Portion of income x falling in bracket [lo, hi]."""
    return max(Fraction(0), min(x, hi) - lo)


def income_above(lo: Fraction, x: Fraction) -> Fraction:
    """Portion of income x above threshold lo."""
    return max(Fraction(0), x - lo)


def tax_before_rebate(x: Fraction) -> Fraction:
    """Slab tax under s.202(1), Income-tax Act 2025."""
    return (
        Fraction(5, 100)  * income_in(Fraction(400_000), Fraction(800_000), x)
      + Fraction(10, 100) * income_in(Fraction(800_000), Fraction(1_200_000), x)
      + Fraction(15, 100) * income_in(Fraction(1_200_000), Fraction(1_600_000), x)
      + Fraction(20, 100) * income_in(Fraction(1_600_000), Fraction(2_000_000), x)
      + Fraction(25, 100) * income_in(Fraction(2_000_000), Fraction(2_400_000), x)
      + Fraction(30, 100) * income_above(Fraction(2_400_000), x)
    )


def rebate(x: Fraction) -> Fraction:
    """Rebate under s.156(2), Income-tax Act 2025."""
    t = tax_before_rebate(x)
    if x <= 1_200_000:
        return min(t, Fraction(60_000))          # s.156(2)(a)
    elif t > x - 1_200_000:
        return t - (x - Fraction(1_200_000))     # s.156(2)(b) marginal relief
    else:
        return Fraction(0)


def tax_after_rebate(x: Fraction) -> Fraction:
    return tax_before_rebate(x) - rebate(x)


def tax_with_cess(x: Fraction) -> Fraction:
    """Total tax including 4% Health & Education Cess (Finance Act 2026, s.2(6))."""
    return (Fraction(1) + Fraction(4, 100)) * tax_after_rebate(x)


class TaxRow(NamedTuple):
    income: int
    base_tax: float
    rebate: float
    tax_after_rebate: float
    cess: float
    total_tax: float
    take_home: float
    marginal_rate_pct: float   # vs previous row; NaN for first


TEST_INCOMES = sorted(set([
    # well below rebate threshold
    0, 100_000, 200_000, 300_000, 400_000,
    # slab boundaries
    500_000, 600_000, 700_000, 800_000,
    900_000, 1_000_000, 1_100_000,
    # dense around rebate threshold (Rs 12L)
    1_150_000, 1_180_000, 1_190_000, 1_195_000,
    1_200_000,
    1_200_001,
    1_201_000, 1_205_000, 1_210_000,
    1_220_000, 1_230_000, 1_240_000, 1_250_000,
    1_260_000, 1_270_000, 1_280_000, 1_290_000,
    1_300_000,
    # cliff recovery and above
    1_350_000, 1_400_000,
    # higher slab boundaries
    1_600_000, 2_000_000, 2_400_000,
    2_500_000, 3_000_000, 5_000_000,
    # very high
    10_000_000, 50_000_000,
]))


def compute_table():
    rows = []
    prev_total = None
    prev_income = None
    for inc in TEST_INCOMES:
        x = Fraction(inc)
        bt  = tax_before_rebate(x)
        rb  = rebate(x)
        tar = tax_after_rebate(x)
        cs  = tax_with_cess(x) - tar
        tot = tax_with_cess(x)
        th  = x - tot

        if prev_total is not None and inc != prev_income:
            delta_tax = float(tot - prev_total)
            delta_inc = float(inc - prev_income)
            marg = (delta_tax / delta_inc) * 100
        else:
            marg = float('nan')

        rows.append(TaxRow(
            income=inc,
            base_tax=float(bt),
            rebate=float(rb),
            tax_after_rebate=float(tar),
            cess=float(cs),
            total_tax=float(tot),
            take_home=float(th),
            marginal_rate_pct=marg,
        ))
        prev_total = tot
        prev_income = inc
    return rows


def fmt(v: float, width: int = 12) -> str:
    if v == 0:
        return "0".rjust(width)
    return f"{v:,.0f}".rjust(width)


def main():
    rows = compute_table()

    header = (
        f"{'Income':>14}  {'BaseTax':>12}  {'Rebate':>12}  "
        f"{'AfterRebate':>12}  {'Cess':>12}  {'TotalTax':>12}  "
        f"{'TakeHome':>14}  {'Marginal%':>10}"
    )
    print("=" * len(header))
    print("Dhaal Validation Table – New Regime, Tax Year 2026-27")
    print("Income-tax Act 2025 s.202(1), s.156; Finance Act 2026 s.2(6)")
    print("=" * len(header))
    print(header)
    print("-" * len(header))

    cliff_rows = []
    for r in rows:
        marg_str = f"{r.marginal_rate_pct:>9.1f}%" if r.marginal_rate_pct == r.marginal_rate_pct else "       n/a"
        line = (
            f"{r.income:>14,}  {fmt(r.base_tax)}  {fmt(r.rebate)}  "
            f"{fmt(r.tax_after_rebate)}  {fmt(r.cess)}  {fmt(r.total_tax)}  "
            f"{fmt(r.take_home, 14)}  {marg_str}"
        )

        if r.marginal_rate_pct == r.marginal_rate_pct and r.marginal_rate_pct > 100:
            line += "  ◄ CLIFF"
            cliff_rows.append(r)
        print(line)

    print("-" * len(header))

    print()
    print("CLIFF ANALYSIS")
    print("-" * 60)

    take_home_at_12L = float(Fraction(1_200_000) - tax_with_cess(Fraction(1_200_000)))
    worst_loss = 0
    worst_income = 0
    for inc in range(1_200_001, 1_350_000):
        x = Fraction(inc)
        th = float(x - tax_with_cess(x))
        loss = take_home_at_12L - th
        if loss > worst_loss:
            worst_loss = loss
            worst_income = inc

    print(f"Take-home at Rs 12,00,000:  Rs {take_home_at_12L:,.0f}")
    print(f"Worst cliff at Rs {worst_income:,}:  take-home = Rs {float(Fraction(worst_income) - tax_with_cess(Fraction(worst_income))):,.0f}")
    print(f"Maximum loss:             Rs {worst_loss:,.2f}")

    for inc in range(1_200_001, 2_000_000):
        x = Fraction(inc)
        th = float(x - tax_with_cess(x))
        if th >= take_home_at_12L:
            print(f"Recovery at Rs {inc:,}:      take-home = Rs {th:,.0f}")
            break

    print()
    print("WITHOUT CESS (tax after rebate only):")
    take_home_no_cess_12L = float(Fraction(1_200_000) - tax_after_rebate(Fraction(1_200_000)))
    print(f"  Take-home at Rs 12,00,000:  Rs {take_home_no_cess_12L:,.0f}")

    for inc in [1_200_001, 1_210_000, 1_250_000, 1_300_000]:
        x = Fraction(inc)
        th = float(x - tax_after_rebate(x))
        loss = take_home_no_cess_12L - th
        print(f"  Take-home at Rs {inc:>10,}:  Rs {th:,.0f}  (loss = Rs {loss:,.2f})")

    print()
    print("CONCLUSION: Tax after rebate (without cess) is cliff-free.")
    print("            The 4% cess reopens a cliff near Rs 12,00,000.")
    print("            Proved in Lean: taxAfterRebate_lipschitz, taxWithCess_cliff.")


if __name__ == "__main__":
    main()

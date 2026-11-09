# Dhaal

Dhaal is a Lean 4 model of the new tax regime under the Income Tax Act, 2025, for Tax Year 2026-27. It proves that the rebate's marginal relief removes the **tax cliff** at ₹12 lakh, and that the 4% cess brings it back.
Both results are also proved in general, for any tax that never falls and never rises faster than income.

## Findings

> The rebate with marginal relief (Income Tax Act, 2025, s.156) is **cliff-free**: for any incomes x ≤ y, the increase in tax is at most the increase in income.

> The Health and Education Cess (Finance Act, 2026, s.2(6)) **reintroduces a cliff** just above ₹12L, with a marginal tax rate of 104%. At worst, a taxpayer earning ₹12,70,588 takes home ₹2,824 less than one earning ₹12,00,000.

> In general: a rebate with marginal relief is cliff-free for any tax that never falls and never rises faster than income. **Any positive cess** charged on top of it brings a cliff back.

The cliff-free results are proved in Lean for every income.
The cliff results are proved by exhibiting a pair of incomes, also checked by Lean.

## Chart

![Tax cliff near ₹12 lakh](cliff_chart.svg)

The blue line is the rebate with marginal relief alone. It stays flat at zero, so there is no cliff.

The red line adds the 4% cess. Between ₹12,00,001 and ₹12,73,933, take-home pay is lower than at ₹12,00,000: earning more leaves you with less.

## Sources

- **Slab rates:** Income Tax Act, 2025 (No. 30 of 2025), s.202(1)
- **Rebate and marginal relief:** Income Tax Act, 2025 (No. 30 of 2025), s.156(2)
- **Cess:** Finance Act, 2026 (No. 4 of 2026), s.2(6)

Texts used:

- [Income Tax Act, 2025, as amended by the Finance Act, 2026](https://www.incometaxindia.gov.in/documents/d/guest/income_tax_act_2025_as_amended_by_fa_act_2026-pdf) (Income Tax Department)
- [Finance Act, 2026](https://egazette.gov.in/WriteReadData/2026/271439.pdf) (Gazette of India)

## Scope

- **Input:** taxable income, after the standard deduction.
- **In scope:** new regime, individual taxpayer, slab rates, rebate with marginal relief, 4% cess.
- **Out of scope:** surcharge, rounding of tax to the nearest ₹10, the old regime, special-rate income such as capital gains.
- **Numbers:** exact rationals (ℚ), so every value can be computed and checked.

## Files

- [`Dhaal/General.lean`](Dhaal/General.lean): brackets, slab schedules, rebate and cess for any thresholds and rates.
- [`Dhaal/India.lean`](Dhaal/India.lean): India's definitions, validation examples, and every result proved twice: `ViaDirect` (from the slabs) and `ViaGeneral` (as an instance of `General.lean`).

## Theorems

### General

```lean
theorem baseTax_lipschitz (h : x ≤ y) (hk : 0 ≤ k)
    (hthres : ThresAscending ((t, r) :: rest)) (hrate : RatesIn k ((t, r) :: rest)) :
    baseTax ((t, r) :: rest) y - baseTax ((t, r) :: rest) x ≤ k * (y - x)
```

*Any slab schedule with ascending thresholds and rates in [0, k] rises by at most k times the rise in income.*

```lean
theorem taxAfterRebate_lipschitz (h : x ≤ y)
    (hmono : ∀ a b, a ≤ b → base a ≤ base b)
    (hlip : ∀ a b, a ≤ b → base b - base a ≤ b - a)
    (hTR : base T ≤ R) :
    taxAfterRebate base T R y - taxAfterRebate base T R x ≤ y - x
```

*A rebate with marginal relief is cliff-free, if the full rebate R covers the tax at the threshold T.*

```lean
theorem withCess_cliff (hmono : ∀ a b, a ≤ b → base a ≤ base b) (hTR : base T ≤ R)
    (hc : 0 < c) (hT : 0 < base T) :
    ∃ x y, x ≤ y ∧ y - x < taxWithCess c base T R y - taxWithCess c base T R x
```

*Any positive cess on top brings a cliff back. Witness: x = T, y = T + base T.*

### India

```lean
theorem taxBeforeRebate_lipschitz {x y : ℚ} (h : x ≤ y) :
    taxBeforeRebate y - taxBeforeRebate x ≤ 3 / 10 * (y - x)
```

*For any incomes x ≤ y, slab tax rises by at most 30% of the rise in income.*

```lean
theorem taxAfterRebate_lipschitz {x y : ℚ} (h : x ≤ y) :
    taxAfterRebate y - taxAfterRebate x ≤ y - x
```

*After the rebate, tax rises by at most the rise in income: marginal relief prevents a cliff.*

```lean
theorem taxWithCess_cliff :
    ∃ x y : ℚ, x ≤ y ∧ y - x < taxWithCess y - taxWithCess x
```

*With cess, there are incomes where tax rises by more than income. From ₹12,00,000 to ₹12,70,000, income rises ₹70,000 and tax rises ₹72,800.*

`incomeIn_lipschitz` is proved twice, once by case analysis and once as a `calc` chain, to show both styles.

## Validation

Every figure below matches the [official tax calculator](https://www.incometax.gov.in) on the Income Tax e-filing portal. The same figures are Lean `example`s in `Dhaal/India.lean`, checked on every build. `validation.py` computes the full table of 40+ incomes with the same formulas.

| Income | Base Tax | Rebate | After Rebate | Total Tax (with cess) | Take-Home |
|---:|---:|---:|---:|---:|---:|
| 10,00,000 | 40,000 | 40,000 | 0 | 0 | 10,00,000 |
| 12,00,000 | 60,000 | 60,000 | 0 | 0 | 12,00,000 |
| 12,10,000 | 61,500 | 51,500 | 10,000 | 10,400 | 11,99,600 |
| 12,70,000 | 70,500 | 500 | 70,000 | 72,800 | 11,97,200 |
| 13,00,000 | 75,000 | 0 | 75,000 | 78,000 | 12,22,000 |
| 25,00,000 | 3,30,000 | 0 | 3,30,000 | 3,43,200 | 21,56,800 |

At ₹12,10,000, take-home (₹11,99,600) is less than at ₹12,00,000 (₹12,00,000). That is the cliff.

## Build

```bash
git clone https://github.com/sayyadirfanali/dhaal && cd dhaal
lake exe cache get   # downloads prebuilt Mathlib
lake build
```

To regenerate the table and the chart:

```bash
pip install -r requirements.txt
python3 validation.py
python3 chart.py
```

## Next Steps
- Surcharge and its marginal relief, at the surcharge thresholds (₹50L, ₹1Cr, …)
- Rounding of tax to the nearest ₹10, which may create small cliffs of its own
- Re-checking past budgets with the general theorem

## Authorship
I read the statutes, made the modelling decisions and wrote most of the Lean proofs.
I used Claude mostly to search Mathlib lemmas and to discuss Lean tactics.
Claude also completed some of the general proofs and drafted the Python scripts and parts of this README.

## Contact

Sayyad Irfan Ali · irfan@irfanali.org · [irfanali.org](https://irfanali.org)

Corrections are welcome, especially on how I've read the statute. Open an issue or email me.

## License

[MIT](LICENSE)

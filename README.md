# dhaal

dhaal is a Lean 4 formalisation of Indian income tax rules.

I've modelled the new tax regime under the Income Tax Act, 2025 to explore properties of rebate rules with respect to **tax cliffs** especially when it interacts with cess.

## The Problem

Under Section 156 of the Income Tax Act, 2025, a rebate reduces tax on a total income of ₹12.0L to ₹0. But the 4% cess levied by the Finance Act, 2026, which expressly allows no marginal relief, creates a tax cliff: at ₹12.7L, total tax is ₹72.8k, leaving ₹2.8k less take-home pay than at ₹12.0L.

Dhaal proves three structural facts about how these rules interact:

1. **Marginal relief prevents cliffs on its own.** Under Section 156, marginal relief caps extra tax so it never exceeds extra income above the ₹12.0L threshold, guaranteeing take-home pay never drops as total income rises.
2. **The 4% cess reintroduces the cliff.** Under Section 2(6) of the Finance Act, 2026, the Health and Education Cess is levied *after* rebate and marginal relief. Consequently, any total income between **₹12.L and ₹12.73L** yields less take-home pay than ₹12.0L (an effective marginal tax rate of 104% up to ₹12.7L).
3. **This holds for any tax system.** Any slab schedule with marginal relief is cliff-free as long as base tax is monotonic and 1-Lipschitz, whereas applying any positive proportional cess on top of a capped tax always creates a cliff.

![Tax cliff near ₹12 lakh](cliff_chart.svg)
*Before cess (blue), take-home pay is non-decreasing. Adding the 4% cess (red) creates a net-income dip between ₹12.0L and ₹12.73L*

## Statutory Sources

- **Tax slabs:** [Income Tax Act, 2025](https://www.incometaxindia.gov.in/documents/d/guest/income_tax_act_2025_as_amended_by_fa_act_2026-pdf), Section 202(1)
- **Rebate and marginal relief:** Income Tax Act, 2025 (No. 30 of 2025), Section 156(2)
- **Health and Education Cess (4%):** [Finance Act, 2026](https://egazette.gov.in/WriteReadData/2026/271439.pdf), Section 2(6)

## Formalised Theorems

### General Rules (`Dhaal/General.lean`)
- **`baseTax_lipschitz`:** A slab schedule is Lipschitz continuous, with constant equal to any upper bound on its rates.
- **`taxAfterRebate_lipschitz`:** A rebate with marginal relief is cliff-free across all incomes whenever the maximum rebate covers the tax at the threshold.
- **`withCess_cliff`:** Applying any positive cess after marginal relief produces a cliff, proved by constructing a witness pair right at and just above the threshold.

### Indian Tax Rules (`Dhaal/India.lean`)
- **`taxBeforeRebate_lipschitz`:** Under the 2026-27 slabs, base tax grows by at most 30% of any income increase.
- **`taxAfterRebate_lipschitz`:** Before cess, Section 156 marginal relief guarantees zero tax cliffs at any income level.
- **`taxWithCess_cliff`:** With the 4% cess included, a cliff occurs between ₹12.0L and ₹12.7L.

(Note: The India results are proved twice, directly in `ViaDirect` and via the general theorems in `ViaGeneral`, as a reference for Lean learners.)

## Empirical Validation

All figures below match the [Income Tax e-filing portal calculator](https://www.incometax.gov.in) and are checked as Lean examples in Dhaal/India.lean on every build.
`validation.py` tabulates 40+ further income points.

| Income (₹) | Base Tax (₹) | Rebate (₹) | Tax After Rebate (₹) | Total Tax with 4% Cess (₹) | Take-Home Pay (₹) |
|---:|---:|---:|---:|---:|---:|
| 10,00,000 | 40,000 | 40,000 | 0 | 0 | 10,00,000 |
| 12,00,000 | 60,000 | 60,000 | 0 | 0 | 12,00,000 |
| 12,10,000 | 61,500 | 51,500 | 10,000 | 10,400 | 11,99,600 |
| 12,70,000 | 70,500 | 500 | 70,000 | 72,800 | 11,97,200 |
| 13,00,000 | 75,000 | 0 | 75,000 | 78,000 | 12,22,000 |
| 25,00,000 | 3,30,000 | 0 | 3,30,000 | 3,43,200 | 21,56,800 |

## Usage

```bash
# Verify Lean 4 proofs
git clone https://github.com/sayyadirfanali/dhaal && cd dhaal
lake exe cache get   # Fetch prebuilt Mathlib cache
lake build           # Check all proofs

# Regenerate validation data and chart (optional)
pip install -r requirements.txt
python3 validation.py && python3 chart.py
```

## Authorship

I read the statutes, made the model, and authored the core definitions and proofs. Claude and Gemini assisted with Mathlib lemmas, proof steps, Python scripts, and README. I have manually verified all definitions and proof statements against the statutory text.

## Contact

Irfan Ali | irfanali.org

Corrections are welcome, especially regarding my reading of the statutes. Please open a GitHub issue or email me.

import Dhaal.General
set_option linter.style.header false

open Dhaal (
  incomeIn incomeAbove
  incomeIn_nonneg incomeIn_mono incomeIn_add incomeIn_incomeAbove_add
  incomeAbove_nonneg incomeAbove_mono incomeAbove_lipschitz
  )

namespace India

def taxBeforeRebate (x : ℚ) : ℚ :=
   5/100 * incomeIn (400000, 800000)   x +
  10/100 * incomeIn (800000, 1200000)  x +
  15/100 * incomeIn (1200000, 1600000) x +
  20/100 * incomeIn (1600000, 2000000) x +
  25/100 * incomeIn (2000000, 2400000) x +
  30/100 * incomeAbove 2400000 x

/-- rebate under Income Tax Act 2025 ss.156(2), encoded literally -/
def rebate (x : ℚ) : ℚ :=
  -- s.156(2)(a)
  if x ≤ 1200000 then min (taxBeforeRebate x) 60000
  -- s.156(2)(b)
  else if x - 1200000 < taxBeforeRebate x then taxBeforeRebate x - (x - 1200000)
  else 0

def taxAfterRebate (x : ℚ) : ℚ := taxBeforeRebate x - rebate x

/-- Cess under Finance Act, 2026, ss.2(6) -/
def taxWithCess (x : ℚ) : ℚ := (1 + 4/100) * taxAfterRebate x


macro "tax_norm" : tactic =>
  `(tactic| norm_num [taxWithCess, taxAfterRebate, taxBeforeRebate, rebate,
                      incomeIn, incomeAbove])

example : taxBeforeRebate  400000 =      0 := by tax_norm
example : taxBeforeRebate  800000 =  20000 := by tax_norm
example : taxBeforeRebate 1200000 =  60000 := by tax_norm
example : taxBeforeRebate 1600000 = 120000 := by tax_norm
example : taxBeforeRebate 2000000 = 200000 := by tax_norm
example : taxBeforeRebate 2400000 = 300000 := by tax_norm
example : taxBeforeRebate 2500000 = 330000 := by tax_norm

example : taxAfterRebate 1000000 = 0 := by tax_norm
example : taxAfterRebate 1200000 = 0 := by tax_norm

example : taxAfterRebate 1210000 = 10000 := by tax_norm
example : taxAfterRebate 1270000 = 70000 := by tax_norm

example : taxAfterRebate (1200000 + 1200000/17) = 1200000/17 := by tax_norm

example : taxAfterRebate 1300000 = 75000 := by tax_norm

example : taxWithCess 1000000 =      0 := by tax_norm
example : taxWithCess 1200000 =      0 := by tax_norm
example : taxWithCess 1200001 =  26/25 := by tax_norm -- cliff (₹1.04 on ₹1 more)
example : taxWithCess 1210000 =  10400 := by tax_norm
example : taxWithCess 1270000 =  72800 := by tax_norm
example : taxWithCess 1300000 =  78000 := by tax_norm
example : taxWithCess 2500000 = 343200 := by tax_norm

example : 1270000 - taxWithCess 1270000 = 1197200 := by tax_norm

namespace ViaDirect

lemma incomeIn_merge (z : ℚ) :
      incomeIn (400000, 800000)   z
    + incomeIn (800000, 1200000)  z
    + incomeIn (1200000, 1600000) z
    + incomeIn (1600000, 2000000) z
    + incomeIn (2000000, 2400000) z
    + incomeAbove 2400000 z
    = incomeAbove 400000 z := by
  have h1 := incomeIn_add 400000  800000 1200000 z (by norm_num) (by norm_num)
  have h2 := incomeIn_add 400000 1200000 1600000 z (by norm_num) (by norm_num)
  have h3 := incomeIn_add 400000 1600000 2000000 z (by norm_num) (by norm_num)
  have h4 := incomeIn_add 400000 2000000 2400000 z (by norm_num) (by norm_num)
  have h5 := incomeIn_incomeAbove_add 400000 2400000 z (by norm_num)
  rw [h1, h2, h3, h4, h5]

lemma taxBeforeRebate_nonneg (x : ℚ) :
    0 ≤ taxBeforeRebate x := by
  simp only [taxBeforeRebate]
  have := incomeIn_nonneg 400000 800000 x
  have := incomeIn_nonneg 800000 1200000 x
  have := incomeIn_nonneg 1200000 1600000 x
  have := incomeIn_nonneg 1600000 2000000 x
  have := incomeIn_nonneg 2000000 2400000 x
  have := incomeAbove_nonneg 2400000 x
  linarith

lemma taxBeforeRebate_mono {x y : ℚ} (h : x ≤ y) :
    taxBeforeRebate x ≤ taxBeforeRebate y := by
  simp only [taxBeforeRebate, incomeIn, incomeAbove]
  gcongr

lemma taxBeforeRebate_lipschitz {x y : ℚ} (h : x ≤ y) :
    taxBeforeRebate y - taxBeforeRebate x ≤ 3 / 10 * (y - x) := by
  have := incomeIn_mono  400000  800000 h
  have := incomeIn_mono  800000 1200000 h
  have := incomeIn_mono 1200000 1600000 h
  have := incomeIn_mono 1600000 2000000 h
  have := incomeIn_mono 2000000 2400000 h
  have := incomeAbove_mono 2400000 h
  have := incomeAbove_lipschitz 400000 h
  have := incomeIn_merge x
  have := incomeIn_merge y
  simp only [taxBeforeRebate]
  linarith

lemma rebate_nonneg (x : ℚ) : 0 ≤ rebate x := by
  have := taxBeforeRebate_nonneg x
  simp only [rebate, min_def]
  split_ifs <;> linarith

lemma taxAfterRebate_of_le {x : ℚ} (hx : x ≤ 1200000) :
    taxAfterRebate x = 0 := by
  simp only [taxAfterRebate, rebate]
  split
  case isFalse => contradiction
  case isTrue  =>
    have hle : taxBeforeRebate x ≤ 60000 := by
      calc taxBeforeRebate x
         ≤ taxBeforeRebate 1200000 := taxBeforeRebate_mono hx
      _  = 60000 := by norm_num [taxBeforeRebate, incomeIn, incomeAbove]
    simp only [min_eq_left hle, sub_self]

lemma taxAfterRebate_of_gt {x : ℚ} (hx : 1200000 < x) :
    taxAfterRebate x = min (taxBeforeRebate x) (x - 1200000) := by
  simp only [taxAfterRebate, rebate, min_def]
  split_ifs <;> linarith

theorem taxAfterRebate_lipschitz {x y : ℚ} (h : x ≤ y) :
    taxAfterRebate y - taxAfterRebate x ≤ y - x := by
  rcases le_or_gt y 1200000 with hy | hy
  · have := taxAfterRebate_of_le hy
    have := taxAfterRebate_of_le (by linarith : x ≤ 1200000)
    linarith
  · rcases le_or_gt x 1200000 with hx | hx
    · rw [taxAfterRebate_of_le hx, taxAfterRebate_of_gt hy]
      simp only [min_def]
      have : 0 ≤ y - 1200000 := by linarith
      have := taxBeforeRebate_nonneg y
      split_ifs <;> linarith
    · rw [taxAfterRebate_of_gt hx, taxAfterRebate_of_gt hy]
      simp only [min_def]
      split_ifs <;> linarith [taxBeforeRebate_lipschitz h]

theorem taxWithCess_cliff :
    ∃ x y : ℚ, x ≤ y ∧ y - x < taxWithCess y - taxWithCess x := by
  use 1200000, 1270000
  simp only [taxWithCess, taxAfterRebate, taxBeforeRebate, rebate, incomeIn, incomeAbove]
  norm_num

end ViaDirect

namespace ViaGeneral

abbrev schedule : List (ℚ × ℚ) :=
  [
    (400000, 5/100),
    (800000, 10/100),
    (1200000, 15/100),
    (1600000, 20/100),
    (2000000, 25/100),
    (2400000, 30/100)
  ]

lemma taxBeforeRebate_eq_baseTax (x : ℚ) :
    taxBeforeRebate x = Dhaal.baseTax schedule x := by
  simp only [taxBeforeRebate, Dhaal.baseTax]
  ring

lemma rebate_eq (x : ℚ) :
    rebate x = Dhaal.rebate taxBeforeRebate 1200000 60000 x := rfl

lemma taxAfterRebate_eq (x : ℚ) :
    taxAfterRebate x = Dhaal.taxAfterRebate taxBeforeRebate 1200000 60000 x := rfl

lemma taxWithCess_eq (x : ℚ) :
    taxWithCess x = Dhaal.taxWithCess (4/100) taxBeforeRebate 1200000 60000 x := rfl

lemma schedule_thres : Dhaal.ThresAscending schedule := by
  simp only [Dhaal.ThresAscending]
  norm_num

lemma schedule_rates : Dhaal.RatesIn (3/10) schedule := by
  intro p hp
  simp only [schedule, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

lemma tax_at_threshold : taxBeforeRebate 1200000 = 60000 := by
  norm_num [taxBeforeRebate, incomeIn, incomeAbove]

lemma taxBeforeRebate_nonneg (x : ℚ) :
    0 ≤ taxBeforeRebate x := by
  rw [taxBeforeRebate_eq_baseTax]
  exact Dhaal.baseTax_nonneg schedule x schedule_rates

lemma taxBeforeRebate_mono {x y : ℚ} (h : x ≤ y) :
    taxBeforeRebate x ≤ taxBeforeRebate y := by
  rw [taxBeforeRebate_eq_baseTax, taxBeforeRebate_eq_baseTax]
  exact Dhaal.baseTax_mono h schedule schedule_rates

lemma taxBeforeRebate_lipschitz {x y : ℚ} (h : x ≤ y) :
    taxBeforeRebate y - taxBeforeRebate x ≤ 3 / 10 * (y - x) := by
  rw [taxBeforeRebate_eq_baseTax, taxBeforeRebate_eq_baseTax]
  exact Dhaal.baseTax_lipschitz h (by norm_num) schedule_thres schedule_rates

lemma taxAfterRebate_of_le {x : ℚ} (hx : x ≤ 1200000) :
    taxAfterRebate x = 0 := by
  rw [taxAfterRebate_eq]
  exact Dhaal.taxAfterRebate_of_le
    (fun _ _ h => taxBeforeRebate_mono h) (le_of_eq tax_at_threshold) hx

lemma taxAfterRebate_of_gt {x : ℚ} (hx : 1200000 < x) :
    taxAfterRebate x = min (taxBeforeRebate x) (x - 1200000) := by
  rw [taxAfterRebate_eq]
  exact Dhaal.taxAfterRebate_of_gt hx

theorem taxAfterRebate_lipschitz {x y : ℚ} (h : x ≤ y) :
    taxAfterRebate y - taxAfterRebate x ≤ y - x := by
  rw [taxAfterRebate_eq, taxAfterRebate_eq]
  exact Dhaal.taxAfterRebate_lipschitz h
    (fun _ _ h => taxBeforeRebate_mono h)
    (fun _ _ h => by linarith [taxBeforeRebate_lipschitz h])
    (le_of_eq tax_at_threshold)

theorem taxWithCess_cliff :
    ∃ x y : ℚ, x ≤ y ∧ y - x < taxWithCess y - taxWithCess x := by
  simp only [taxWithCess_eq]
  exact Dhaal.withCess_cliff
    (fun _ _ h => taxBeforeRebate_mono h) (le_of_eq tax_at_threshold)
    (by norm_num) (by rw [tax_at_threshold]; norm_num)

end ViaGeneral

end India

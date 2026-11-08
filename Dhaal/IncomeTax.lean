import Mathlib

namespace Dhaal
def incomeIn : ℚ × ℚ → ℚ → ℚ
  | (lo, hi), x => max (min x hi - lo) 0

def incomeAbove : ℚ → ℚ → ℚ
  | lo, x => max 0 (x - lo)

def taxBeforeRebate (x : ℚ) : ℚ :=
   5/100 * incomeIn (400000, 800000)   x +
  10/100 * incomeIn (800000, 1200000)  x +
  15/100 * incomeIn (1200000, 1600000) x +
  20/100 * incomeIn (1600000, 2000000) x +
  25/100 * incomeIn (2000000, 2400000) x +
  30/100 * incomeAbove 2400000 x

/-- Rebate under S.156(2), Income Tax Act 2025, encoded literally. -/
def rebate (x : ℚ) : ℚ :=
  -- Income Tax Act (2)(a)
  if x ≤ 1200000 then min (taxBeforeRebate x) 60000
  -- Income Tax Act (2)(b)
  else if x - 1200000 < taxBeforeRebate x then taxBeforeRebate x - (x - 1200000)
  else 0

def taxAfterRebate (x : ℚ) : ℚ := taxBeforeRebate x - rebate x

-- Finance Act 2(6)
def taxWithCess (x : ℚ) : ℚ := (1 + 4/100) * taxAfterRebate x

-- incomeIn
lemma incomeIn_nonneg (lo hi x : ℚ) :
    0 ≤ incomeIn (lo, hi) x := by
  simp only [incomeIn]
  exact le_max_right (min x hi - lo) 0

@[gcongr]
lemma incomeIn_mono (lo hi : ℚ) {x y : ℚ} (h : x ≤ y) :
    incomeIn (lo, hi) x ≤ incomeIn (lo, hi) y := by
  simp only [incomeIn]
  gcongr

lemma incomeIn_lipschitz (lo hi : ℚ) {x y : ℚ} (h : x ≤ y) :
    incomeIn (lo, hi) y - incomeIn (lo, hi) x ≤ y - x := by
  simp only [incomeIn]
  simp only [max_def, min_def]
  split_ifs <;> linarith

lemma incomeIn_lipschitz_calc (lo hi : ℚ) {x y : ℚ} (h : x ≤ y) :
    incomeIn (lo, hi) y - incomeIn (lo, hi) x ≤ y - x := by
  simp only [incomeIn]
  calc max (min y hi - lo) 0 - max (min x hi - lo) 0
      ≤ |max (min y hi - lo) 0 - max (min x hi - lo) 0| := le_abs_self _
    _ ≤ |(min y hi - lo) - (min x hi - lo)| := abs_max_sub_max_le_abs _ _ 0
    _ = |min y hi - min x hi| := by rw [sub_sub_sub_cancel_right]
    _ ≤ |y - x| := abs_inf_sub_inf_le_abs y x hi
    _ = y - x := abs_of_nonneg (by linarith)

lemma incomeIn_add (a b c x : ℚ) (hab : a ≤ b) (hbc : b ≤ c) :
    incomeIn (a, b) x + incomeIn (b, c) x = incomeIn (a, c) x := by
  simp only [incomeIn]
  simp only [max_def, min_def]
  split_ifs <;> linarith

lemma incomeIn_incomeAbove_add (a b x : ℚ) (hab : a ≤ b) :
    incomeIn (a, b) x + incomeAbove b x = incomeAbove a x := by
  simp only [incomeIn, incomeAbove]
  simp only [max_def, min_def]
  split_ifs <;> linarith

lemma incomeIn_merge (z : ℚ) :
      incomeIn (400000, 800000)   z
    + incomeIn (800000, 1200000)  z
    + incomeIn (1200000, 1600000) z
    + incomeIn (1600000, 2000000) z
    + incomeIn (2000000, 2400000) z
    + incomeAbove 2400000 z
    = incomeAbove 400000 z := by
      have h1 := incomeIn_add  400000  800000 1200000 z (by norm_num) (by norm_num)
      have h2 := incomeIn_add  400000 1200000 1600000 z (by norm_num) (by norm_num)
      have h3 := incomeIn_add  400000 1600000 2000000 z (by norm_num) (by norm_num)
      have h4 := incomeIn_add  400000 2000000 2400000 z (by norm_num) (by norm_num)
      have h5 := incomeIn_incomeAbove_add 400000 2400000 z (by norm_num)
      rw [h1, h2, h3, h4, h5]

-- incomeAbove
lemma incomeAbove_nonneg (lo x : ℚ) :
  0 ≤ incomeAbove lo x := by
  simp only [incomeAbove]
  exact le_max_left 0 (x - lo)

@[gcongr]
lemma incomeAbove_mono (lo : ℚ) {x y : ℚ} (h : x ≤ y) :
    incomeAbove lo x ≤ incomeAbove lo y := by
  simp only [incomeAbove]
  gcongr

lemma incomeAbove_lipschitz (lo : ℚ) {x y : ℚ} (h : x ≤ y) :
    incomeAbove lo y - incomeAbove lo x ≤ y - x := by
  simp only [incomeAbove, max_def]
  split_ifs <;> linarith

-- taxBeforeRebate
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

@[gcongr]
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

-- rebate
lemma rebate_nonneg (x : ℚ) : 0 ≤ rebate x := by
  have := taxBeforeRebate_nonneg x
  simp only [rebate, min_def]
  split_ifs <;> linarith

-- taxAfterRebate
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
    simp [min_eq_left hle]

lemma taxAfterRebate_of_gt {x : ℚ} (hx : 1200000 < x) :
    taxAfterRebate x = min (taxBeforeRebate x) (x - 1200000) := by
  simp only [taxAfterRebate, rebate, min_def]
  split_ifs <;> linarith

theorem taxAfterRebate_lipschitz {x y : ℚ} (h : x ≤ y) :
    taxAfterRebate y - taxAfterRebate x ≤ y - x := by
  rcases le_or_gt y 1200000 with hy | hy
  -- y ≤ 1200000
  · have := taxAfterRebate_of_le hy
    have := taxAfterRebate_of_le (by linarith : x ≤ 1200000)
    linarith
  -- ¬ y ≤ 1200000
  · rcases le_or_gt x 1200000 with hx | hx
    -- x ≤ 1200000
    · rw [taxAfterRebate_of_le hx, taxAfterRebate_of_gt hy]
      simp only [min_def]
      have : 0 ≤ y - 1200000 := by linarith
      have := taxBeforeRebate_nonneg y
      split_ifs <;> linarith
    -- ¬ x ≤ 1200000
    · rw [taxAfterRebate_of_gt hx, taxAfterRebate_of_gt hy]
      simp only [min_def]
      split_ifs <;>  linarith [taxBeforeRebate_lipschitz h]

theorem taxWithCess_cliff :
    ∃ x y : ℚ, x ≤ y ∧ y - x < taxWithCess y - taxWithCess x := by
    use 1200000, 1270000
    simp only [taxWithCess, taxAfterRebate, taxBeforeRebate, rebate, incomeIn, incomeAbove]
    norm_num

macro "tax_norm" : tactic => `(tactic| norm_num [taxWithCess, taxAfterRebate, taxBeforeRebate, rebate, incomeIn, incomeAbove])

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
example : taxWithCess 1200001 =  26/25 := by tax_norm   -- ₹1.04 on ₹1 more
example : taxWithCess 1210000 =  10400 := by tax_norm
example : taxWithCess 1270000 =  72800 := by tax_norm
example : taxWithCess 1300000 =  78000 := by tax_norm
example : taxWithCess 2500000 = 343200 := by tax_norm

example : 1270000 - taxWithCess 1270000 = 1197200 := by tax_norm

end Dhaal

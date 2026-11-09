import Mathlib
set_option linter.style.header false

namespace Dhaal

def incomeIn : ℚ × ℚ → ℚ → ℚ
  | (lo, hi), x => max (min x hi - lo) 0

def incomeAbove : ℚ → ℚ → ℚ
  | lo, x => max 0 (x - lo)

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

def baseTax : List (ℚ × ℚ) → ℚ → ℚ
  | [],                         _ => 0
  | [(t, r)],                   x => r * incomeAbove t x
  | (t, r) :: (t', r') :: rest, x => r * incomeIn (t, t') x + baseTax ((t', r') :: rest) x

def ThresAscending : List (ℚ × ℚ) → Prop
  | (t, _) :: (t', r') :: rest => t ≤ t' ∧ ThresAscending ((t', r') :: rest)
  | _                          => True

def RatesIn (k : ℚ) (ps : List (ℚ × ℚ)) : Prop := ∀ p ∈ ps, 0 ≤ p.2 ∧ p.2 ≤ k

theorem baseTax_nonneg {k : ℚ} (ps : List (ℚ × ℚ)) (x : ℚ) (hrate : RatesIn k ps) :
    0 ≤ baseTax ps x := by
  induction ps with
  | nil =>
    simp only [baseTax, le_rfl]
  | cons p ps ihp =>
    obtain ⟨t, r⟩ := p
    have hr : 0 ≤ r := (hrate (t, r) (by simp)).1
    rcases ps with _ | ⟨⟨t', r'⟩, ps'⟩
    · simp only [baseTax]
      exact mul_nonneg hr (incomeAbove_nonneg t x)
    · have hrest : 0 ≤ baseTax ((t', r') :: ps') x :=
        ihp (fun q hq => hrate q (List.mem_cons_of_mem _ hq))
      have hfirst := mul_nonneg hr (incomeIn_nonneg t t' x)
      simp only [baseTax]
      linarith

theorem baseTax_mono {k x y : ℚ}
    (h : x ≤ y)
    (ps : List (ℚ × ℚ))
    (hrate : RatesIn k ps) :
    baseTax ps x ≤ baseTax ps y := by
  induction ps with
  | nil =>
    simp only [baseTax, le_rfl]
  | cons p ps ihp =>
    obtain ⟨t, r⟩ := p
    have hr : 0 ≤ r := (hrate (t, r) (by simp)).1
    rcases ps with _ | ⟨⟨t', r'⟩, ps'⟩
    · simp only [baseTax]
      exact mul_le_mul_of_nonneg_left (incomeAbove_mono t h) hr
    · simp only [baseTax]
      have hfirst : r * incomeIn (t, t') x ≤ r * incomeIn (t, t') y :=
        mul_le_mul_of_nonneg_left (incomeIn_mono t t' h) hr
      have hrest : baseTax ((t', r') :: ps') x ≤ baseTax ((t', r') :: ps') y :=
        ihp (fun q hq => hrate q (List.mem_cons_of_mem _ hq))
      linarith

theorem baseTax_le_above {k x y : ℚ}
    (h : x ≤ y)
    (t r : ℚ)
    (rest : List (ℚ × ℚ))
    (hthres : ThresAscending ((t, r) :: rest))
    (hrate : RatesIn k ((t, r) :: rest)) :
    baseTax ((t, r) :: rest) y - baseTax ((t, r) :: rest) x
      ≤ k * (incomeAbove t y - incomeAbove t x) := by
  induction rest generalizing t r with
  | nil =>
    simp only [baseTax]
    have hmono := incomeAbove_mono t h
    have hrk := (hrate (t, r) (by simp)).2
    have hpos : 0 ≤ incomeAbove t y - incomeAbove t x := by linarith
    rw [<- mul_sub]
    exact mul_le_mul_of_nonneg_right hrk hpos
  | cons p rest ih =>
    obtain ⟨t', r'⟩ := p
    have ih' := ih t' r' hthres.2 (fun q hq => hrate q (List.mem_cons_of_mem _ hq))
    have hrk : r ≤ k := (hrate (t, r) (by simp)).2
    set ity := incomeIn (t, t') y with hIty
    set itx := incomeIn (t, t') x with hItx
    have hD : 0 ≤ ity - itx := by linarith [incomeIn_mono t t' h]
    simp only [baseTax]
    have : r * ity - r * itx ≤ k * (ity - itx) := by
      rw [<- mul_sub]
      exact mul_le_mul_of_nonneg_right hrk hD
    rw [<- incomeIn_incomeAbove_add t t' y hthres.1, <- incomeIn_incomeAbove_add t t' x hthres.1]
    linarith

theorem baseTax_lipschitz {k x y t r : ℚ} {rest : List (ℚ × ℚ)}
    (h : x ≤ y)
    (hk : 0 ≤ k)
    (hthres : ThresAscending ((t, r) :: rest))
    (hrate : RatesIn k ((t, r) :: rest)) :
    baseTax ((t, r) :: rest) y - baseTax ((t, r) :: rest) x ≤ k * (y - x) := by
  have habove := baseTax_le_above h t r rest hthres hrate
  have hlip := incomeAbove_lipschitz t h
  have hscale : k * (incomeAbove t y - incomeAbove t x) ≤ k * (y - x) :=
    mul_le_mul_of_nonneg_left hlip hk
  linarith

def rebate (base : ℚ → ℚ) (T R x : ℚ) : ℚ :=
  if x ≤ T then min (base x) R
  else if base x > x - T then base x - (x - T)
  else 0

def taxAfterRebate (base : ℚ → ℚ) (T R x : ℚ) : ℚ := base x - rebate base T R x

theorem taxAfterRebate_of_le {baseTax : ℚ → ℚ} {T R x : ℚ}
    (hmono : ∀ a b, a ≤ b → baseTax a ≤ baseTax b)
    (hTR : baseTax T ≤ R)
    (hx : x ≤ T) :
    taxAfterRebate baseTax T R x = 0 := by
  have hle : baseTax x ≤ R := le_trans (hmono x T hx) hTR
  simp only [taxAfterRebate, rebate, ite_eq_left hx]
  rw [min_eq_left hle]
  ring

theorem taxAfterRebate_of_gt {baseTax : ℚ → ℚ} {T R x : ℚ}
    (hx : T < x) :
    taxAfterRebate baseTax T R x = min (baseTax x) (x - T) := by
  have hnx : ¬ x ≤ T := not_le.mpr hx
  simp only [taxAfterRebate, rebate, ite_eq_right hnx]
  split_ifs with hb
  · rw [min_eq_right (by linarith)]
    ring
  · push Not at hb
    rw [min_eq_left hb]
    ring

theorem taxAfterRebate_lipschitz {base : ℚ → ℚ} {T R x y : ℚ}
    (h : x ≤ y)
    (hmono : ∀ a b, a ≤ b → base a ≤ base b)
    (hlip : ∀ a b, a ≤ b → base b - base a ≤ b - a)
    (hTR : base T ≤ R) :
    taxAfterRebate base T R y - taxAfterRebate base T R x ≤ y - x := by
  rcases le_or_gt y T with hy | hy
  · rw [taxAfterRebate_of_le hmono hTR hy,
        taxAfterRebate_of_le hmono hTR (le_trans h hy)]
    linarith
  · rcases le_or_gt x T with hx | hx
    · rw [taxAfterRebate_of_le hmono hTR hx, taxAfterRebate_of_gt hy]
      simp only [min_def]
      split_ifs <;> linarith
    · rw [taxAfterRebate_of_gt hx, taxAfterRebate_of_gt hy]
      have := hlip x y h
      simp only [min_def]
      split_ifs <;> linarith

def taxWithCess (c : ℚ) (base : ℚ → ℚ) (T R x : ℚ) : ℚ := (1 + c) * taxAfterRebate base T R x

theorem withCess_cliff {base : ℚ → ℚ} {T R c : ℚ}
    (hmono : ∀ a b, a ≤ b → base a ≤ base b)
    (hTR : base T ≤ R)
    (hc : 0 < c)
    (hT : 0 < base T) :
    ∃ x y, x ≤ y ∧ y - x < taxWithCess c base T R y - taxWithCess c base T R x := by
  have hgt : T < T + base T := by linarith
  have hwidth : T + base T - T = base T := by ring
  have hmin : min (base (T + base T)) (base T) = base T :=
    min_eq_right (hmono T (T + base T) (le_of_lt hgt))
  refine ⟨T, T + base T, le_of_lt hgt, ?_⟩
  simp only [taxWithCess]
  rw [taxAfterRebate_of_le hmono hTR (le_refl T), taxAfterRebate_of_gt hgt, hwidth, hmin]
  have := mul_pos hc hT
  linarith

end Dhaal

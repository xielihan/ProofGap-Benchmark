import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

namespace ProofGap.Exercise1625

noncomputable section

def equation (x : ℝ) : Prop := x * Real.tanh x = 1
def f (x : ℝ) := Real.tanh x - 1 / x
def Approx (actual expected tolerance : ℝ) : Prop :=
  |actual - expected| < tolerance
def upperApproximant : ℕ → ℝ
  | 1 => 1.339
  | 2 => 1.2032
  | 3 => 1.1996796
  | _ => 0
def lowerApproximant : ℕ → ℝ
  | 1 => 1.168
  | 2 => 1.1989
  | 3 => 1.1996781
  | _ => 0
def reportedRoots : Set ℝ := {-1.199678, 1.199678}
def ApproxRootSet (samples : Set ℝ) (tolerance : ℝ) : Prop :=
  (∀ s ∈ samples, ∃ r, equation r ∧ |s - r| < tolerance) ∧
    (∀ r, equation r → ∃ s ∈ samples, |r - s| < tolerance)

private lemma tanh_hasDerivAt (x : ℝ) :
    HasDerivAt Real.tanh (1 / (Real.cosh x) ^ 2) x := by
  have hc : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  have hq := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hc
  have hq' : HasDerivAt (fun y => Real.sinh y / Real.cosh y)
      (1 / (Real.cosh x) ^ 2) x := by
    convert hq using 1
    field_simp [hc]
    nlinarith [Real.cosh_sq_sub_sinh_sq x]
  rw [show Real.tanh = fun y => Real.sinh y / Real.cosh y by
    funext y; exact Real.tanh_eq_sinh_div_cosh y]
  exact hq'

private def expLower16 (x : ℝ) : ℝ :=
  ∑ m ∈ Finset.range 16, x ^ m / m.factorial

private def expUpper16 (x : ℝ) : ℝ :=
  expLower16 x + x ^ 16 * 17 / ((16 : ℕ).factorial * 16)

private lemma exp_four_lower (x b : ℝ) (hx0 : 0 ≤ x)
    (hcalc : b < (expLower16 x) ^ 4) :
    b < Real.exp (4 * x) := by
  have hle : expLower16 x ≤ Real.exp x := by
    exact Real.sum_le_exp_of_nonneg hx0 16
  have hlo : 0 ≤ expLower16 x := by
    unfold expLower16
    positivity
  rw [show (4 : ℝ) * x = (4 : ℕ) * x by norm_num, Real.exp_nat_mul]
  exact hcalc.trans_le (pow_le_pow_left₀ hlo hle 4)

private lemma exp_four_upper (x b : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hcalc : (expUpper16 x) ^ 4 < b) :
    Real.exp (4 * x) < b := by
  have hle : Real.exp x ≤ expUpper16 x := by
    convert Real.exp_bound' hx0 hx1 (by norm_num : 0 < 16) using 1 <;>
      norm_num [expUpper16, expLower16]
  rw [show (4 : ℝ) * x = (4 : ℕ) * x by norm_num, Real.exp_nat_mul]
  exact (pow_le_pow_left₀ (Real.exp_nonneg x) hle 4).trans_lt hcalc

private lemma tanh_eq_exp_two (x : ℝ) :
    Real.tanh x = (Real.exp (2 * x) - 1) / (Real.exp (2 * x) + 1) := by
  rw [Real.tanh_eq, Real.exp_neg]
  have he : Real.exp x ≠ 0 := Real.exp_ne_zero x
  have htwo : Real.exp (2 * x) = Real.exp x ^ 2 := by
    rw [show 2 * x = x + x by ring, Real.exp_add]
    ring
  rw [div_eq_iff]
  · field_simp [he]
    rw [htwo]
  · positivity

private lemma f_neg_of_exp_lt (x : ℝ) (hx : 1 < x)
    (he : Real.exp (2 * x) < (x + 1) / (x - 1)) :
    f x < 0 := by
  unfold f
  rw [tanh_eq_exp_two, sub_lt_zero]
  have hE : 0 < Real.exp (2 * x) := Real.exp_pos _
  have hx0 : 0 < x := by linarith
  rw [div_lt_div_iff₀ (by positivity) hx0]
  have h := (lt_div_iff₀ (by linarith : 0 < x - 1)).mp he
  nlinarith

private lemma f_pos_of_exp_gt (x : ℝ) (hx : 1 < x)
    (he : (x + 1) / (x - 1) < Real.exp (2 * x)) :
    0 < f x := by
  unfold f
  rw [sub_pos, tanh_eq_exp_two]
  have hE : 0 < Real.exp (2 * x) := Real.exp_pos _
  have hx0 : 0 < x := by linarith
  rw [div_lt_div_iff₀ hx0 (by positivity)]
  have h := (div_lt_iff₀ (by linarith : 0 < x - 1)).mp he
  nlinarith

private lemma exp_two_lower : (7389 / 1000 : ℝ) < Real.exp 2 := by
  convert exp_four_lower (1 / 2) (7389 / 1000) (by norm_num) (by
    norm_num [expLower16, Finset.sum_range_succ, Nat.factorial]
    ) using 1 <;> norm_num

private lemma exp_two_upper : Real.exp (2 : ℝ) < 739 / 100 := by
  convert exp_four_upper (1 / 2) (739 / 100) (by norm_num) (by norm_num) (by
    norm_num [expUpper16, expLower16, Finset.sum_range_succ, Nat.factorial]
    ) using 1 <;> norm_num

private lemma exp_four_lower_num : (5459 / 100 : ℝ) < Real.exp 4 := by
  convert exp_four_lower 1 (5459 / 100) (by norm_num) (by
    norm_num [expLower16, Finset.sum_range_succ, Nat.factorial]
    ) using 1 <;> norm_num

private lemma exp_four_upper_num : Real.exp (4 : ℝ) < 273 / 5 := by
  convert exp_four_upper 1 (273 / 5) (by norm_num) (by norm_num) (by
    norm_num [expUpper16, expLower16, Finset.sum_range_succ, Nat.factorial]
    ) using 1 <;> norm_num

private lemma f_one_approx : Approx (f 1) (-0.2384) (1 / 10000) := by
  unfold Approx
  have hf : f 1 = -2 / (Real.exp 2 + 1) := by
    unfold f
    rw [tanh_eq_exp_two]
    norm_num
    field_simp [ne_of_gt (by positivity : 0 < Real.exp 2 + 1)]
    ring
  rw [hf, abs_lt]
  have hd : 0 < Real.exp 2 + 1 := by positivity
  constructor
  · rw [lt_sub_iff_add_lt]
    apply (lt_div_iff₀ hd).2
    nlinarith [exp_two_lower]
  · rw [sub_lt_iff_lt_add]
    apply (div_lt_iff₀ hd).2
    nlinarith [exp_two_upper]

private lemma f_two_approx : Approx (f 2) 0.4640 (1 / 10000) := by
  unfold Approx
  have hf : f 2 = (Real.exp 4 - 3) / (2 * (Real.exp 4 + 1)) := by
    unfold f
    rw [tanh_eq_exp_two]
    norm_num
    field_simp [ne_of_gt (by positivity : 0 < Real.exp 4 + 1)]
    ring
  rw [hf, abs_lt]
  have hd : 0 < 2 * (Real.exp 4 + 1) := by positivity
  constructor
  · rw [lt_sub_iff_add_lt]
    apply (lt_div_iff₀ hd).2
    nlinarith [exp_four_lower_num]
  · rw [sub_lt_iff_lt_add]
    apply (div_lt_iff₀ hd).2
    nlinarith [exp_four_upper_num]

private lemma f_one_neg : f 1 < 0 := by
  have h := (abs_lt.mp f_one_approx).2
  unfold Approx at h
  norm_num at h ⊢
  linarith

private lemma f_two_pos : 0 < f 2 := by
  have h := (abs_lt.mp f_two_approx).1
  unfold Approx at h
  norm_num at h ⊢
  linarith

private lemma continuousOn_f_pos : ContinuousOn f (Set.Ioi 0) := by
  intro x hx
  unfold f
  have hx0 : x ≠ 0 := ne_of_gt hx
  convert ((tanh_hasDerivAt x).continuousAt.sub
    (continuousAt_const.div continuousAt_id hx0)).continuousWithinAt using 1 <;>
      simp [id]

private lemma f_deriv_pos (x : ℝ) (hx : 0 < x) : 0 < deriv f x := by
  unfold f
  have hinv : HasDerivAt (fun y : ℝ => 1 / y) (-1 / x ^ 2) x := by
    convert (hasDerivAt_const x (1 : ℝ)).div (hasDerivAt_id x) hx.ne' using 1 <;>
      simp [id] <;> field_simp [hx.ne'] <;> ring
  rw [show deriv (fun y => Real.tanh y - 1 / y) x =
      1 / (Real.cosh x) ^ 2 - (-1 / x ^ 2) by
    exact ((tanh_hasDerivAt x).sub hinv).deriv]
  have hc : 0 < (Real.cosh x) ^ 2 := sq_pos_of_pos (Real.cosh_pos x)
  have hx2 : 0 < x ^ 2 := sq_pos_of_pos hx
  have hc' : 0 < 1 / (Real.cosh x) ^ 2 := one_div_pos.mpr hc
  have hx2' : 0 < 1 / x ^ 2 := one_div_pos.mpr hx2
  simpa [neg_div] using add_pos hc' hx2'

private lemma strictMonoOn_f_pos : StrictMonoOn f (Set.Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0) continuousOn_f_pos
  intro x hx
  apply f_deriv_pos x
  simpa only [interior_Ioi] using hx

private lemma exists_unique_f_root :
    ∃ r : ℝ, r ∈ Set.Ioo (1 : ℝ) 2 ∧ f r = 0 ∧
      ∀ x : ℝ, 0 < x → f x = 0 → x = r := by
  have hc : ContinuousOn f (Set.Icc (1 : ℝ) 2) :=
    continuousOn_f_pos.mono (by intro x hx; exact lt_of_lt_of_le (by norm_num) hx.1)
  have hz : (0 : ℝ) ∈ Set.Icc (f 1) (f 2) := ⟨f_one_neg.le, f_two_pos.le⟩
  rcases intermediate_value_Icc (by norm_num : (1 : ℝ) ≤ 2) hc hz with
    ⟨r, hrIcc, hr0⟩
  have hr1 : r ≠ 1 := by
    intro h
    subst r
    exact f_one_neg.ne hr0
  have hr2 : r ≠ 2 := by
    intro h
    subst r
    exact f_two_pos.ne' hr0
  have hrIoo : r ∈ Set.Ioo (1 : ℝ) 2 :=
    ⟨lt_of_le_of_ne hrIcc.1 (Ne.symm hr1), lt_of_le_of_ne hrIcc.2 hr2⟩
  refine ⟨r, hrIoo, hr0, ?_⟩
  intro x hx hx0
  exact strictMonoOn_f_pos.injOn hx (lt_trans (by norm_num) hrIoo.1) (hx0.trans hr0.symm)

private lemma f_at_1168_neg : f 1.168 < 0 := by
  apply f_neg_of_exp_lt 1.168 (by norm_num)
  convert exp_four_upper (1.168 / 2) ((1.168 + 1) / (1.168 - 1))
      (by norm_num) (by norm_num) (by
        norm_num [expUpper16, expLower16, Finset.sum_range_succ, Nat.factorial]
      ) using 1 <;> norm_num

private lemma f_at_1339_pos : 0 < f 1.339 := by
  apply f_pos_of_exp_gt 1.339 (by norm_num)
  convert exp_four_lower (1.339 / 2) ((1.339 + 1) / (1.339 - 1))
      (by norm_num) (by
        norm_num [expLower16, Finset.sum_range_succ, Nat.factorial]
      ) using 1 <;> norm_num

private lemma f_at_11989_neg : f 1.1989 < 0 := by
  apply f_neg_of_exp_lt 1.1989 (by norm_num)
  convert exp_four_upper (1.1989 / 2) ((1.1989 + 1) / (1.1989 - 1))
      (by norm_num) (by norm_num) (by
        norm_num [expUpper16, expLower16, Finset.sum_range_succ, Nat.factorial]
      ) using 1 <;> norm_num

private lemma f_at_12032_pos : 0 < f 1.2032 := by
  apply f_pos_of_exp_gt 1.2032 (by norm_num)
  convert exp_four_lower (1.2032 / 2) ((1.2032 + 1) / (1.2032 - 1))
      (by norm_num) (by
        norm_num [expLower16, Finset.sum_range_succ, Nat.factorial]
      ) using 1 <;> norm_num

private lemma f_at_11996781_neg : f 1.1996781 < 0 := by
  apply f_neg_of_exp_lt 1.1996781 (by norm_num)
  convert exp_four_upper (1.1996781 / 2) ((1.1996781 + 1) / (1.1996781 - 1))
      (by norm_num) (by norm_num) (by
        norm_num [expUpper16, expLower16, Finset.sum_range_succ, Nat.factorial]
      ) using 1 <;> norm_num

private lemma f_at_11996796_pos : 0 < f 1.1996796 := by
  apply f_pos_of_exp_gt 1.1996796 (by norm_num)
  convert exp_four_lower (1.1996796 / 2) ((1.1996796 + 1) / (1.1996796 - 1))
      (by norm_num) (by
        norm_num [expLower16, Finset.sum_range_succ, Nat.factorial]
      ) using 1 <;> norm_num

private lemma f_at_1199677_neg : f 1.199677 < 0 := by
  apply f_neg_of_exp_lt 1.199677 (by norm_num)
  convert exp_four_upper (1.199677 / 2) ((1.199677 + 1) / (1.199677 - 1))
      (by norm_num) (by norm_num) (by
        norm_num [expUpper16, expLower16, Finset.sum_range_succ, Nat.factorial]
      ) using 1 <;> norm_num

private lemma f_at_1199679_pos : 0 < f 1.199679 := by
  apply f_pos_of_exp_gt 1.199679 (by norm_num)
  convert exp_four_lower (1.199679 / 2) ((1.199679 + 1) / (1.199679 - 1))
      (by norm_num) (by
        norm_num [expLower16, Finset.sum_range_succ, Nat.factorial]
      ) using 1 <;> norm_num

private lemma equation_iff_f_eq_zero {x : ℝ} (hx : x ≠ 0) :
    equation x ↔ f x = 0 := by
  unfold equation f
  rw [sub_eq_zero, eq_div_iff hx]
  simp only [mul_comm]

private lemma equation_neg_iff (x : ℝ) : equation (-x) ↔ equation x := by
  unfold equation
  rw [Real.tanh_neg]
  constructor <;> intro h
  · nlinarith
  · nlinarith

private lemma exists_classified_root :
    ∃ r : ℝ, r ∈ Set.Ioo (1 : ℝ) 2 ∧ equation r ∧
      ∀ x : ℝ, equation x ↔ x = -r ∨ x = r := by
  rcases exists_unique_f_root with ⟨r, hrIoo, hfr, huniq⟩
  have hrpos : 0 < r := lt_trans (by norm_num) hrIoo.1
  have hreq : equation r := (equation_iff_f_eq_zero hrpos.ne').2 hfr
  refine ⟨r, hrIoo, hreq, ?_⟩
  intro x
  constructor
  · intro hx
    have hxne : x ≠ 0 := by
      intro h
      subst x
      norm_num [equation] at hx
    rcases lt_or_gt_of_ne hxne with hxneg | hxpos
    · left
      have hnegEq : equation (-x) := (equation_neg_iff x).2 hx
      have hnegF : f (-x) = 0 :=
        (equation_iff_f_eq_zero (by linarith : -x ≠ 0)).1 hnegEq
      have hxr := huniq (-x) (by linarith) hnegF
      linarith
    · right
      exact huniq x hxpos ((equation_iff_f_eq_zero hxne).1 hx)
  · rintro (rfl | rfl)
    · exact (equation_neg_iff r).2 hreq
    · exact hreq

private lemma root_gt_of_f_neg {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hfa : f a < 0) (hfr : f r = 0) : a < r := by
  apply (strictMonoOn_f_pos.lt_iff_lt ha hr).mp
  linarith

private lemma root_lt_of_f_pos {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hfa : 0 < f a) (hfr : f r = 0) : r < a := by
  apply (strictMonoOn_f_pos.lt_iff_lt hr ha).mp
  linarith

theorem gap1 :
    ∃ ξ : ℝ, ξ ∈ Set.Ioo (1 : ℝ) 2 ∧ equation ξ ∧
      (∀ x : ℝ, equation x ↔ x = -ξ ∨ x = ξ) := by
  exact exists_classified_root
theorem gap2 (x : ℝ) (hx : x ≠ 0) :
    deriv f x = 1 / (Real.cosh x) ^ 2 + 1 / x ^ 2 := by
  unfold f
  have hinv : HasDerivAt (fun y : ℝ => 1 / y) (-1 / x ^ 2) x := by
    convert (hasDerivAt_const x (1 : ℝ)).div (hasDerivAt_id x) hx using 1 <;>
      simp [id] <;> field_simp [hx] <;> ring
  convert (tanh_hasDerivAt x).sub hinv |>.deriv using 1 <;> ring
theorem gap3 (x : ℝ) (hx : x ≠ 0) :
    1 / (Real.cosh x) ^ 2 + 1 / x ^ 2 > 0 := by
  have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  have hc2 : 0 < (Real.cosh x) ^ 2 := sq_pos_of_pos (Real.cosh_pos x)
  positivity
theorem gap4 (x : ℝ) (hx : x ≠ 0) :
    deriv f x > 0 := by rw [gap2 x hx]; exact gap3 x hx
theorem gap5 : Approx (f 1) (-0.2384) (1 / 10000) := by
  exact f_one_approx
theorem gap6 : Approx (f 2) 0.4640 (1 / 10000) := by
  exact f_two_approx
theorem gap7 :
    ∃! ξ : ℝ, ξ ∈ Set.Ioo (1 : ℝ) 2 ∧ f ξ = 0 := by
  rcases exists_unique_f_root with ⟨r, hr, hfr, huniq⟩
  refine ⟨r, ⟨hr, hfr⟩, ?_⟩
  intro y hy
  exact huniq y (lt_trans (by norm_num) hy.1.1) hy.2
theorem gap8 (x : ℝ) (hx : x ≠ 0) :
    deriv (deriv f) x =
      -(2 * Real.sinh x / (Real.cosh x) ^ 3) - 2 / x ^ 3 := by
  have hlocal : deriv f =ᶠ[nhds x]
      fun y => 1 / (Real.cosh y) ^ 2 + 1 / y ^ 2 := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact gap2 y hy
  rw [hlocal.deriv_eq]
  have hc : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  have hfirst : HasDerivAt (fun y : ℝ => 1 / (Real.cosh y) ^ 2)
      (-(2 * Real.sinh x / (Real.cosh x) ^ 3)) x := by
    convert (hasDerivAt_const x (1 : ℝ)).div ((Real.hasDerivAt_cosh x).pow 2)
      (pow_ne_zero 2 hc) using 1 <;> simp [Pi.pow_apply] <;>
        field_simp [hc] <;> ring
  have hsecond : HasDerivAt (fun y : ℝ => 1 / y ^ 2) (-2 / x ^ 3) x := by
    convert (hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 2)
      (pow_ne_zero 2 hx) using 1 <;> simp [id] <;> field_simp [hx] <;> ring
  change deriv ((fun y : ℝ => 1 / (Real.cosh y) ^ 2) +
    fun y => 1 / y ^ 2) x = _
  convert (hfirst.add hsecond).deriv using 1 <;> ring
theorem gap9 (x : ℝ) (hx : 0 < x) :
    -(2 * Real.sinh x / (Real.cosh x) ^ 3) - 2 / x ^ 3 < 0 := by
  have hs : 0 < Real.sinh x := (Real.sinh_pos_iff).2 hx
  have hc : 0 < Real.cosh x := Real.cosh_pos x
  have h₁ : 0 < 2 * Real.sinh x / (Real.cosh x) ^ 3 := by positivity
  have h₂ : 0 < 2 / x ^ 3 := by positivity
  linarith
theorem gap10 (x : ℝ) (hx : 0 < x) :
    deriv (deriv f) x < 0 := by
  rw [gap8 x hx.ne']
  exact gap9 x hx
theorem gap11 : upperApproximant 1 = 1.339 := by rfl
theorem gap12 : lowerApproximant 1 = 1.168 := by rfl
theorem gap13 :
    ∃ ξ : ℝ, equation ξ ∧ 1.168 < ξ := by
  rcases exists_unique_f_root with ⟨r, hr, hfr, _⟩
  have hrpos : 0 < r := lt_trans (by norm_num) hr.1
  exact ⟨r, (equation_iff_f_eq_zero hrpos.ne').2 hfr,
    root_gt_of_f_neg (by norm_num) hrpos f_at_1168_neg hfr⟩
theorem gap14 :
    ∃ ξ : ℝ, equation ξ ∧ ξ < 1.339 := by
  rcases exists_unique_f_root with ⟨r, hr, hfr, _⟩
  have hrpos : 0 < r := lt_trans (by norm_num) hr.1
  exact ⟨r, (equation_iff_f_eq_zero hrpos.ne').2 hfr,
    root_lt_of_f_pos (by norm_num) hrpos f_at_1339_pos hfr⟩
theorem gap15 : (1.168 : ℝ) < 1.339 := by norm_num
theorem gap16 : upperApproximant 2 = 1.2032 := by rfl
theorem gap17 : lowerApproximant 2 = 1.1989 := by rfl
theorem gap18 :
    ∃ ξ : ℝ, equation ξ ∧ 1.1989 < ξ := by
  rcases exists_unique_f_root with ⟨r, hr, hfr, _⟩
  have hrpos : 0 < r := lt_trans (by norm_num) hr.1
  exact ⟨r, (equation_iff_f_eq_zero hrpos.ne').2 hfr,
    root_gt_of_f_neg (by norm_num) hrpos f_at_11989_neg hfr⟩
theorem gap19 :
    ∃ ξ : ℝ, equation ξ ∧ ξ < 1.2032 := by
  rcases exists_unique_f_root with ⟨r, hr, hfr, _⟩
  have hrpos : 0 < r := lt_trans (by norm_num) hr.1
  exact ⟨r, (equation_iff_f_eq_zero hrpos.ne').2 hfr,
    root_lt_of_f_pos (by norm_num) hrpos f_at_12032_pos hfr⟩
theorem gap20 : (1.1989 : ℝ) < 1.2032 := by norm_num
theorem gap21 : upperApproximant 3 = 1.1996796 := by rfl
theorem gap22 : lowerApproximant 3 = 1.1996781 := by rfl
theorem gap23 :
    ∃ ξ : ℝ, equation ξ ∧ 1.1996781 < ξ := by
  rcases exists_unique_f_root with ⟨r, hr, hfr, _⟩
  have hrpos : 0 < r := lt_trans (by norm_num) hr.1
  exact ⟨r, (equation_iff_f_eq_zero hrpos.ne').2 hfr,
    root_gt_of_f_neg (by norm_num) hrpos f_at_11996781_neg hfr⟩
theorem gap24 :
    ∃ ξ : ℝ, equation ξ ∧ ξ < 1.1996796 := by
  rcases exists_unique_f_root with ⟨r, hr, hfr, _⟩
  have hrpos : 0 < r := lt_trans (by norm_num) hr.1
  exact ⟨r, (equation_iff_f_eq_zero hrpos.ne').2 hfr,
    root_lt_of_f_pos (by norm_num) hrpos f_at_11996796_pos hfr⟩
theorem gap25 : (1.1996781 : ℝ) < 1.1996796 := by norm_num
theorem gap26 : ApproxRootSet reportedRoots (1 / 1000000) := by
  rcases exists_classified_root with ⟨r, hr, hreq, hclass⟩
  have hrpos : 0 < r := lt_trans (by norm_num) hr.1
  have hfr : f r = 0 := (equation_iff_f_eq_zero hrpos.ne').1 hreq
  have hlo : (1.199677 : ℝ) < r :=
    root_gt_of_f_neg (by norm_num) hrpos f_at_1199677_neg hfr
  have hhi : r < (1.199679 : ℝ) :=
    root_lt_of_f_pos (by norm_num) hrpos f_at_1199679_pos hfr
  have hnear : |r - 1.199678| < (1 / 1000000 : ℝ) := by
    rw [abs_lt]
    constructor <;> norm_num <;> linarith
  have hnegEq : equation (-r) := (equation_neg_iff r).2 hreq
  unfold ApproxRootSet
  constructor
  · intro s hs
    simp only [reportedRoots, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · refine ⟨-r, hnegEq, ?_⟩
      rw [show (-1.199678 : ℝ) - -r = r - 1.199678 by ring]
      exact hnear
    · exact ⟨r, hreq, by simpa [abs_sub_comm] using hnear⟩
  · intro x hx
    rcases (hclass x).1 hx with rfl | rfl
    · refine ⟨-1.199678, ?_, ?_⟩
      · simp [reportedRoots]
      · rw [show (-r : ℝ) - -1.199678 = -(r - 1.199678) by ring, abs_neg]
        exact hnear
    · refine ⟨1.199678, ?_, ?_⟩
      · simp [reportedRoots]
      · exact hnear

end
end ProofGap.Exercise1625

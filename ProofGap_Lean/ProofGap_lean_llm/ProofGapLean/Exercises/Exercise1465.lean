import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Order.Filter.AtTopBot.Defs

namespace ProofGap.Exercise1465

noncomputable section

open Filter

def f (a x : ℝ) : ℝ := x ^ 5 - 5 * x - a

def UniqueRootOn (u : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∃ x ∈ s, u x = 0 ∧ ∀ y ∈ s, u y = 0 → y = x

theorem gap1 (a x : ℝ) :
    deriv (f a) x = 5 * x ^ 4 - 5 := by
  simpa [f] using
    ((((hasDerivAt_id x).pow 5).sub
      ((hasDerivAt_const x 5).mul (hasDerivAt_id x))).sub
      (hasDerivAt_const x a)).deriv

theorem gap2 (a x : ℝ) (hzero : deriv (f a) x = 0) :
    x = -1 ∨ x = 1 := by
  rw [gap1] at hzero
  have hx4 : x ^ 4 = 1 := by
    linarith
  have hx2 : x ^ 2 = 1 := by
    nlinarith [sq_nonneg (x ^ 2 - 1)]
  have hfac : (x - 1) * (x + 1) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfac with h | h
  · right
    linarith
  · left
    linarith

theorem gap3 (a : ℝ) :
    Tendsto (f a) atBot atBot := by
  refine tendsto_atBot.2 ?_
  intro b
  filter_upwards [eventually_le_atBot (min (-2) (b + a))] with x hx
  have hxneg : x ≤ -2 := le_trans hx (min_le_left _ _)
  have hxba : x ≤ b + a := le_trans hx (min_le_right _ _)
  have hx0 : x ≤ 0 := by linarith
  have hx2 : 4 ≤ x ^ 2 := by nlinarith
  have hx4 : 6 ≤ x ^ 4 := by
    nlinarith [sq_nonneg (x ^ 2 - 4)]
  have hmul := mul_le_mul_of_nonpos_right hx4 hx0
  dsimp [f]
  nlinarith [hmul]

theorem gap4 (a : ℝ) :
    Tendsto (f a) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro b
  filter_upwards [eventually_ge_atTop (max 2 (b + a))] with x hx
  have hxpos : 2 ≤ x := le_trans (le_max_left _ _) hx
  have hxba : b + a ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 ≤ x := by linarith
  have hx2 : 4 ≤ x ^ 2 := by nlinarith
  have hx4 : 6 ≤ x ^ 4 := by
    nlinarith [sq_nonneg (x ^ 2 - 4)]
  have hmul := mul_le_mul_of_nonneg_right hx4 hx0
  dsimp [f]
  nlinarith [hmul]

theorem gap5 (a x : ℝ) (hx : x < -1) :
    deriv (f a) x > 0 := by
  rw [gap1]
  have hx2 : 1 < x ^ 2 := by
    nlinarith [sq_nonneg (x + 1)]
  have hx4 : 1 < x ^ 4 := by
    nlinarith [sq_nonneg (x ^ 2 - 1)]
  nlinarith

theorem gap6 (a x : ℝ) (hx : 1 < x) :
    deriv (f a) x > 0 := by
  rw [gap1]
  have hx2 : 1 < x ^ 2 := by
    nlinarith [sq_nonneg (x - 1)]
  have hx4 : 1 < x ^ 4 := by
    nlinarith [sq_nonneg (x ^ 2 - 1)]
  nlinarith

theorem gap7 (a x : ℝ) (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    deriv (f a) x < 0 := by
  rw [gap1]
  have hprod : 0 < (1 - x) * (1 + x) := by
    exact mul_pos (by linarith [hx.2]) (by linarith [hx.1])
  have hx2 : x ^ 2 < 1 := by
    nlinarith
  have hprod2 : 0 < (1 - x ^ 2) * (1 + x ^ 2) := by
    apply mul_pos
    · linarith
    · nlinarith [sq_nonneg x]
  have hx4 : x ^ 4 < 1 := by
    nlinarith
  nlinarith

theorem gap8 (a : ℝ) :
    f a (-1) = 4 - a := by
  norm_num [f]

theorem gap9 (a : ℝ) :
    f a 1 = -4 - a := by
  norm_num [f]

theorem gap10 (a : ℝ) (ha : a < -4) :
    f a (-1) > 0 := by
  rw [gap8]
  linarith

theorem gap11 (a : ℝ) (ha : a < -4) :
    f a 1 > 0 := by
  rw [gap9]
  linarith

theorem gap12 (a : ℝ) (ha : a < -4) :
    UniqueRootOn (f a) (Set.Iio (-1)) := by
  have hev1 : ∀ᶠ x in atBot, f a x ≤ -1 :=
    (gap3 a) (eventually_le_atBot (-1))
  have hev2 : ∀ᶠ x : ℝ in atBot, x ≤ -2 := eventually_le_atBot (-2 : ℝ)
  have hev : ∀ᶠ x : ℝ in atBot, f a x ≤ -1 ∧ x ≤ -2 := by
    filter_upwards [hev1, hev2] with x hfx hx
    exact ⟨hfx, hx⟩
  rcases hev.exists with ⟨l, hfl, hl⟩
  have hlneg : f a l < 0 := by linarith
  have hrpos : 0 < f a (-1) := gap10 a ha
  have hcont : Continuous (f a) := by
    unfold f
    fun_prop
  have hdiff : Differentiable ℝ (f a) := by
    unfold f
    fun_prop
  have hzmem : 0 ∈ Set.Icc (f a l) (f a (-1)) := ⟨le_of_lt hlneg, le_of_lt hrpos⟩
  rcases intermediate_value_Icc (show l ≤ -1 by linarith) hcont.continuousOn hzmem with
    ⟨x, hx, hzero⟩
  have hxmem : x ∈ Set.Iio (-1) := by
    have hxne : x ≠ -1 := by
      intro heq
      subst x
      linarith
    exact lt_of_le_of_ne hx.2 hxne
  change x < (-1 : ℝ) at hxmem
  refine ⟨x, hxmem, hzero, ?_⟩
  intro y hy hyzero
  change y < (-1 : ℝ) at hy
  by_contra hne
  rcases lt_or_gt_of_ne hne with hyx | hxy
  · rcases exists_deriv_eq_slope (f a) hyx hcont.continuousOn hdiff.differentiableOn with
      ⟨c, hc, hder⟩
    have hc0 : deriv (f a) c = 0 := by
      rw [hder]
      simp [hyzero, hzero]
    rcases gap2 a c hc0 with hcval | hcval
    · subst c
      linarith [hc.2, hxmem]
    · subst c
      linarith [hc.2, hxmem]
  · rcases exists_deriv_eq_slope (f a) hxy hcont.continuousOn hdiff.differentiableOn with
      ⟨c, hc, hder⟩
    have hc0 : deriv (f a) c = 0 := by
      rw [hder]
      simp [hyzero, hzero]
    rcases gap2 a c hc0 with hcval | hcval
    · subst c
      linarith [hc.2, hy]
    · subst c
      linarith [hc.2, hy]

theorem gap13 (a : ℝ) (hl : -4 < a) (hu : a < 4) :
    f a (-1) > 0 := by
  rw [gap8]
  linarith

theorem gap14 (a : ℝ) (hl : -4 < a) (hu : a < 4) :
    f a 1 < 0 := by
  rw [gap9]
  linarith

theorem gap15 (a : ℝ) (hl : -4 < a) (hu : a < 4) :
    UniqueRootOn (f a) (Set.Iio (-1)) := by
  have hev1 : ∀ᶠ x in atBot, f a x ≤ -1 :=
    (gap3 a) (eventually_le_atBot (-1))
  have hev2 : ∀ᶠ x : ℝ in atBot, x ≤ -2 := eventually_le_atBot (-2 : ℝ)
  have hev : ∀ᶠ x : ℝ in atBot, f a x ≤ -1 ∧ x ≤ -2 := by
    filter_upwards [hev1, hev2] with x hfx hx
    exact ⟨hfx, hx⟩
  rcases hev.exists with ⟨l, hfl, hle⟩
  have hlneg : f a l < 0 := by linarith
  have hrpos : 0 < f a (-1) := gap13 a hl hu
  have hcont : Continuous (f a) := by
    unfold f
    fun_prop
  have hdiff : Differentiable ℝ (f a) := by
    unfold f
    fun_prop
  have hzmem : 0 ∈ Set.Icc (f a l) (f a (-1)) := ⟨le_of_lt hlneg, le_of_lt hrpos⟩
  rcases intermediate_value_Icc (show l ≤ -1 by linarith) hcont.continuousOn hzmem with
    ⟨x, hx, hzero⟩
  have hxmem : x ∈ Set.Iio (-1) := by
    have hxne : x ≠ -1 := by
      intro heq
      subst x
      linarith
    exact lt_of_le_of_ne hx.2 hxne
  change x < (-1 : ℝ) at hxmem
  refine ⟨x, hxmem, hzero, ?_⟩
  intro y hy hyzero
  change y < (-1 : ℝ) at hy
  by_contra hne
  rcases lt_or_gt_of_ne hne with hyx | hxy
  · rcases exists_deriv_eq_slope (f a) hyx hcont.continuousOn hdiff.differentiableOn with
      ⟨c, hc, hder⟩
    have hc0 : deriv (f a) c = 0 := by
      rw [hder]
      simp [hyzero, hzero]
    rcases gap2 a c hc0 with hcval | hcval
    · subst c
      linarith [hc.2, hxmem]
    · subst c
      linarith [hc.2, hxmem]
  · rcases exists_deriv_eq_slope (f a) hxy hcont.continuousOn hdiff.differentiableOn with
      ⟨c, hc, hder⟩
    have hc0 : deriv (f a) c = 0 := by
      rw [hder]
      simp [hyzero, hzero]
    rcases gap2 a c hc0 with hcval | hcval
    · subst c
      linarith [hc.2, hy]
    · subst c
      linarith [hc.2, hy]

theorem gap16 (a : ℝ) (hl : -4 < a) (hu : a < 4) :
    UniqueRootOn (f a) (Set.Ioo (-1) 1) := by
  have hlpos : 0 < f a (-1) := gap13 a hl hu
  have hrneg : f a 1 < 0 := gap14 a hl hu
  have hcont : Continuous (f a) := by
    unfold f
    fun_prop
  have hdiff : Differentiable ℝ (f a) := by
    unfold f
    fun_prop
  have hzmem : 0 ∈ Set.Icc (f a 1) (f a (-1)) := ⟨le_of_lt hrneg, le_of_lt hlpos⟩
  rcases intermediate_value_Icc' (show (-1 : ℝ) ≤ 1 by norm_num)
      hcont.continuousOn hzmem with ⟨x, hx, hzero⟩
  have hxleft : -1 < x := by
    have hxne : x ≠ -1 := by
      intro heq
      subst x
      linarith
    exact lt_of_le_of_ne hx.1 (Ne.symm hxne)
  have hxright : x < 1 := by
    have hxne : x ≠ 1 := by
      intro heq
      subst x
      linarith
    exact lt_of_le_of_ne hx.2 hxne
  have hxmem : x ∈ Set.Ioo (-1) 1 := ⟨hxleft, hxright⟩
  refine ⟨x, hxmem, hzero, ?_⟩
  intro y hy hyzero
  by_contra hne
  rcases lt_or_gt_of_ne hne with hyx | hxy
  · rcases exists_deriv_eq_slope (f a) hyx hcont.continuousOn hdiff.differentiableOn with
      ⟨c, hc, hder⟩
    have hc0 : deriv (f a) c = 0 := by
      rw [hder]
      simp [slope, hyzero, hzero]
    rcases gap2 a c hc0 with hcval | hcval
    · subst c
      linarith [hc.1, hy.1]
    · subst c
      linarith [hc.2, hxmem.2]
  · rcases exists_deriv_eq_slope (f a) hxy hcont.continuousOn hdiff.differentiableOn with
      ⟨c, hc, hder⟩
    have hc0 : deriv (f a) c = 0 := by
      rw [hder]
      simp [slope, hyzero, hzero]
    rcases gap2 a c hc0 with hcval | hcval
    · subst c
      linarith [hc.1, hxmem.1]
    · subst c
      linarith [hc.2, hy.2]

theorem gap17 (a : ℝ) (hl : -4 < a) (hu : a < 4) :
    UniqueRootOn (f a) (Set.Ioi 1) := by
  have hev1 : ∀ᶠ x in atTop, 1 ≤ f a x :=
    (gap4 a) (eventually_ge_atTop 1)
  have hev2 : ∀ᶠ x : ℝ in atTop, 2 ≤ x := eventually_ge_atTop (2 : ℝ)
  have hev : ∀ᶠ x : ℝ in atTop, 1 ≤ f a x ∧ 2 ≤ x := by
    filter_upwards [hev1, hev2] with x hfx hx
    exact ⟨hfx, hx⟩
  rcases hev.exists with ⟨r, hfr, hre⟩
  have hlneg : f a 1 < 0 := gap14 a hl hu
  have hrpos : 0 < f a r := by linarith
  have hcont : Continuous (f a) := by
    unfold f
    fun_prop
  have hdiff : Differentiable ℝ (f a) := by
    unfold f
    fun_prop
  have hzmem : 0 ∈ Set.Icc (f a 1) (f a r) := ⟨le_of_lt hlneg, le_of_lt hrpos⟩
  rcases intermediate_value_Icc (show (1 : ℝ) ≤ r by linarith)
      hcont.continuousOn hzmem with ⟨x, hx, hzero⟩
  have hxmem : x ∈ Set.Ioi 1 := by
    have hxne : x ≠ 1 := by
      intro heq
      subst x
      linarith
    exact lt_of_le_of_ne hx.1 (Ne.symm hxne)
  change (1 : ℝ) < x at hxmem
  refine ⟨x, hxmem, hzero, ?_⟩
  intro y hy hyzero
  change (1 : ℝ) < y at hy
  by_contra hne
  rcases lt_or_gt_of_ne hne with hyx | hxy
  · rcases exists_deriv_eq_slope (f a) hyx hcont.continuousOn hdiff.differentiableOn with
      ⟨c, hc, hder⟩
    have hc0 : deriv (f a) c = 0 := by
      rw [hder]
      simp [hyzero, hzero]
    rcases gap2 a c hc0 with hcval | hcval
    · subst c
      linarith [hc.1, hy]
    · subst c
      linarith [hc.1, hy]
  · rcases exists_deriv_eq_slope (f a) hxy hcont.continuousOn hdiff.differentiableOn with
      ⟨c, hc, hder⟩
    have hc0 : deriv (f a) c = 0 := by
      rw [hder]
      simp [hyzero, hzero]
    rcases gap2 a c hc0 with hcval | hcval
    · subst c
      linarith [hc.1, hxmem]
    · subst c
      linarith [hc.1, hxmem]

theorem gap18 (a : ℝ) (ha : 4 < a) :
    f a (-1) < 0 := by
  rw [gap8]
  linarith

theorem gap19 (a : ℝ) (ha : 4 < a) :
    f a 1 < 0 := by
  rw [gap9]
  linarith

theorem gap20 (a : ℝ) (ha : 4 < a) :
    UniqueRootOn (f a) (Set.Ioi 1) := by
  have hev1 : ∀ᶠ x in atTop, 1 ≤ f a x :=
    (gap4 a) (eventually_ge_atTop 1)
  have hev2 : ∀ᶠ x : ℝ in atTop, 2 ≤ x := eventually_ge_atTop (2 : ℝ)
  have hev : ∀ᶠ x : ℝ in atTop, 1 ≤ f a x ∧ 2 ≤ x := by
    filter_upwards [hev1, hev2] with x hfx hx
    exact ⟨hfx, hx⟩
  rcases hev.exists with ⟨r, hfr, hre⟩
  have hlneg : f a 1 < 0 := gap19 a ha
  have hrpos : 0 < f a r := by linarith
  have hcont : Continuous (f a) := by
    unfold f
    fun_prop
  have hdiff : Differentiable ℝ (f a) := by
    unfold f
    fun_prop
  have hzmem : 0 ∈ Set.Icc (f a 1) (f a r) := ⟨le_of_lt hlneg, le_of_lt hrpos⟩
  rcases intermediate_value_Icc (show (1 : ℝ) ≤ r by linarith)
      hcont.continuousOn hzmem with ⟨x, hx, hzero⟩
  have hxmem : x ∈ Set.Ioi 1 := by
    have hxne : x ≠ 1 := by
      intro heq
      subst x
      linarith
    exact lt_of_le_of_ne hx.1 (Ne.symm hxne)
  change (1 : ℝ) < x at hxmem
  refine ⟨x, hxmem, hzero, ?_⟩
  intro y hy hyzero
  change (1 : ℝ) < y at hy
  by_contra hne
  rcases lt_or_gt_of_ne hne with hyx | hxy
  · rcases exists_deriv_eq_slope (f a) hyx hcont.continuousOn hdiff.differentiableOn with
      ⟨c, hc, hder⟩
    have hc0 : deriv (f a) c = 0 := by
      rw [hder]
      simp [hyzero, hzero]
    rcases gap2 a c hc0 with hcval | hcval
    · subst c
      linarith [hc.1, hy]
    · subst c
      linarith [hc.1, hy]
  · rcases exists_deriv_eq_slope (f a) hxy hcont.continuousOn hdiff.differentiableOn with
      ⟨c, hc, hder⟩
    have hc0 : deriv (f a) c = 0 := by
      rw [hder]
      simp [hyzero, hzero]
    rcases gap2 a c hc0 with hcval | hcval
    · subst c
      linarith [hc.1, hxmem]
    · subst c
      linarith [hc.1, hxmem]

theorem gap21 (a x : ℝ) :
    x ∈ {y : ℝ | y ^ 5 - 5 * y = a} ↔ x ^ 5 - 5 * x = a := by
  rfl

end

end ProofGap.Exercise1465

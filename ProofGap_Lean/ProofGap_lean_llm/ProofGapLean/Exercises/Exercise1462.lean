import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Order.Filter.AtTopBot.Defs

namespace ProofGap.Exercise1462

noncomputable section

open Filter

def f (x : ℝ) : ℝ := x ^ 3 - 6 * x ^ 2 + 9 * x - 10

def UniqueRootOn (u : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∃ x ∈ s, u x = 0 ∧ ∀ y ∈ s, u y = 0 → y = x

private lemma f_add_six (x : ℝ) :
    f x + 6 = (x - 1) ^ 2 * (x - 4) := by
  unfold f
  ring

private lemma f_sub_f (y x : ℝ) :
    f y - f x =
      (y - x) * (y ^ 2 + y * x + x ^ 2 - 6 * (y + x) + 9) := by
  unfold f
  ring

private lemma continuous_f : Continuous f := by
  have h3 : Continuous (fun x : ℝ => x ^ 3) := continuous_id.pow 3
  have h6 : Continuous (fun x : ℝ => 6 * x ^ 2) :=
    continuous_const.mul (continuous_id.pow 2)
  have h9 : Continuous (fun x : ℝ => 9 * x) :=
    continuous_const.mul continuous_id
  have h10 : Continuous (fun _ : ℝ => (10 : ℝ)) := continuous_const
  simpa only [f] using ((h3.sub h6).add h9).sub h10

theorem gap1 (x : ℝ) :
    deriv f x = 3 * x ^ 2 - 12 * x + 9 := by
  have hid : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have h2 :
      HasDerivAt (fun y : ℝ => y * y) (1 * x + x * 1) x := by
    exact hid.mul hid
  have h3 :
      HasDerivAt (fun y : ℝ => (y * y) * y)
        ((1 * x + x * 1) * x + (x * x) * 1) x := by
    exact h2.mul hid
  have h6 :
      HasDerivAt (fun y : ℝ => 6 * (y * y))
        (6 * (1 * x + x * 1)) x := by
    exact h2.const_mul 6
  have h9 : HasDerivAt (fun y : ℝ => 9 * y) (9 * 1) x := by
    exact hid.const_mul 9
  have hpoly :
      HasDerivAt
        (fun y : ℝ => (y * y) * y - 6 * (y * y) + 9 * y - 10)
        (((1 * x + x * 1) * x + (x * x) * 1 -
          6 * (1 * x + x * 1)) + 9 * 1) x := by
    exact ((h3.sub h6).add h9).sub_const 10
  have hfun :
      f = fun y : ℝ => (y * y) * y - 6 * (y * y) + 9 * y - 10 := by
    funext y
    unfold f
    ring
  rw [hfun]
  convert hpoly.deriv using 1 <;> ring

theorem gap2 (x : ℝ) (hzero : deriv f x = 0) :
    x = 1 ∨ x = 3 := by
  rw [gap1] at hzero
  have hfac : (x - 1) * (x - 3) = 0 := by
    nlinarith [hzero]
  rcases mul_eq_zero.mp hfac with h | h
  · left
    linarith
  · right
    linarith

theorem gap3 :
    Tendsto f atBot atBot := by
  refine tendsto_atBot.2 ?_
  intro b
  refine (eventually_le_atBot (min 0 ((b + 10) / 9))).mono ?_
  intro x hx
  have hx0 : x ≤ 0 := le_trans hx (min_le_left _ _)
  have hxb : x ≤ (b + 10) / 9 := le_trans hx (min_le_right _ _)
  have hm : x * x ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hx0 (sq_nonneg x)
  have hc : x ^ 3 ≤ 0 := by
    nlinarith [hm]
  unfold f
  nlinarith [hc, sq_nonneg x]

theorem gap4 (x : ℝ) (hx : x < 1) :
    deriv f x > 0 := by
  rw [gap1]
  have hx3 : x < 3 := by
    linarith
  have hp : 0 < (x - 1) * (x - 3) :=
    mul_pos_of_neg_of_neg (sub_neg.mpr hx) (sub_neg.mpr hx3)
  nlinarith [hp]

theorem gap5 :
    f 1 = -6 := by
  norm_num [f]

theorem gap6 :
    (-6 : ℝ) < 0 := by
  norm_num

theorem gap7 :
    ¬ ∃ x ∈ Set.Iio (1 : ℝ), f x = 0 := by
  rintro ⟨x, hx, hzero⟩
  have hx1 : x < 1 := hx
  have hs : 0 ≤ (x - 1) ^ 2 := sq_nonneg (x - 1)
  have hx4 : x - 4 ≤ 0 :=
    sub_nonpos.mpr (le_trans (le_of_lt hx1) (by norm_num))
  have hp : (x - 1) ^ 2 * (x - 4) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hs hx4
  have hid := f_add_six x
  rw [hzero] at hid
  nlinarith [hp]

theorem gap8 (x : ℝ) (hx : x ∈ Set.Ioo (1 : ℝ) 3) :
    deriv f x < 0 := by
  rw [gap1]
  have hp : (x - 1) * (x - 3) < 0 :=
    mul_neg_of_pos_of_neg (sub_pos.mpr hx.1) (sub_neg.mpr hx.2)
  nlinarith [hp]

theorem gap9 :
    f 3 = -10 := by
  norm_num [f]

theorem gap10 :
    (-10 : ℝ) < 0 := by
  norm_num

theorem gap11 :
    ¬ ∃ x ∈ Set.Ioo (1 : ℝ) 3, f x = 0 := by
  rintro ⟨x, hx, hzero⟩
  have hx3 : x < 3 := hx.2
  have hs : 0 ≤ (x - 1) ^ 2 := sq_nonneg (x - 1)
  have hx4 : x - 4 ≤ 0 :=
    sub_nonpos.mpr (le_trans (le_of_lt hx3) (by norm_num))
  have hp : (x - 1) ^ 2 * (x - 4) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hs hx4
  have hid := f_add_six x
  rw [hzero] at hid
  nlinarith [hp]

theorem gap12 (x : ℝ) (hx : 3 < x) :
    deriv f x > 0 := by
  rw [gap1]
  have hp : 0 < (x - 1) * (x - 3) :=
    mul_pos (sub_pos.mpr (by linarith)) (sub_pos.mpr hx)
  nlinarith [hp]

theorem gap13 :
    f 3 = -10 := by
  exact gap9

theorem gap14 :
    (-10 : ℝ) < 0 := by
  exact gap10

theorem gap15 :
    Tendsto f atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro b
  refine (eventually_ge_atTop (max 6 ((b + 10) / 9))).mono ?_
  intro x hx
  have hx6 : 6 ≤ x := le_trans (le_max_left _ _) hx
  have hxb : (b + 10) / 9 ≤ x := le_trans (le_max_right _ _) hx
  have hp : 0 ≤ x ^ 2 * (x - 6) :=
    mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx6)
  unfold f
  nlinarith [hp]

theorem gap16 :
    UniqueRootOn f (Set.Ioi 3) := by
  have hroot_image : (0 : ℝ) ∈ f '' Set.Icc (3 : ℝ) 5 := by
    exact
      (intermediate_value_Icc (f := f) (by norm_num)
        continuous_f.continuousOn) (by norm_num [f])
  rcases hroot_image with ⟨x, hx, hroot⟩
  have hxgt : 3 < x := by
    rcases lt_or_eq_of_le hx.1 with hlt | heq
    · exact hlt
    · subst x
      norm_num [f] at hroot
  refine ⟨x, hxgt, hroot, ?_⟩
  intro y hy hyroot
  have hcross : 0 < (x - 3) * (y - 3) :=
    mul_pos (sub_pos.mpr hxgt) (sub_pos.mpr hy)
  have hq :
      0 < y ^ 2 + y * x + x ^ 2 - 6 * (y + x) + 9 := by
    nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 3), hcross]
  have hdiff := f_sub_f y x
  rw [hyroot, hroot] at hdiff
  have hp :
      (y - x) * (y ^ 2 + y * x + x ^ 2 - 6 * (y + x) + 9) = 0 := by
    nlinarith [hdiff]
  rcases mul_eq_zero.mp hp with hyx | hqzero
  · linarith
  · exact (ne_of_gt hq hqzero).elim

theorem gap17 (x : ℝ) :
    x ∈ {y : ℝ | 3 < y ∧ f y = 0} ↔
      x ^ 3 - 6 * x ^ 2 + 9 * x - 10 = 0 := by
  constructor
  · rintro ⟨_, hroot⟩
    simpa [f] using hroot
  · intro hpoly
    have hroot : f x = 0 := by
      simpa [f] using hpoly
    have hxgt : 3 < x := by
      by_contra hnot
      have hx3 : x ≤ 3 := le_of_not_gt hnot
      have hs : 0 ≤ (x - 1) ^ 2 := sq_nonneg (x - 1)
      have hx4 : x - 4 ≤ 0 := by
        linarith
      have hp : (x - 1) ^ 2 * (x - 4) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hs hx4
      have hid := f_add_six x
      rw [hroot] at hid
      nlinarith [hp]
    exact ⟨hxgt, hroot⟩

end

end ProofGap.Exercise1462

import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise2435
noncomputable section

open scoped Interval

def s : ℝ :=
  ∫ y in (1 : ℝ)..Real.exp 1,
    Real.sqrt (1 + (y / 2 - 1 / (2 * y)) ^ 2)

private lemma positive_on_uIcc_one_exp_one {x : ℝ}
    (hx : x ∈ Set.uIcc (1 : ℝ) (Real.exp 1)) : 0 < x := by
  exact lt_of_lt_of_le
    (lt_min zero_lt_one (Real.exp_pos 1)) hx.1

theorem gap1 :
    s =
      ∫ y in (1 : ℝ)..Real.exp 1,
        Real.sqrt (1 + (y / 2 - 1 / (2 * y)) ^ 2) := by
  rfl

theorem gap2 :
    (∫ y in (1 : ℝ)..Real.exp 1,
      Real.sqrt (1 + (y / 2 - 1 / (2 * y)) ^ 2)) =
        ∫ y in (1 : ℝ)..Real.exp 1, (1 + y ^ 2) / (2 * y) := by
  apply intervalIntegral.integral_congr
  intro y hy
  change
    Real.sqrt (1 + (y / 2 - 1 / (2 * y)) ^ 2) =
      (1 + y ^ 2) / (2 * y)
  have hypos : 0 < y := positive_on_uIcc_one_exp_one hy
  have hsq :
      1 + (y / 2 - 1 / (2 * y)) ^ 2 =
        ((1 + y ^ 2) / (2 * y)) ^ 2 := by
    field_simp [ne_of_gt hypos]
    ring
  have hquot : 0 < (1 + y ^ 2) / (2 * y) :=
    div_pos
      (add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg y))
      (mul_pos (by norm_num) hypos)
  calc
    Real.sqrt (1 + (y / 2 - 1 / (2 * y)) ^ 2) =
        Real.sqrt (((1 + y ^ 2) / (2 * y)) ^ 2) := congrArg Real.sqrt hsq
    _ = |(1 + y ^ 2) / (2 * y)| := Real.sqrt_sq_eq_abs _
    _ = (1 + y ^ 2) / (2 * y) := abs_of_pos hquot

theorem gap3 :
    (∫ y in (1 : ℝ)..Real.exp 1, (1 + y ^ 2) / (2 * y)) =
      ((Real.exp 1) ^ 2 + 1) / 4 := by
  let F : ℝ → ℝ := fun x => x ^ 2 / 4 + Real.log x / 2
  have hderiv : ∀ x ∈ Set.uIcc (1 : ℝ) (Real.exp 1),
      HasDerivAt F ((1 + x ^ 2) / (2 * x)) x := by
    intro x hx
    have hxpos : 0 < x := positive_on_uIcc_one_exp_one hx
    have hx0 : x ≠ 0 := ne_of_gt hxpos
    have h := (((hasDerivAt_id x).pow 2).div_const 4).add
      ((Real.hasDerivAt_log hx0).div_const 2)
    change HasDerivAt (fun z : ℝ => z ^ 2 / 4 + Real.log z / 2)
      ((1 + x ^ 2) / (2 * x)) x
    convert h using 1 <;> simp only [id_eq] <;>
      field_simp [hx0] <;> ring
  have hcont : ContinuousOn (fun x : ℝ => (1 + x ^ 2) / (2 * x))
      (Set.uIcc (1 : ℝ) (Real.exp 1)) := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (positive_on_uIcc_one_exp_one hx)
    exact
      ((continuousAt_const.add (continuousAt_id.pow 2)).div
        (continuousAt_const.mul continuousAt_id)
        (mul_ne_zero (by norm_num) hx0)).continuousWithinAt
  have hint : IntervalIntegrable (fun x : ℝ => (1 + x ^ 2) / (2 * x))
      MeasureTheory.volume 1 (Real.exp 1) :=
    hcont.intervalIntegrable
  calc
    (∫ y in (1 : ℝ)..Real.exp 1, (1 + y ^ 2) / (2 * y)) =
        F (Real.exp 1) - F 1 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    _ = ((Real.exp 1) ^ 2 + 1) / 4 := by
      simp only [F, Real.log_exp, Real.log_one]
      ring

theorem gap4 :
    s = ((Real.exp 1) ^ 2 + 1) / 4 := by
  calc
    s = ∫ y in (1 : ℝ)..Real.exp 1,
        Real.sqrt (1 + (y / 2 - 1 / (2 * y)) ^ 2) := gap1
    _ = ∫ y in (1 : ℝ)..Real.exp 1, (1 + y ^ 2) / (2 * y) := gap2
    _ = ((Real.exp 1) ^ 2 + 1) / 4 := gap3

end
end ProofGap.Exercise2435

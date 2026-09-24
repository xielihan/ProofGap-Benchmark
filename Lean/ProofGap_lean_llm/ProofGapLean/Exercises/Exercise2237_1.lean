import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

open scoped Interval

namespace ProofGap.Exercise2237_1

noncomputable section

def f (x : ℝ) : ℝ :=
  if x ∈ Set.Icc (0 : ℝ) 1 then x ^ 2
  else if x ∈ Set.Ioc (1 : ℝ) 2 then 2 - x
  else 0

theorem gap1 :
    (∫ x in (0 : ℝ)..2, f x) =
      (∫ x in (0 : ℝ)..1, x ^ 2) +
        ∫ x in (1 : ℝ)..2, 2 - x := by
  calc
    (∫ x in (0 : ℝ)..2, f x) =
        (∫ x in (0 : ℝ)..1, f x) + ∫ x in (1 : ℝ)..2, f x := by
      symm
      apply intervalIntegral.integral_add_adjacent_intervals
      · apply ContinuousOn.intervalIntegrable
        refine (continuous_id.pow 2).continuousOn.congr ?_
        intro x hx
        norm_num [Set.uIcc] at hx
        simp [f, hx]
      · apply ContinuousOn.intervalIntegrable
        have hcont : Continuous (fun x : ℝ => (2 : ℝ) - x) :=
          continuous_const.sub continuous_id
        refine hcont.continuousOn.congr ?_
        intro x hx
        norm_num [Set.uIcc] at hx
        rcases eq_or_lt_of_le hx.1 with rfl | hx1
        · norm_num [f]
        · simp [f, hx1, hx.2]
    _ = (∫ x in (0 : ℝ)..1, x ^ 2) + ∫ x in (1 : ℝ)..2, 2 - x := by
      congr 1
      · apply intervalIntegral.integral_congr
        intro x hx
        norm_num at hx
        simp [f, hx]
      · apply intervalIntegral.integral_congr
        intro x hx
        norm_num at hx
        rcases eq_or_lt_of_le hx.1 with rfl | hx1
        · norm_num [f]
        · simp [f, hx1, hx.2]

theorem gap2 :
    (∫ x in (0 : ℝ)..1, x ^ 2) +
        (∫ x in (1 : ℝ)..2, 2 - x) =
      5 / 6 := by
  have hsq : (∫ x in (0 : ℝ)..1, x ^ 2) = 1 / 3 := by
    calc
      (∫ x in (0 : ℝ)..1, x ^ 2) =
          (((1 : ℝ) * 1) * 1 / 3) - (((0 : ℝ) * 0) * 0 / 3) := by
        refine intervalIntegral.integral_eq_sub_of_hasDerivAt
          (a := (0 : ℝ)) (b := (1 : ℝ))
          (f := fun x : ℝ => (x * x) * x / 3)
          (f' := fun x : ℝ => x ^ 2) ?_ ?_
        · intro x _
          convert
            (((hasDerivAt_id x).mul (hasDerivAt_id x)).mul
              (hasDerivAt_id x)).div_const 3 using 1 <;>
            simp only [Pi.mul_apply, id_eq] <;> ring
        · simpa only [id_eq] using
            ((continuous_id.pow 2).intervalIntegrable
              (μ := MeasureTheory.volume) (0 : ℝ) (1 : ℝ))
      _ = 1 / 3 := by norm_num
  have haff : (∫ x in (1 : ℝ)..2, 2 - x) = 1 / 2 := by
    calc
      (∫ x in (1 : ℝ)..2, 2 - x) =
          (2 * (2 : ℝ) - ((2 : ℝ) * 2) / 2) -
            (2 * (1 : ℝ) - ((1 : ℝ) * 1) / 2) := by
        refine intervalIntegral.integral_eq_sub_of_hasDerivAt
          (a := (1 : ℝ)) (b := (2 : ℝ))
          (f := fun x : ℝ => 2 * x - (x * x) / 2)
          (f' := fun x : ℝ => 2 - x) ?_ ?_
        · intro x _
          convert ((hasDerivAt_id x).const_mul 2).sub
            (((hasDerivAt_id x).mul (hasDerivAt_id x)).div_const 2) using 1 <;>
            simp only [id_eq] <;> ring
        · have hcont : Continuous (fun x : ℝ => (2 : ℝ) - x) :=
            continuous_const.sub continuous_id
          exact hcont.intervalIntegrable
            (μ := MeasureTheory.volume) (1 : ℝ) (2 : ℝ)
      _ = 1 / 2 := by norm_num
  rw [hsq, haff]
  norm_num

theorem gap3 :
    (∫ x in (0 : ℝ)..2, f x) = 5 / 6 := by
  rw [gap1, gap2]

end

end ProofGap.Exercise2237_1

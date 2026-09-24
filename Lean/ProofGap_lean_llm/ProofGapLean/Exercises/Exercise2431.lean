import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise2431
noncomputable section

open scoped Interval

def s : ℝ := ∫ x in (0 : ℝ)..4, Real.sqrt (1 + (9 / 4 : ℝ) * x)

theorem gap1 :
    s = ∫ x in (0 : ℝ)..4, Real.sqrt (1 + (9 / 4 : ℝ) * x) := by
  rfl

theorem gap2 :
    (∫ x in (0 : ℝ)..4, Real.sqrt (1 + (9 / 4 : ℝ) * x)) =
      (8 / 27 : ℝ) * (10 * Real.sqrt 10 - 1) := by
  let F : ℝ → ℝ := fun x =>
    (8 / 27 : ℝ) *
      ((1 + (9 / 4 : ℝ) * x) * Real.sqrt (1 + (9 / 4 : ℝ) * x))
  have hcont : Continuous (fun x : ℝ => Real.sqrt (1 + (9 / 4 : ℝ) * x)) :=
    Real.continuous_sqrt.comp
      (continuous_const.add (continuous_const.mul continuous_id))
  have hint : IntervalIntegrable
      (fun x : ℝ => Real.sqrt (1 + (9 / 4 : ℝ) * x))
      MeasureTheory.volume 0 4 :=
    hcont.intervalIntegrable 0 4
  calc
    (∫ x in (0 : ℝ)..4, Real.sqrt (1 + (9 / 4 : ℝ) * x)) = F 4 - F 0 := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro x hx
        rw [Set.uIcc_of_le (by norm_num)] at hx
        have hpos : 0 < 1 + (9 / 4 : ℝ) * x := by
          nlinarith [hx.1]
        have hu : HasDerivAt
            (fun y : ℝ => 1 + (9 / 4 : ℝ) * y) (9 / 4 : ℝ) x := by
          convert
            (hasDerivAt_const (x := x) (c := (1 : ℝ))).add
              ((hasDerivAt_id x).const_mul (9 / 4 : ℝ)) using 1 <;>
            norm_num
        have hsqrt_ne : Real.sqrt (1 + (9 / 4 : ℝ) * x) ≠ 0 :=
          ne_of_gt (Real.sqrt_pos.2 hpos)
        have hsqrt : HasDerivAt
            (fun y : ℝ => Real.sqrt (1 + (9 / 4 : ℝ) * y))
            ((9 / 8 : ℝ) / Real.sqrt (1 + (9 / 4 : ℝ) * x)) x := by
          convert
            (Real.hasDerivAt_sqrt (ne_of_gt hpos)).comp x hu using 1 <;>
            field_simp [hsqrt_ne] <;> ring
        have hquot :
            (1 + (9 / 4 : ℝ) * x) /
                Real.sqrt (1 + (9 / 4 : ℝ) * x) =
              Real.sqrt (1 + (9 / 4 : ℝ) * x) := by
          apply (div_eq_iff hsqrt_ne).2
          calc
            1 + (9 / 4 : ℝ) * x =
                (Real.sqrt (1 + (9 / 4 : ℝ) * x)) ^ 2 :=
              (Real.sq_sqrt (le_of_lt hpos)).symm
            _ = Real.sqrt (1 + (9 / 4 : ℝ) * x) *
                Real.sqrt (1 + (9 / 4 : ℝ) * x) := by ring
        have hcoef :
            (8 / 27 : ℝ) *
                ((9 / 4 : ℝ) * Real.sqrt (1 + (9 / 4 : ℝ) * x) +
                  (1 + (9 / 4 : ℝ) * x) *
                    ((9 / 8 : ℝ) /
                      Real.sqrt (1 + (9 / 4 : ℝ) * x))) =
              Real.sqrt (1 + (9 / 4 : ℝ) * x) := by
          calc
            (8 / 27 : ℝ) *
                  ((9 / 4 : ℝ) * Real.sqrt (1 + (9 / 4 : ℝ) * x) +
                    (1 + (9 / 4 : ℝ) * x) *
                      ((9 / 8 : ℝ) /
                        Real.sqrt (1 + (9 / 4 : ℝ) * x))) =
                (8 / 27 : ℝ) *
                  ((9 / 4 : ℝ) * Real.sqrt (1 + (9 / 4 : ℝ) * x) +
                    (9 / 8 : ℝ) *
                      ((1 + (9 / 4 : ℝ) * x) /
                        Real.sqrt (1 + (9 / 4 : ℝ) * x))) := by ring
            _ = (8 / 27 : ℝ) *
                  ((9 / 4 : ℝ) * Real.sqrt (1 + (9 / 4 : ℝ) * x) +
                    (9 / 8 : ℝ) * Real.sqrt (1 + (9 / 4 : ℝ) * x)) := by
              rw [hquot]
            _ = Real.sqrt (1 + (9 / 4 : ℝ) * x) := by ring
        dsimp [F]
        rw [← hcoef]
        exact (hu.mul hsqrt).const_mul (8 / 27 : ℝ)
      · exact hint
    _ = (8 / 27 : ℝ) * (10 * Real.sqrt 10 - 1) := by
      norm_num [F] <;> ring

theorem gap3 :
    s = (8 / 27 : ℝ) * (10 * Real.sqrt 10 - 1) := by
  calc
    s = ∫ x in (0 : ℝ)..4, Real.sqrt (1 + (9 / 4 : ℝ) * x) := gap1
    _ = (8 / 27 : ℝ) * (10 * Real.sqrt 10 - 1) := gap2

end
end ProofGap.Exercise2431

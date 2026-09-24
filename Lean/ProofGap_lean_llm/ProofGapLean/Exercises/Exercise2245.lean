import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Basic

open scoped Interval

namespace ProofGap.Exercise2245

noncomputable section

def xOfT (t : ℝ) : ℝ := (5 - t ^ 2) / 4
def jacobian (t : ℝ) : ℝ := -t / 2
def pullback (t : ℝ) : ℝ := (5 - t ^ 2) / 8

private def integralPrimitive (x : ℝ) : ℝ :=
  (Real.sqrt (5 - 4 * x)) ^ 3 / 24 - 5 * Real.sqrt (5 - 4 * x) / 8

private lemma hasDerivAt_integralPrimitive (x : ℝ) (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) :
    HasDerivAt integralPrimitive (x / Real.sqrt (5 - 4 * x)) x := by
  have hpos : 0 < 5 - 4 * x := by linarith
  have hsqrt_ne : Real.sqrt (5 - 4 * x) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hpos)
  have hinner : HasDerivAt (fun y : ℝ => 5 - 4 * y) (-4) x := by
    simpa using
      (hasDerivAt_const x (5 : ℝ)).sub ((hasDerivAt_id x).const_mul (4 : ℝ))
  have hsqrt :
      HasDerivAt (fun y : ℝ => Real.sqrt (5 - 4 * y))
        ((1 / (2 * Real.sqrt (5 - 4 * x))) * (-4)) x :=
    (Real.hasDerivAt_sqrt (ne_of_gt hpos)).comp x hinner
  have h :=
    ((hsqrt.pow 3).div_const (24 : ℝ)).sub
      ((hsqrt.const_mul (5 : ℝ)).div_const (8 : ℝ))
  have hsquare :
      Real.sqrt (5 - 4 * x) ^ 2 = 5 - 4 * x :=
    Real.sq_sqrt hpos.le
  have hderiv :
      ((((3 : ℕ) : ℝ) * Real.sqrt (5 - 4 * x) ^ ((3 : ℕ) - 1) *
            (1 / (2 * Real.sqrt (5 - 4 * x)) * (-4))) / 24 -
        5 * (1 / (2 * Real.sqrt (5 - 4 * x)) * (-4)) / 8) =
        x / Real.sqrt (5 - 4 * x) := by
    rw [show (3 : ℕ) - 1 = 2 by norm_num, hsquare]
    field_simp [hsqrt_ne] <;> ring
  rw [hderiv] at h
  simpa [integralPrimitive] using h

private lemma integral_left_value :
    (∫ x in (-1 : ℝ)..1, x / Real.sqrt (5 - 4 * x)) = 1 / 6 := by
  calc
    (∫ x in (-1 : ℝ)..1, x / Real.sqrt (5 - 4 * x)) =
        integralPrimitive 1 - integralPrimitive (-1) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro x hx
        rw [Set.uIcc_of_le (by norm_num)] at hx
        exact hasDerivAt_integralPrimitive x hx.1 hx.2
      · have hinner : Continuous (fun x : ℝ => 5 - 4 * x) :=
          continuous_const.sub (continuous_const.mul continuous_id)
        have hsqrt : Continuous (fun x : ℝ => Real.sqrt (5 - 4 * x)) :=
          Real.continuous_sqrt.comp hinner
        have hcont :
            ContinuousOn (fun x : ℝ => x / Real.sqrt (5 - 4 * x))
              (Set.uIcc (-1 : ℝ) 1) := by
          refine continuousOn_id.div hsqrt.continuousOn ?_
          intro x hx
          rw [Set.uIcc_of_le (by norm_num)] at hx
          exact (Real.sqrt_pos.2 (by linarith [hx.1, hx.2])).ne'
        exact hcont.intervalIntegrable
    _ = 1 / 6 := by
      have hsqrt9 : Real.sqrt (9 : ℝ) = 3 := by
        rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
        norm_num
      norm_num [integralPrimitive, hsqrt9]

private def pullbackPrimitive (t : ℝ) : ℝ :=
  (5 * t - t ^ 3 / 3) / 8

private lemma hasDerivAt_pullbackPrimitive (t : ℝ) :
    HasDerivAt pullbackPrimitive (pullback t) t := by
  unfold pullbackPrimitive pullback
  convert
    ((((hasDerivAt_id t).const_mul (5 : ℝ)).sub
      (((hasDerivAt_id t).pow 3).div_const (3 : ℝ))).div_const (8 : ℝ)) using 1 <;>
    simp [id] <;>
    ring

private lemma integral_pullback_value :
    -(∫ t in (3 : ℝ)..1, pullback t) = 1 / 6 := by
  calc
    -(∫ t in (3 : ℝ)..1, pullback t) =
        -(pullbackPrimitive 1 - pullbackPrimitive 3) := by
      congr 1
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro t ht
        exact hasDerivAt_pullbackPrimitive t
      · have hcont : Continuous (fun t : ℝ => ((5 : ℝ) - t ^ 2) / (8 : ℝ)) :=
          (continuous_const.sub (continuous_id.pow 2)).div_const (8 : ℝ)
        have hi :
            IntervalIntegrable
              (fun t : ℝ => ((5 : ℝ) - t ^ 2) / (8 : ℝ))
              MeasureTheory.volume (3 : ℝ) (1 : ℝ) :=
          hcont.intervalIntegrable (μ := MeasureTheory.volume) (3 : ℝ) (1 : ℝ)
        simpa [pullback] using hi
    _ = 1 / 6 := by
      norm_num [pullbackPrimitive]

theorem gap1 :
    (∫ x in (-1 : ℝ)..1, x / Real.sqrt (5 - 4 * x)) =
      -(∫ t in (3 : ℝ)..1, pullback t) := by
  exact integral_left_value.trans integral_pullback_value.symm

theorem gap2 :
    -(∫ t in (3 : ℝ)..1, pullback t) = 1 / 6 := by
  exact integral_pullback_value

theorem gap3 :
    (∫ x in (-1 : ℝ)..1, x / Real.sqrt (5 - 4 * x)) =
      1 / 6 := by
  exact gap1.trans gap2

end

end ProofGap.Exercise2245

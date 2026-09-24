import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3804

noncomputable section

open MeasureTheory

def quadratic (a b c x : ℝ) : ℝ :=
  a * x ^ 2 + 2 * b * x + c

def gaussianQuadraticIntegral (a b c : ℝ) : ℝ :=
  ∫ x : ℝ, Real.exp (-(quadratic a b c x))

private theorem scaledShiftedGaussianIntegral (a b : ℝ) (ha : 0 < a) :
    (∫ x : ℝ, Real.exp (-((a * x + b) ^ 2 / a))) =
      1 / Real.sqrt a * ∫ t : ℝ, Real.exp (-(t ^ 2)) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have halg (x : ℝ) :
      (a * x + b) ^ 2 / a = a * (x + b / a) ^ 2 := by
    field_simp [ha0]
  have htranslate :
      (∫ x : ℝ, Real.exp (-(a * (x + b / a) ^ 2))) =
        ∫ x : ℝ, Real.exp (-(a * x ^ 2)) := by
    simpa using
      (MeasureTheory.integral_add_right_eq_self
        (fun x : ℝ => Real.exp (-(a * x ^ 2))) (b / a))
  have hgaussian :
      (∫ x : ℝ, Real.exp (-(a * x ^ 2))) =
        Real.sqrt (Real.pi / a) := by
    simpa only [neg_mul] using (integral_gaussian (b := a))
  have hfull :
      (∫ x : ℝ, Real.exp (-(x ^ 2))) = Real.sqrt Real.pi := by
    simpa using (integral_gaussian (b := (1 : ℝ)))
  calc
    (∫ x : ℝ, Real.exp (-((a * x + b) ^ 2 / a))) =
        ∫ x : ℝ, Real.exp (-(a * (x + b / a) ^ 2)) := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change Real.exp (-((a * x + b) ^ 2 / a)) =
          Real.exp (-(a * (x + b / a) ^ 2))
        rw [halg x]
    _ = ∫ x : ℝ, Real.exp (-(a * x ^ 2)) := htranslate
    _ = Real.sqrt (Real.pi / a) := hgaussian
    _ = Real.sqrt Real.pi / Real.sqrt a := by
      rw [Real.sqrt_div (le_of_lt Real.pi_pos)]
    _ = 1 / Real.sqrt a * Real.sqrt Real.pi := by ring
    _ = 1 / Real.sqrt a * ∫ t : ℝ, Real.exp (-(t ^ 2)) := by
      rw [hfull]

theorem gap1 (a b c x : ℝ) (ha : 0 < a) (hdisc : 0 < a * c - b ^ 2) :
    quadratic a b c x =
      ((a * x + b) ^ 2 + a * c - b ^ 2) / a := by
  unfold quadratic
  field_simp [ne_of_gt ha]
  ring

theorem gap2 (a b c : ℝ) (ha : 0 < a) (hdisc : 0 < a * c - b ^ 2) :
    gaussianQuadraticIntegral a b c =
      ∫ x : ℝ,
        Real.exp (-(((a * x + b) ^ 2 + a * c - b ^ 2) / a)) := by
  unfold gaussianQuadraticIntegral
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change Real.exp (-(quadratic a b c x)) =
      Real.exp (-(((a * x + b) ^ 2 + a * c - b ^ 2) / a))
    rw [gap1 a b c x ha hdisc]

theorem gap3 (a b c : ℝ) (ha : 0 < a) (hdisc : 0 < a * c - b ^ 2) :
    gaussianQuadraticIntegral a b c =
      Real.exp ((b ^ 2 - a * c) / a) *
        ∫ x : ℝ, Real.exp (-((a * x + b) ^ 2 / a)) := by
  rw [gap2 a b c ha hdisc]
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change Real.exp (-(((a * x + b) ^ 2 + a * c - b ^ 2) / a)) =
      Real.exp ((b ^ 2 - a * c) / a) *
        Real.exp (-((a * x + b) ^ 2 / a))
    rw [← Real.exp_add]
    congr 1
    ring

theorem gap4 (a b c : ℝ) (ha : 0 < a) (hdisc : 0 < a * c - b ^ 2) :
    gaussianQuadraticIntegral a b c =
      Real.exp ((b ^ 2 - a * c) / a) *
        ∫ t : ℝ, 1 / Real.sqrt a * Real.exp (-(t ^ 2)) := by
  rw [gap3 a b c ha hdisc]
  congr 1
  rw [scaledShiftedGaussianIntegral a b ha]
  rw [MeasureTheory.integral_const_mul]

theorem gap5 (a b c : ℝ) (ha : 0 < a) (hdisc : 0 < a * c - b ^ 2) :
    gaussianQuadraticIntegral a b c =
      2 / Real.sqrt a * Real.exp ((b ^ 2 - a * c) / a) *
        ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(t ^ 2)) := by
  have hfull :
      (∫ x : ℝ, Real.exp (-(x ^ 2))) = Real.sqrt Real.pi := by
    simpa using (integral_gaussian (b := (1 : ℝ)))
  have hhalf :
      (∫ x : ℝ in Set.Ioi 0, Real.exp (-(x ^ 2))) =
        Real.sqrt Real.pi / 2 := by
    simpa using (integral_gaussian_Ioi (b := (1 : ℝ)))
  rw [gap4 a b c ha hdisc]
  rw [MeasureTheory.integral_const_mul, hfull, hhalf]
  ring

theorem gap6 (a b c : ℝ) (ha : 0 < a) (hdisc : 0 < a * c - b ^ 2) :
    gaussianQuadraticIntegral a b c =
      Real.sqrt (Real.pi / a) *
        Real.exp ((b ^ 2 - a * c) / a) := by
  have hfull :
      (∫ x : ℝ, Real.exp (-(x ^ 2))) = Real.sqrt Real.pi := by
    simpa using (integral_gaussian (b := (1 : ℝ)))
  rw [gap4 a b c ha hdisc]
  rw [MeasureTheory.integral_const_mul, hfull]
  rw [Real.sqrt_div (le_of_lt Real.pi_pos)]
  ring

end

end ProofGap.Exercise3804

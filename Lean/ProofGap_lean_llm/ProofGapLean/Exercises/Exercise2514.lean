import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

open scoped Interval

namespace ProofGap.Exercise2514

noncomputable section

def solidMass (y : ℝ → ℝ) (a : ℝ) : ℝ :=
  ∫ x in 0..a, Real.pi * y x ^ 2
def firstMoment (y : ℝ → ℝ) (a : ℝ) : ℝ :=
  ∫ x in 0..a, x * Real.pi * y x ^ 2
def centroidX (y : ℝ → ℝ) (a : ℝ) : ℝ :=
  firstMoment y a / solidMass y a

private lemma integral_two_p_mul_x (a p : ℝ) :
    (∫ x in 0..a, 2 * p * x) = p * a ^ 2 := by
  calc
    (∫ x in 0..a, 2 * p * x) = p * a ^ 2 - p * 0 ^ 2 := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro x hx
        have hid : HasDerivAt (fun z : ℝ => z) 1 x := hasDerivAt_id x
        have hsq :
            HasDerivAt (fun z : ℝ => z * z) (1 * x + x * 1) x :=
          hid.mul hid
        convert hsq.const_mul p using 1 <;> ring_nf
      · have hc : Continuous (fun x : ℝ => 2 * p * x) :=
          continuous_const.mul continuous_id
        exact hc.intervalIntegrable (μ := MeasureTheory.volume) (0 : ℝ) a
    _ = p * a ^ 2 := by ring

private lemma integral_two_p_mul_sq (a p : ℝ) :
    (∫ x in 0..a, 2 * p * x ^ 2) = 2 * p / 3 * a ^ 3 := by
  calc
    (∫ x in 0..a, 2 * p * x ^ 2) =
        2 * p / 3 * a ^ 3 - 2 * p / 3 * 0 ^ 3 := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro x hx
        have hid : HasDerivAt (fun z : ℝ => z) 1 x := hasDerivAt_id x
        have hsq :
            HasDerivAt (fun z : ℝ => z * z) (1 * x + x * 1) x :=
          hid.mul hid
        have hcub :
            HasDerivAt (fun z : ℝ => (z * z) * z)
              ((1 * x + x * 1) * x + (x * x) * 1) x :=
          hsq.mul hid
        convert hcub.const_mul (2 * p / 3) using 1 <;> ring_nf
      · have hc : Continuous (fun x : ℝ => 2 * p * x ^ 2) :=
          continuous_const.mul (continuous_id.pow 2)
        exact hc.intervalIntegrable (μ := MeasureTheory.volume) (0 : ℝ) a
    _ = 2 * p / 3 * a ^ 3 := by ring

theorem gap1 (η : ℝ) (hη : η = 0) : η = 0 := by
  exact hη

theorem gap2 (y : ℝ → ℝ) (a ξ : ℝ)
    (hξ : ξ = centroidX y a) :
    ξ = (∫ x in 0..a, x * Real.pi * y x ^ 2) /
      (∫ x in 0..a, Real.pi * y x ^ 2) := by
  simpa [centroidX, firstMoment, solidMass] using hξ

theorem gap3 (y : ℝ → ℝ) (a p : ℝ) (ha : 0 < a) (hp : 0 < p)
    (hBoundary : ∀ x ∈ Set.Icc (0 : ℝ) a, y x ^ 2 = 2 * p * x) :
    centroidX y a =
      (∫ x in 0..a, 2 * p * x ^ 2) /
        (∫ x in 0..a, 2 * p * x) := by
  have hnum :
      (∫ x in 0..a, x * Real.pi * y x ^ 2) =
        Real.pi * (∫ x in 0..a, 2 * p * x ^ 2) := by
    calc
      (∫ x in 0..a, x * Real.pi * y x ^ 2) =
          ∫ x in 0..a, Real.pi * (2 * p * x ^ 2) := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hx' : x ∈ Set.Icc (0 : ℝ) a := by
          simpa [Set.uIcc_of_le ha.le] using hx
        change x * Real.pi * y x ^ 2 = Real.pi * (2 * p * x ^ 2)
        rw [hBoundary x hx']
        ring
      _ = Real.pi * (∫ x in 0..a, 2 * p * x ^ 2) := by
        rw [intervalIntegral.integral_const_mul]
  have hden :
      (∫ x in 0..a, Real.pi * y x ^ 2) =
        Real.pi * (∫ x in 0..a, 2 * p * x) := by
    calc
      (∫ x in 0..a, Real.pi * y x ^ 2) =
          ∫ x in 0..a, Real.pi * (2 * p * x) := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hx' : x ∈ Set.Icc (0 : ℝ) a := by
          simpa [Set.uIcc_of_le ha.le] using hx
        change Real.pi * y x ^ 2 = Real.pi * (2 * p * x)
        rw [hBoundary x hx']
      _ = Real.pi * (∫ x in 0..a, 2 * p * x) := by
        rw [intervalIntegral.integral_const_mul]
  have hD : (∫ x in 0..a, 2 * p * x) ≠ 0 := by
    rw [integral_two_p_mul_x]
    exact mul_ne_zero (ne_of_gt hp) (pow_ne_zero 2 (ne_of_gt ha))
  rw [centroidX, firstMoment, solidMass, hnum, hden]
  apply (div_eq_div_iff (mul_ne_zero Real.pi_ne_zero hD) hD).2
  ring

theorem gap4 (a p : ℝ) (ha : 0 < a) (hp : 0 < p) :
    (∫ x in 0..a, 2 * p * x ^ 2) /
        (∫ x in 0..a, 2 * p * x) =
      2 / 3 * a := by
  rw [integral_two_p_mul_sq, integral_two_p_mul_x]
  have hD : p * a ^ 2 ≠ 0 :=
    mul_ne_zero (ne_of_gt hp) (pow_ne_zero 2 (ne_of_gt ha))
  apply (div_eq_iff hD).2
  ring

theorem gap5 (y : ℝ → ℝ) (a p ξ : ℝ)
    (ha : 0 < a) (hp : 0 < p)
    (hBoundary : ∀ x ∈ Set.Icc (0 : ℝ) a, y x ^ 2 = 2 * p * x)
    (hξ : ξ = centroidX y a) :
    ξ = 2 / 3 * a := by
  calc
    ξ = centroidX y a := hξ
    _ = (∫ x in 0..a, 2 * p * x ^ 2) /
          (∫ x in 0..a, 2 * p * x) := gap3 y a p ha hp hBoundary
    _ = 2 / 3 * a := gap4 a p ha hp

theorem gap6 (a ξ η : ℝ)
    (hξ : ξ = 2 / 3 * a) (hη : η = 0) :
    (ξ, η) = (2 / 3 * a, 0) := by
  rw [hξ, hη]

end

end ProofGap.Exercise2514

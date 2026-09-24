import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise4326

noncomputable section

open scoped Interval

def semicircle (a θ : ℝ) : ℝ × ℝ :=
  (a * Real.cos θ, a * Real.sin θ)

def linearDensity (M a : ℝ) : ℝ := M / (Real.pi * a)

def arcSpeed (a θ : ℝ) : ℝ :=
  Real.sqrt
    ((deriv (fun t => (semicircle a t).1) θ) ^ 2 +
      (deriv (fun t => (semicircle a t).2) θ) ^ 2)

def horizontalForce (k m M a : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..Real.pi,
    k * m * linearDensity M a / a ^ 2 *
      Real.cos θ * arcSpeed a θ

def verticalForce (k m M a : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..Real.pi,
    k * m * linearDensity M a / a ^ 2 *
      Real.sin θ * arcSpeed a θ

private theorem arcSpeed_eq (a θ : ℝ) (ha : 0 < a) :
    arcSpeed a θ = a := by
  unfold arcSpeed
  change Real.sqrt
      ((deriv (fun t : ℝ => a * Real.cos t) θ) ^ 2 +
        (deriv (fun t : ℝ => a * Real.sin t) θ) ^ 2) = a
  have hcos :
      deriv (fun t : ℝ => a * Real.cos t) θ =
        a * (-Real.sin θ) :=
    ((Real.hasDerivAt_cos θ).const_mul a).deriv
  have hsin :
      deriv (fun t : ℝ => a * Real.sin t) θ =
        a * Real.cos θ :=
    ((Real.hasDerivAt_sin θ).const_mul a).deriv
  rw [hcos, hsin]
  have hinside :
      (a * (-Real.sin θ)) ^ 2 + (a * Real.cos θ) ^ 2 = a ^ 2 := by
    calc
      (a * (-Real.sin θ)) ^ 2 + (a * Real.cos θ) ^ 2 =
          a ^ 2 * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by ring
      _ = a ^ 2 := by rw [Real.sin_sq_add_cos_sq]; ring
  rw [hinside, Real.sqrt_sq_eq_abs, abs_of_pos ha]

private theorem integral_cos_zero_pi :
    (∫ θ in (0 : ℝ)..Real.pi, Real.cos θ) = 0 := by
  have hderiv : deriv Real.sin = Real.cos := by
    funext x
    exact (Real.hasDerivAt_sin x).deriv
  have hFTC :
      (∫ θ in (0 : ℝ)..Real.pi, Real.cos θ) =
        Real.sin Real.pi - Real.sin 0 :=
    intervalIntegral.integral_deriv_eq_sub' Real.sin hderiv
      (by
        intro x hx
        exact (Real.hasDerivAt_sin x).differentiableAt)
      Real.continuous_cos.continuousOn
  calc
    (∫ θ in (0 : ℝ)..Real.pi, Real.cos θ) =
        Real.sin Real.pi - Real.sin 0 := hFTC
    _ = 0 := by norm_num

private theorem integral_sin_zero_pi :
    (∫ θ in (0 : ℝ)..Real.pi, Real.sin θ) = 2 := by
  have hnegcos (x : ℝ) :
      HasDerivAt (fun t : ℝ => -Real.cos t) (Real.sin x) x := by
    simpa only [neg_neg] using (Real.hasDerivAt_cos x).neg
  have hderiv :
      deriv (fun t : ℝ => -Real.cos t) = Real.sin := by
    funext x
    exact (hnegcos x).deriv
  have hFTC :
      (∫ θ in (0 : ℝ)..Real.pi, Real.sin θ) =
        -Real.cos Real.pi - (-Real.cos 0) :=
    intervalIntegral.integral_deriv_eq_sub'
      (fun t : ℝ => -Real.cos t) hderiv
      (by
        intro x hx
        exact (hnegcos x).differentiableAt)
      Real.continuous_sin.continuousOn
  calc
    (∫ θ in (0 : ℝ)..Real.pi, Real.sin θ) =
        -Real.cos Real.pi - (-Real.cos 0) := hFTC
    _ = 2 := by norm_num

theorem gap1
    (k m M a : ℝ) (ha : 0 < a) :
    horizontalForce k m M a = 0 := by
  unfold horizontalForce
  calc
    (∫ θ in (0 : ℝ)..Real.pi,
        k * m * linearDensity M a / a ^ 2 *
          Real.cos θ * arcSpeed a θ) =
        ∫ θ in (0 : ℝ)..Real.pi,
          (k * m * linearDensity M a / a ^ 2 * a) * Real.cos θ := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      change
        k * m * linearDensity M a / a ^ 2 * Real.cos θ * arcSpeed a θ =
          (k * m * linearDensity M a / a ^ 2 * a) * Real.cos θ
      rw [arcSpeed_eq a θ ha]
      ring
    _ = (k * m * linearDensity M a / a ^ 2 * a) *
          (∫ θ in (0 : ℝ)..Real.pi, Real.cos θ) := by
      rw [intervalIntegral.integral_const_mul]
    _ = 0 := by
      rw [integral_cos_zero_pi]
      ring

theorem gap2 (a θ : ℝ) (ha : 0 < a) :
    arcSpeed a θ = a := by
  exact arcSpeed_eq a θ ha

theorem gap3
    (k m M a θ : ℝ) (ha : 0 < a) :
    k * m * linearDensity M a / a ^ 2 *
        Real.sin θ * arcSpeed a θ =
      k * m * (M / (Real.pi * a)) / a ^ 2 *
        Real.sin θ * a := by
  rw [linearDensity, arcSpeed_eq a θ ha]

theorem gap4
    (k m M a θ : ℝ) (ha : 0 < a) :
    k * m * (M / (Real.pi * a)) / a ^ 2 *
        Real.sin θ * a =
      k * m * M / (Real.pi * a ^ 2) * Real.sin θ := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [ha0, hpi]

theorem gap5
    (k m M a : ℝ) (ha : 0 < a) :
    verticalForce k m M a =
      k * m * M / (Real.pi * a ^ 2) *
        (∫ θ in (0 : ℝ)..Real.pi, Real.sin θ) := by
  unfold verticalForce
  calc
    (∫ θ in (0 : ℝ)..Real.pi,
        k * m * linearDensity M a / a ^ 2 *
          Real.sin θ * arcSpeed a θ) =
        ∫ θ in (0 : ℝ)..Real.pi,
          (k * m * M / (Real.pi * a ^ 2)) * Real.sin θ := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      change
        k * m * linearDensity M a / a ^ 2 * Real.sin θ * arcSpeed a θ =
          k * m * M / (Real.pi * a ^ 2) * Real.sin θ
      exact (gap3 k m M a θ ha).trans (gap4 k m M a θ ha)
    _ = k * m * M / (Real.pi * a ^ 2) *
          (∫ θ in (0 : ℝ)..Real.pi, Real.sin θ) := by
      rw [intervalIntegral.integral_const_mul]

theorem gap6
    (k m M a : ℝ) (ha : 0 < a) :
    verticalForce k m M a =
      2 * k * m * M / (Real.pi * a ^ 2) := by
  rw [gap5 k m M a ha, integral_sin_zero_pi]
  ring

end

end ProofGap.Exercise4326

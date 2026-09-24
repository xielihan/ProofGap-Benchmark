import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

open scoped Interval

namespace ProofGap.Exercise2474

noncomputable section

def xAxisVolume : ℝ :=
  Real.pi * ∫ x in 0..Real.pi, Real.sin x ^ 2

def yAxisVolume : ℝ :=
  2 * Real.pi * ∫ x in 0..Real.pi, x * Real.sin x

private theorem sin_sq_interval_integral :
    (∫ x in (0 : ℝ)..Real.pi, Real.sin x ^ 2) = Real.pi / 2 := by
  let F : ℝ → ℝ := fun x => x / 2 - (Real.sin x * Real.cos x) / 2
  have hF : ∀ x : ℝ, HasDerivAt F (Real.sin x ^ 2) x := by
    intro x
    have hraw : HasDerivAt
        (fun y : ℝ => y / 2 - (Real.sin y * Real.cos y) / 2)
        (1 / 2 -
          (Real.cos x * Real.cos x + Real.sin x * (-Real.sin x)) / 2) x :=
      ((hasDerivAt_id x).div_const 2).sub
        (((Real.hasDerivAt_sin x).mul (Real.hasDerivAt_cos x)).div_const 2)
    have hcoef :
        1 / 2 -
            (Real.cos x * Real.cos x + Real.sin x * (-Real.sin x)) / 2 =
          Real.sin x ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq x]
    simpa only [F, hcoef] using hraw
  have hInt :
      (∫ x in (0 : ℝ)..Real.pi, Real.sin x ^ 2) =
        F Real.pi - F 0 :=
    intervalIntegral.integral_deriv_eq_sub' F
      (funext fun x => (hF x).deriv)
      (fun x _ => (hF x).differentiableAt)
      (Real.continuous_sin.pow 2).continuousOn
  simpa [F] using hInt

private theorem mul_sin_interval_integral :
    (∫ x in (0 : ℝ)..Real.pi, x * Real.sin x) = Real.pi := by
  let F : ℝ → ℝ := fun x => Real.sin x - x * Real.cos x
  have hF : ∀ x : ℝ, HasDerivAt F (x * Real.sin x) x := by
    intro x
    have hraw : HasDerivAt
        (fun y : ℝ => Real.sin y - y * Real.cos y)
        (Real.cos x -
          (1 * Real.cos x + x * (-Real.sin x))) x :=
      (Real.hasDerivAt_sin x).sub
        ((hasDerivAt_id x).mul (Real.hasDerivAt_cos x))
    have hcoef :
        Real.cos x - (1 * Real.cos x + x * (-Real.sin x)) =
          x * Real.sin x := by
      ring
    simpa only [F, hcoef] using hraw
  have hInt :
      (∫ x in (0 : ℝ)..Real.pi, x * Real.sin x) =
        F Real.pi - F 0 :=
    intervalIntegral.integral_deriv_eq_sub' F
      (funext fun x => (hF x).deriv)
      (fun x _ => (hF x).differentiableAt)
      (continuous_id.mul Real.continuous_sin).continuousOn
  simpa [F] using hInt

theorem gap1 (Vₓ : ℝ) (hV : Vₓ = xAxisVolume) :
    Vₓ = Real.pi * ∫ x in 0..Real.pi, Real.sin x ^ 2 := by
  simpa [xAxisVolume] using hV

theorem gap2 :
    Real.pi * (∫ x in 0..Real.pi, Real.sin x ^ 2) =
      Real.pi ^ 2 / 2 := by
  rw [sin_sq_interval_integral]
  ring

theorem gap3 (Vₓ : ℝ) (hV : Vₓ = xAxisVolume) :
    Vₓ = Real.pi ^ 2 / 2 := by
  rw [hV, xAxisVolume]
  exact gap2

theorem gap4 (Vᵧ : ℝ) (hV : Vᵧ = yAxisVolume) :
    Vᵧ = 2 * Real.pi * ∫ x in 0..Real.pi, x * Real.sin x := by
  simpa [yAxisVolume] using hV

theorem gap5 :
    2 * Real.pi * (∫ x in 0..Real.pi, x * Real.sin x) =
      2 * Real.pi ^ 2 := by
  rw [mul_sin_interval_integral]
  ring

theorem gap6 (Vᵧ : ℝ) (hV : Vᵧ = yAxisVolume) :
    Vᵧ = 2 * Real.pi ^ 2 := by
  rw [hV, yAxisVolume]
  exact gap5

end

end ProofGap.Exercise2474

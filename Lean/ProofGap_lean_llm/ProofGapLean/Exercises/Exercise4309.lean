import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4309

noncomputable section

open MeasureTheory
open scoped Interval

def astroidParam (a b t : ℝ) : ℝ × ℝ :=
  (a * (Real.cos t) ^ 3, b * (Real.sin t) ^ 3)

def astroidOrientedArea (a b : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    ∫ t in (0 : ℝ)..2 * Real.pi,
      (astroidParam a b t).1 *
          deriv (fun s => (astroidParam a b s).2) t -
        (astroidParam a b t).2 *
          deriv (fun s => (astroidParam a b s).1) t

theorem gap1 (a b : ℝ) :
    astroidOrientedArea a b =
      3 * a * b / 2 *
        ∫ t in (0 : ℝ)..2 * Real.pi,
          (Real.cos t) ^ 4 * (Real.sin t) ^ 2 +
            (Real.cos t) ^ 2 * (Real.sin t) ^ 4 := by
  have hsin (t : ℝ) :
      deriv (fun s => (astroidParam a b s).2) t =
        b * (3 * (Real.sin t) ^ 2 * Real.cos t) := by
    simpa [astroidParam, mul_assoc] using
      ((((Real.hasDerivAt_sin t).pow 3).const_mul b).deriv)
  have hcos (t : ℝ) :
      deriv (fun s => (astroidParam a b s).1) t =
        a * (3 * (Real.cos t) ^ 2 * (-Real.sin t)) := by
    simpa [astroidParam, mul_assoc] using
      ((((Real.hasDerivAt_cos t).pow 3).const_mul a).deriv)
  have hcong :
      (∫ t in (0 : ℝ)..2 * Real.pi,
        (astroidParam a b t).1 *
            deriv (fun s => (astroidParam a b s).2) t -
          (astroidParam a b t).2 *
            deriv (fun s => (astroidParam a b s).1) t) =
        ∫ t in (0 : ℝ)..2 * Real.pi,
          (3 * a * b) *
            ((Real.cos t) ^ 4 * (Real.sin t) ^ 2 +
              (Real.cos t) ^ 2 * (Real.sin t) ^ 4) := by
    apply intervalIntegral.integral_congr
    intro t ht
    change
      (astroidParam a b t).1 *
            deriv (fun s => (astroidParam a b s).2) t -
          (astroidParam a b t).2 *
            deriv (fun s => (astroidParam a b s).1) t =
        (3 * a * b) *
          ((Real.cos t) ^ 4 * (Real.sin t) ^ 2 +
            (Real.cos t) ^ 2 * (Real.sin t) ^ 4)
    rw [hsin t, hcos t]
    simp only [astroidParam]
    ring
  unfold astroidOrientedArea
  rw [hcong, intervalIntegral.integral_const_mul]
  ring

theorem gap2 (a b : ℝ) :
    3 * a * b / 2 *
        (∫ t in (0 : ℝ)..2 * Real.pi,
          (Real.cos t) ^ 4 * (Real.sin t) ^ 2 +
            (Real.cos t) ^ 2 * (Real.sin t) ^ 4) =
      (3 / 8 : ℝ) * a * b *
        ∫ t in (0 : ℝ)..2 * Real.pi,
          (Real.sin (2 * t)) ^ 2 := by
  have htrig (t : ℝ) :
      (Real.cos t) ^ 4 * (Real.sin t) ^ 2 +
          (Real.cos t) ^ 2 * (Real.sin t) ^ 4 =
        (1 / 4 : ℝ) * (Real.sin (2 * t)) ^ 2 := by
    rw [Real.sin_two_mul]
    calc
      (Real.cos t) ^ 4 * (Real.sin t) ^ 2 +
          (Real.cos t) ^ 2 * (Real.sin t) ^ 4 =
          (Real.cos t) ^ 2 * (Real.sin t) ^ 2 *
            ((Real.sin t) ^ 2 + (Real.cos t) ^ 2) := by ring
      _ = (Real.cos t) ^ 2 * (Real.sin t) ^ 2 := by
        rw [Real.sin_sq_add_cos_sq]
        ring
      _ = (1 / 4 : ℝ) * (2 * Real.sin t * Real.cos t) ^ 2 := by ring
  have hcong :
      (∫ t in (0 : ℝ)..2 * Real.pi,
          (Real.cos t) ^ 4 * (Real.sin t) ^ 2 +
            (Real.cos t) ^ 2 * (Real.sin t) ^ 4) =
        ∫ t in (0 : ℝ)..2 * Real.pi,
          (1 / 4 : ℝ) * (Real.sin (2 * t)) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact htrig t
  rw [hcong, intervalIntegral.integral_const_mul]
  ring

theorem gap3 (a b : ℝ) :
    (3 / 8 : ℝ) * a * b *
        (∫ t in (0 : ℝ)..2 * Real.pi,
          (Real.sin (2 * t)) ^ 2) =
      (3 / 8 : ℝ) * Real.pi * a * b := by
  let F : ℝ → ℝ := fun t =>
    t / 2 - (Real.sin (2 * t) * Real.cos (2 * t)) / 4
  have hF (t : ℝ) : HasDerivAt F ((Real.sin (2 * t)) ^ 2) t := by
    have hlin : HasDerivAt (fun x : ℝ => 2 * x) 2 t := by
      simpa using (hasDerivAt_id t).const_mul 2
    have hs : HasDerivAt (fun x : ℝ => Real.sin (2 * x))
        (Real.cos (2 * t) * 2) t :=
      (Real.hasDerivAt_sin (2 * t)).comp t hlin
    have hc : HasDerivAt (fun x : ℝ => Real.cos (2 * x))
        (-Real.sin (2 * t) * 2) t :=
      (Real.hasDerivAt_cos (2 * t)).comp t hlin
    have hraw := ((hasDerivAt_id t).div_const 2).sub ((hs.mul hc).div_const 4)
    convert hraw using 1
    nlinarith [Real.sin_sq_add_cos_sq (2 * t)]
  have hcontinuous : Continuous (fun t : ℝ => (Real.sin (2 * t)) ^ 2) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).pow 2
  have hderiv : deriv F = fun t : ℝ => (Real.sin (2 * t)) ^ 2 := by
    funext t
    exact (hF t).deriv
  have hIntegral :
      (∫ t in (0 : ℝ)..2 * Real.pi, (Real.sin (2 * t)) ^ 2) =
        F (2 * Real.pi) - F 0 := by
    exact intervalIntegral.integral_deriv_eq_sub' F hderiv
      (fun x _ => (hF x).differentiableAt)
      hcontinuous.continuousOn
  rw [hIntegral]
  simp [F, Real.sin_two_mul]
  ring

theorem gap4 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    astroidOrientedArea a b =
      (3 / 8 : ℝ) * Real.pi * a * b := by
  calc
    astroidOrientedArea a b =
        3 * a * b / 2 *
          (∫ t in (0 : ℝ)..2 * Real.pi,
            (Real.cos t) ^ 4 * (Real.sin t) ^ 2 +
              (Real.cos t) ^ 2 * (Real.sin t) ^ 4) := gap1 a b
    _ = (3 / 8 : ℝ) * a * b *
          (∫ t in (0 : ℝ)..2 * Real.pi,
            (Real.sin (2 * t)) ^ 2) := gap2 a b
    _ = (3 / 8 : ℝ) * Real.pi * a * b := gap3 a b

end

end ProofGap.Exercise4309

import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace ProofGap.Exercise2416
noncomputable section

open scoped Interval
open MeasureTheory

def curveX (a t : ℝ) : ℝ := a * (2 * Real.cos t - Real.cos (2 * t))
def curveY (a t : ℝ) : ℝ := a * (2 * Real.sin t - Real.sin (2 * t))
def area (a : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    ∫ t in (0 : ℝ)..2 * Real.pi,
      curveX a t * deriv (curveY a) t - curveY a t * deriv (curveX a) t

private theorem curveY_hasDerivAt (a t : ℝ) :
    HasDerivAt (curveY a) (a * (2 * Real.cos t - 2 * Real.cos (2 * t))) t := by
  have harg : HasDerivAt (fun x : ℝ => 2 * x) 2 t := by
    simpa using (hasDerivAt_id t).const_mul 2
  have hsin2 := (Real.hasDerivAt_sin (2 * t)).comp t harg
  unfold curveY
  convert (((Real.hasDerivAt_sin t).const_mul 2).sub hsin2).const_mul a using 1 <;> ring

private theorem curveX_hasDerivAt (a t : ℝ) :
    HasDerivAt (curveX a) (a * (-2 * Real.sin t + 2 * Real.sin (2 * t))) t := by
  have harg : HasDerivAt (fun x : ℝ => 2 * x) 2 t := by
    simpa using (hasDerivAt_id t).const_mul 2
  have hcos2 := (Real.hasDerivAt_cos (2 * t)).comp t harg
  unfold curveX
  convert (((Real.hasDerivAt_cos t).const_mul 2).sub hcos2).const_mul a using 1 <;> ring

private theorem deriv_curveY (a t : ℝ) :
    deriv (curveY a) t = a * (2 * Real.cos t - 2 * Real.cos (2 * t)) :=
  (curveY_hasDerivAt a t).deriv

private theorem deriv_curveX (a t : ℝ) :
    deriv (curveX a) t = a * (-2 * Real.sin t + 2 * Real.sin (2 * t)) :=
  (curveX_hasDerivAt a t).deriv

theorem gap1 (a : ℝ) :
    area a =
      (1 / 2 : ℝ) *
        ∫ t in (0 : ℝ)..2 * Real.pi,
          curveX a t * deriv (curveY a) t -
            curveY a t * deriv (curveX a) t := by rfl

theorem gap2 (a : ℝ) :
    area a =
      (1 / 2 : ℝ) *
        ∫ t in (0 : ℝ)..2 * Real.pi,
          a * (2 * Real.cos t - Real.cos (2 * t)) *
              (a * (2 * Real.cos t - 2 * Real.cos (2 * t))) -
            a * (2 * Real.sin t - Real.sin (2 * t)) *
              (a * (-2 * Real.sin t + 2 * Real.sin (2 * t))) := by
  unfold area
  apply congrArg ((1 / 2 : ℝ) * ·)
  apply intervalIntegral.integral_congr
  intro t ht
  change curveX a t * deriv (curveY a) t -
      curveY a t * deriv (curveX a) t =
    a * (2 * Real.cos t - Real.cos (2 * t)) *
        (a * (2 * Real.cos t - 2 * Real.cos (2 * t))) -
      a * (2 * Real.sin t - Real.sin (2 * t)) *
        (a * (-2 * Real.sin t + 2 * Real.sin (2 * t)))
  rw [deriv_curveY, deriv_curveX]
  unfold curveX curveY
  rfl

theorem gap3 (a : ℝ) :
    area a =
      3 * a ^ 2 *
        ∫ t in (0 : ℝ)..2 * Real.pi,
          (1 - Real.cos t * Real.cos (2 * t) -
            Real.sin t * Real.sin (2 * t)) := by
  rw [gap2]
  have hcongr :
      (∫ t in (0 : ℝ)..2 * Real.pi,
        a * (2 * Real.cos t - Real.cos (2 * t)) *
              (a * (2 * Real.cos t - 2 * Real.cos (2 * t))) -
            a * (2 * Real.sin t - Real.sin (2 * t)) *
              (a * (-2 * Real.sin t + 2 * Real.sin (2 * t)))) =
        ∫ t in (0 : ℝ)..2 * Real.pi,
          (6 * a ^ 2) * (1 - Real.cos t * Real.cos (2 * t) -
            Real.sin t * Real.sin (2 * t)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    change
      a * (2 * Real.cos t - Real.cos (2 * t)) *
            (a * (2 * Real.cos t - 2 * Real.cos (2 * t))) -
          a * (2 * Real.sin t - Real.sin (2 * t)) *
            (a * (-2 * Real.sin t + 2 * Real.sin (2 * t))) =
        (6 * a ^ 2) * (1 - Real.cos t * Real.cos (2 * t) -
          Real.sin t * Real.sin (2 * t))
    nlinarith [Real.sin_sq_add_cos_sq t, Real.sin_sq_add_cos_sq (2 * t)]
  rw [hcongr, intervalIntegral.integral_const_mul]
  ring

theorem gap4 (a : ℝ) :
    3 * a ^ 2 *
        (∫ t in (0 : ℝ)..2 * Real.pi,
          (1 - Real.cos t * Real.cos (2 * t) -
            Real.sin t * Real.sin (2 * t))) =
      3 * a ^ 2 * ∫ t in (0 : ℝ)..2 * Real.pi, (1 - Real.cos t) := by
  apply congrArg (3 * a ^ 2 * ·)
  apply intervalIntegral.integral_congr
  intro t ht
  have htrig : Real.cos t * Real.cos (2 * t) +
      Real.sin t * Real.sin (2 * t) = Real.cos t := by
    rw [← Real.cos_sub]
    rw [show t - 2 * t = -t by ring, Real.cos_neg]
  linarith

theorem gap5 (a : ℝ) :
    3 * a ^ 2 * ∫ t in (0 : ℝ)..2 * Real.pi, (1 - Real.cos t) =
      6 * Real.pi * a ^ 2 := by
  have hone : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 (2 * Real.pi) :=
    intervalIntegrable_const
  have hcos : IntervalIntegrable Real.cos volume 0 (2 * Real.pi) :=
    Real.continuous_cos.intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hone hcos]
  rw [integral_cos]
  simp only [intervalIntegral.integral_const, Real.sin_two_pi, Real.sin_zero,
    sub_zero, zero_sub]
  simp only [smul_eq_mul]
  ring

theorem gap6 (a : ℝ) :
    area a = 6 * Real.pi * a ^ 2 := by
  rw [gap3, gap4, gap5]

end
end ProofGap.Exercise2416

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise4370

noncomputable section

open scoped Interval

def xCoord (a t : ℝ) : ℝ :=
  a * Real.sin t ^ 2

def yCoord (a t : ℝ) : ℝ :=
  2 * a * Real.sin t * Real.cos t

def zCoord (a t : ℝ) : ℝ :=
  a * Real.cos t ^ 2

def xDeriv (a t : ℝ) : ℝ :=
  2 * a * Real.sin t * Real.cos t

def yDeriv (a t : ℝ) : ℝ :=
  2 * a * (Real.cos t ^ 2 - Real.sin t ^ 2)

def zDeriv (a t : ℝ) : ℝ :=
  -2 * a * Real.sin t * Real.cos t

def lineIntegral (a : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..Real.pi,
    (yCoord a t + zCoord a t) * xDeriv a t +
      (zCoord a t + xCoord a t) * yDeriv a t +
      (xCoord a t + yCoord a t) * zDeriv a t

def zeroCurlSurfaceFlux : ℝ :=
  0

theorem gap1 (a : ℝ) :
    lineIntegral a = zeroCurlSurfaceFlux := by
  unfold lineIntegral zeroCurlSurfaceFlux
  let F : ℝ → ℝ := fun t =>
    xCoord a t * yCoord a t + yCoord a t * zCoord a t +
      zCoord a t * xCoord a t
  let g : ℝ → ℝ := fun t =>
    (yCoord a t + zCoord a t) * xDeriv a t +
      (zCoord a t + xCoord a t) * yDeriv a t +
      (xCoord a t + yCoord a t) * zDeriv a t
  have hx (t : ℝ) : HasDerivAt (xCoord a) (xDeriv a t) t := by
    unfold xCoord xDeriv
    convert ((Real.hasDerivAt_sin t).pow 2).const_mul a using 1 <;> ring
  have hy (t : ℝ) : HasDerivAt (yCoord a) (yDeriv a t) t := by
    unfold yCoord yDeriv
    convert ((Real.hasDerivAt_sin t).mul (Real.hasDerivAt_cos t)).const_mul
      (2 * a) using 1 <;> (try simp only [Pi.mul_apply]) <;> ring
  have hz (t : ℝ) : HasDerivAt (zCoord a) (zDeriv a t) t := by
    unfold zCoord zDeriv
    convert ((Real.hasDerivAt_cos t).pow 2).const_mul a using 1 <;> ring
  have hF (t : ℝ) : HasDerivAt F (g t) t := by
    dsimp only [F, g]
    convert (((hx t).mul (hy t)).add ((hy t).mul (hz t))).add
      ((hz t).mul (hx t)) using 1 <;> ring
  have hg : Continuous g := by
    dsimp [g, xCoord, yCoord, zCoord, xDeriv, yDeriv, zDeriv]
    fun_prop
  calc
    (∫ t in (0 : ℝ)..Real.pi,
        (yCoord a t + zCoord a t) * xDeriv a t +
          (zCoord a t + xCoord a t) * yDeriv a t +
          (xCoord a t + yCoord a t) * zDeriv a t) =
        ∫ t in (0 : ℝ)..Real.pi, g t := by rfl
    _ = F Real.pi - F 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ => hF t) (hg.intervalIntegrable 0 Real.pi)
    _ = 0 := by
      simp [F, xCoord, yCoord, zCoord]

theorem gap2 (a : ℝ) :
    lineIntegral a = 0 := by
  simpa [zeroCurlSurfaceFlux] using gap1 a

end

end ProofGap.Exercise4370

import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ProofGap.Exercise1130_2

noncomputable section

def y (x : ℝ) : ℝ := Real.exp x

def differential (f : ℝ → ℝ) (x dx : ℝ) : ℝ :=
  deriv f x * dx

def secondDifferential (f : ℝ → ℝ) (x dx ddx : ℝ) : ℝ :=
  deriv f x * ddx + deriv (fun t => deriv f t) x * dx ^ 2

private theorem deriv_y (x : ℝ) : deriv y x = Real.exp x := by
  change deriv Real.exp x = Real.exp x
  exact (Real.hasDerivAt_exp x).deriv

theorem gap1 (x dx : ℝ) :
    differential y x dx = Real.exp x * dx := by
  unfold differential
  rw [deriv_y]

theorem gap2 (x dx ddx : ℝ) :
    secondDifferential y x dx ddx =
      Real.exp x * ddx + Real.exp x * dx ^ 2 := by
  have h : (fun t : ℝ => deriv y t) = y := by
    funext t
    exact deriv_y t
  unfold secondDifferential
  rw [h, deriv_y]

end

end ProofGap.Exercise1130_2

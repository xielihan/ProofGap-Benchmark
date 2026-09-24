import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ProofGap.Exercise1130_1

noncomputable section

def y (x : ℝ) : ℝ := Real.exp x

def differential (f : ℝ → ℝ) (x dx : ℝ) : ℝ :=
  deriv f x * dx

def secondDifferential (f : ℝ → ℝ) (x dx : ℝ) : ℝ :=
  deriv (fun t => deriv f t) x * dx ^ 2

private theorem deriv_exp_eq (x : ℝ) :
    deriv (fun t : ℝ => Real.exp t) x = Real.exp x := by
  exact (Real.hasDerivAt_exp x).deriv

theorem gap1 (x dx : ℝ) :
    differential y x dx = Real.exp x * dx := by
  unfold differential y
  rw [deriv_exp_eq]

theorem gap2 (x dx : ℝ) :
    secondDifferential y x dx = Real.exp x * dx ^ 2 := by
  unfold secondDifferential y
  simp only [deriv_exp_eq]

end

end ProofGap.Exercise1130_1

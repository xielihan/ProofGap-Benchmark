import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add

namespace ProofGap.Exercise3336

noncomputable section

def z (φ ψ : ℝ → ℝ) (x y : ℝ) : ℝ :=
  φ x + ψ y

def partialX (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => g s y) x

def partialXY (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => partialX g x s) y

theorem gap1 (φ ψ : ℝ → ℝ)
    (hφ : Differentiable ℝ φ) (hψ : Differentiable ℝ ψ) :
    ∀ x y, partialX (z φ ψ) x y = deriv φ x := by
  intro x y
  change deriv (fun s => φ s + ψ y) x = deriv φ x
  exact ((hφ x).hasDerivAt.add_const (ψ y)).deriv

theorem gap2 (φ ψ : ℝ → ℝ)
    (hφ : Differentiable ℝ φ) (hψ : Differentiable ℝ ψ) :
    ∀ x y, partialXY (z φ ψ) x y = 0 := by
  intro x y
  simp [partialXY, gap1 φ ψ hφ hψ]

theorem gap3 (φ ψ : ℝ → ℝ)
    (hφ : Differentiable ℝ φ) (hψ : Differentiable ℝ ψ) :
    ∀ x y, partialXY (z φ ψ) x y = 0 := by
  exact gap2 φ ψ hφ hψ

end

end ProofGap.Exercise3336

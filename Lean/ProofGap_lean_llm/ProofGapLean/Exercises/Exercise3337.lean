import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3337

noncomputable section

def z (φ ψ : ℝ → ℝ) (x y : ℝ) : ℝ :=
  φ x * ψ y

def partialX (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => g s y) x

def partialY (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => g x s) y

def partialXY (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => partialX g x s) y

theorem gap1 (φ ψ : ℝ → ℝ)
    (hφ : Differentiable ℝ φ) (hψ : Differentiable ℝ ψ) :
    ∀ x y, partialX (z φ ψ) x y = deriv φ x * ψ y := by
  intro x y
  unfold partialX z
  simpa using ((hφ x).hasDerivAt.mul_const (ψ y)).deriv

theorem gap2 (φ ψ : ℝ → ℝ)
    (hφ : Differentiable ℝ φ) (hψ : Differentiable ℝ ψ) :
    ∀ x y, partialY (z φ ψ) x y = φ x * deriv ψ y := by
  intro x y
  unfold partialY z
  simpa using ((hψ y).hasDerivAt.const_mul (φ x)).deriv

theorem gap3 (φ ψ : ℝ → ℝ)
    (hφ : Differentiable ℝ φ) (hψ : Differentiable ℝ ψ) :
    ∀ x y, partialXY (z φ ψ) x y = deriv φ x * deriv ψ y := by
  intro x y
  unfold partialXY
  have hfun :
      (fun s => partialX (z φ ψ) x s) =
        (fun s => deriv φ x * ψ s) := by
    funext s
    exact gap1 φ ψ hφ hψ x s
  rw [hfun]
  simpa using ((hψ y).hasDerivAt.const_mul (deriv φ x)).deriv

theorem gap4 (φ ψ : ℝ → ℝ)
    (hφ : Differentiable ℝ φ) (hψ : Differentiable ℝ ψ) :
    ∀ x y,
      z φ ψ x y * partialXY (z φ ψ) x y =
        φ x * ψ y * deriv φ x * deriv ψ y := by
  intro x y
  rw [gap3 φ ψ hφ hψ x y]
  unfold z
  ring

theorem gap5 (φ ψ : ℝ → ℝ) :
    ∀ x y,
      φ x * ψ y * deriv φ x * deriv ψ y =
        deriv φ x * ψ y * φ x * deriv ψ y := by
  intro x y
  ring

theorem gap6 (φ ψ : ℝ → ℝ)
    (hφ : Differentiable ℝ φ) (hψ : Differentiable ℝ ψ) :
    ∀ x y,
      deriv φ x * ψ y * φ x * deriv ψ y =
        partialX (z φ ψ) x y * partialY (z φ ψ) x y := by
  intro x y
  rw [gap1 φ ψ hφ hψ x y, gap2 φ ψ hφ hψ x y]
  ring

theorem gap7 (φ ψ : ℝ → ℝ)
    (hφ : Differentiable ℝ φ) (hψ : Differentiable ℝ ψ) :
    ∀ x y,
      z φ ψ x y * partialXY (z φ ψ) x y =
        partialX (z φ ψ) x y * partialY (z φ ψ) x y := by
  intro x y
  calc
    z φ ψ x y * partialXY (z φ ψ) x y =
        φ x * ψ y * deriv φ x * deriv ψ y :=
      gap4 φ ψ hφ hψ x y
    _ = deriv φ x * ψ y * φ x * deriv ψ y :=
      gap5 φ ψ x y
    _ = partialX (z φ ψ) x y * partialY (z φ ψ) x y :=
      gap6 φ ψ hφ hψ x y

theorem gap8 (φ ψ : ℝ → ℝ)
    (hφ : Differentiable ℝ φ) (hψ : Differentiable ℝ ψ) :
    ∀ x y,
      z φ ψ x y * partialXY (z φ ψ) x y =
        partialX (z φ ψ) x y * partialY (z φ ψ) x y := by
  exact gap7 φ ψ hφ hψ

end

end ProofGap.Exercise3337

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace ProofGap.Exercise4306

noncomputable section

def P (F : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  y * F x y

def Q (F : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  x * F x y

def admissibleFields : Set (ℝ → ℝ → ℝ) :=
  {F |
    ∀ x y,
      x * deriv (fun t => F t y) x =
        y * deriv (fun t => F x t) y}

theorem gap1
    (F : ℝ → ℝ → ℝ) (x y : ℝ)
    (hx : DifferentiableAt ℝ (fun t => F t y) x)
    (hy : DifferentiableAt ℝ (fun t => F x t) y) :
    deriv (fun t => Q F t y) x =
        F x y + x * deriv (fun t => F t y) x ∧
      deriv (fun t => P F x t) y =
        F x y + y * deriv (fun t => F x t) y := by
  constructor
  · simpa [Q] using ((hasDerivAt_id x).mul hx.hasDerivAt).deriv
  · simpa [P] using ((hasDerivAt_id y).mul hy.hasDerivAt).deriv

theorem gap2
    (F : ℝ → ℝ → ℝ) (x y : ℝ)
    (hx : DifferentiableAt ℝ (fun t => F t y) x)
    (hy : DifferentiableAt ℝ (fun t => F x t) y) :
    deriv (fun t => Q F t y) x =
        deriv (fun t => P F x t) y ↔
      x * deriv (fun t => F t y) x =
        y * deriv (fun t => F x t) y := by
  obtain ⟨hQ, hP⟩ := gap1 F x y hx hy
  rw [hQ, hP]
  simp

theorem gap3 (F : ℝ → ℝ → ℝ) :
    F ∈ admissibleFields ↔
      ∀ x y,
        x * deriv (fun t => F t y) x =
          y * deriv (fun t => F x t) y := by
  rfl

end

end ProofGap.Exercise4306

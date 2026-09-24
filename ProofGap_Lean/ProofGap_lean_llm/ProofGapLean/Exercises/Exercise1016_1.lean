import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Abs

namespace ProofGap.Exercise1016_1

noncomputable section

def f₁ (x : ℝ) : ℝ := x ^ 2
def g₁ (x : ℝ) : ℝ := |x|
def F₁ (x : ℝ) : ℝ := f₁ (g₁ x)

def f₂ (x : ℝ) : ℝ := x
def g₂ (x : ℝ) : ℝ := |x|
def F₂ (x : ℝ) : ℝ := f₂ (g₂ x)

theorem gap1 (f g : ℝ → ℝ) (x₀ : ℝ) :
    DifferentiableAt ℝ (f ∘ g) x₀ ∨
      ¬ DifferentiableAt ℝ (f ∘ g) x₀ := by
  by_cases h : DifferentiableAt ℝ (f ∘ g) x₀
  · exact Or.inl h
  · exact Or.inr h

theorem gap2 : g₁ 0 = 0 := by
  simp [g₁]

theorem gap3 : HasDerivAt f₁ 0 0 := by
  have h := (hasDerivAt_id (0 : ℝ)).mul (hasDerivAt_id (0 : ℝ))
  have hfun : (id * id : ℝ → ℝ) = f₁ := by
    funext x
    simp [f₁, pow_two]
  rw [hfun] at h
  simpa using h

theorem gap4 : ¬ DifferentiableAt ℝ g₁ 0 := by
  simpa [g₁] using not_differentiableAt_abs_zero

theorem gap5 (x : ℝ) : F₁ x = f₁ (g₁ x) := by
  rfl

theorem gap6 (x : ℝ) : f₁ (g₁ x) = |x| ^ 2 := by
  rfl

theorem gap7 (x : ℝ) : |x| ^ 2 = x ^ 2 := by
  exact sq_abs x

theorem gap8 (x : ℝ) : F₁ x = x ^ 2 := by
  calc
    F₁ x = f₁ (g₁ x) := gap5 x
    _ = |x| ^ 2 := gap6 x
    _ = x ^ 2 := gap7 x

theorem gap9 : HasDerivAt F₁ 0 0 := by
  have hfun : F₁ = f₁ := by
    funext x
    simpa [f₁] using gap8 x
  rw [hfun]
  exact gap3

theorem gap10 : g₂ 0 = 0 := by
  simp [g₂]

theorem gap11 : HasDerivAt f₂ 1 0 := by
  simpa [f₂] using (hasDerivAt_id (0 : ℝ))

theorem gap12 : ¬ DifferentiableAt ℝ g₂ 0 := by
  simpa [g₁, g₂] using gap4

theorem gap13 (x : ℝ) : F₂ x = f₂ (g₂ x) := by
  rfl

theorem gap14 (x : ℝ) : f₂ (g₂ x) = |x| := by
  rfl

theorem gap15 (x : ℝ) : F₂ x = |x| := by
  calc
    F₂ x = f₂ (g₂ x) := gap13 x
    _ = |x| := gap14 x

theorem gap16 : ¬ DifferentiableAt ℝ F₂ 0 := by
  simpa [F₂, f₂] using gap12

end

end ProofGap.Exercise1016_1

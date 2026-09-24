import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace ProofGap.Exercise1016_2

noncomputable section

def f₁ (x : ℝ) : ℝ := |x|
def g₁ (x : ℝ) : ℝ := x ^ 2
def F₁ (x : ℝ) : ℝ := f₁ (g₁ x)

def f₂ (x : ℝ) : ℝ := |x|
def g₂ (x : ℝ) : ℝ := x
def F₂ (x : ℝ) : ℝ := f₂ (g₂ x)

theorem gap1 (f g : ℝ → ℝ) (x₀ : ℝ) :
    DifferentiableAt ℝ (f ∘ g) x₀ ∨
      ¬ DifferentiableAt ℝ (f ∘ g) x₀ := by
  exact Classical.em _

theorem gap2 : g₁ 0 = 0 := by
  norm_num [g₁]

theorem gap3 : ¬ DifferentiableAt ℝ f₁ 0 := by
  simpa [f₁] using not_differentiableAt_abs_zero

theorem gap4 : DifferentiableAt ℝ g₁ 0 := by
  unfold g₁
  exact ((hasDerivAt_id (0 : ℝ)).pow 2).differentiableAt

theorem gap5 : HasDerivAt g₁ 0 0 := by
  unfold g₁
  convert (hasDerivAt_id (0 : ℝ)).pow 2 using 1 <;> norm_num

theorem gap6 (x : ℝ) : F₁ x = f₁ (g₁ x) := by
  rfl

theorem gap7 (x : ℝ) : f₁ (g₁ x) = |x ^ 2| := by
  rfl

theorem gap8 (x : ℝ) : |x ^ 2| = x ^ 2 := by
  exact abs_of_nonneg (sq_nonneg x)

theorem gap9 (x : ℝ) : F₁ x = x ^ 2 := by
  rw [gap6, gap7, gap8]

theorem gap10 : DifferentiableAt ℝ F₁ 0 := by
  have hF : F₁ = fun x : ℝ => x ^ 2 := funext gap9
  rw [hF]
  exact ((hasDerivAt_id (0 : ℝ)).pow 2).differentiableAt

theorem gap11 : HasDerivAt F₁ 0 0 := by
  have hF : F₁ = fun x : ℝ => x ^ 2 := funext gap9
  rw [hF]
  convert (hasDerivAt_id (0 : ℝ)).pow 2 using 1 <;> norm_num

theorem gap12 : g₂ 0 = 0 := by
  rfl

theorem gap13 : ¬ DifferentiableAt ℝ f₂ 0 := by
  simpa [f₂] using not_differentiableAt_abs_zero

theorem gap14 : DifferentiableAt ℝ g₂ 0 := by
  unfold g₂
  exact (hasDerivAt_id (0 : ℝ)).differentiableAt

theorem gap15 (x : ℝ) : F₂ x = f₂ (g₂ x) := by
  rfl

theorem gap16 (x : ℝ) : f₂ (g₂ x) = |x| := by
  rfl

theorem gap17 (x : ℝ) : F₂ x = |x| := by
  rw [gap15, gap16]

theorem gap18 : ¬ DifferentiableAt ℝ F₂ 0 := by
  have hF : F₂ = abs := funext gap17
  rw [hF]
  exact not_differentiableAt_abs_zero

end

end ProofGap.Exercise1016_2

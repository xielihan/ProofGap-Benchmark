import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Add

namespace ProofGap.Exercise1016_3

noncomputable section

def f₁ (x : ℝ) : ℝ := 2 * x + |x|
def g₁ (x : ℝ) : ℝ := (2 / 3 : ℝ) * x - (1 / 3 : ℝ) * |x|
def F₁ (x : ℝ) : ℝ := f₁ (g₁ x)

def f₂ (x : ℝ) : ℝ := |x|
def g₂ (x : ℝ) : ℝ := |x|
def F₂ (x : ℝ) : ℝ := f₂ (g₂ x)

theorem gap1 (f g : ℝ → ℝ) (x₀ : ℝ) :
    DifferentiableAt ℝ (f ∘ g) x₀ ∨
      ¬ DifferentiableAt ℝ (f ∘ g) x₀ := by
  exact Classical.em _

theorem gap2 : g₁ 0 = 0 := by
  norm_num [g₁]

theorem gap3 : ¬ DifferentiableAt ℝ f₁ 0 := by
  intro hf
  apply not_differentiableAt_abs_zero
  have habs :
      DifferentiableAt ℝ (fun x : ℝ => f₁ x - 2 * x) 0 :=
    hf.sub (differentiableAt_id.const_mul 2)
  convert habs using 1
  funext x
  simp [f₁]

theorem gap4 : ¬ DifferentiableAt ℝ g₁ 0 := by
  intro hg
  apply not_differentiableAt_abs_zero
  have habs :
      DifferentiableAt ℝ (fun x : ℝ => 2 * x - 3 * g₁ x) 0 :=
    (differentiableAt_id.const_mul 2).sub (hg.const_mul 3)
  convert habs using 1
  funext x
  simp [g₁]
  ring

theorem gap5 (x : ℝ) : F₁ x = f₁ (g₁ x) := by
  rfl

theorem gap6 (x : ℝ) :
    f₁ (g₁ x) =
      2 * ((2 / 3 : ℝ) * x - (1 / 3 : ℝ) * |x|) +
        |((2 / 3 : ℝ) * x - (1 / 3 : ℝ) * |x|)| := by
  rfl

theorem gap7 (x : ℝ) :
    2 * ((2 / 3 : ℝ) * x - (1 / 3 : ℝ) * |x|) +
      |((2 / 3 : ℝ) * x - (1 / 3 : ℝ) * |x|)| = x := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    have hg :
        0 ≤ (2 / 3 : ℝ) * x - (1 / 3 : ℝ) * x := by
      linarith
    rw [abs_of_nonneg hg]
    ring
  · rw [abs_of_neg hx]
    have hg :
        (2 / 3 : ℝ) * x - (1 / 3 : ℝ) * -x < 0 := by
      linarith
    rw [abs_of_neg hg]
    ring

theorem gap8 (x : ℝ) : F₁ x = x := by
  rw [gap5, gap6, gap7]

theorem gap9 : DifferentiableAt ℝ F₁ 0 := by
  have hF : F₁ = id := funext gap8
  rw [hF]
  exact differentiableAt_id

theorem gap10 : HasDerivAt F₁ 1 0 := by
  have hF : F₁ = id := funext gap8
  rw [hF]
  exact hasDerivAt_id 0

theorem gap11 : g₂ 0 = 0 := by
  norm_num [g₂]

theorem gap12 : ¬ DifferentiableAt ℝ f₂ 0 := by
  simpa [f₂] using not_differentiableAt_abs_zero

theorem gap13 : ¬ DifferentiableAt ℝ g₂ 0 := by
  simpa [g₂] using not_differentiableAt_abs_zero

theorem gap14 (x : ℝ) : F₂ x = f₂ (g₂ x) := by
  rfl

theorem gap15 (x : ℝ) : f₂ (g₂ x) = |x| := by
  exact abs_abs x

theorem gap16 (x : ℝ) : F₂ x = |x| := by
  rw [gap14, gap15]

theorem gap17 : ¬ DifferentiableAt ℝ F₂ 0 := by
  have hF : F₂ = abs := funext gap16
  rw [hF]
  exact not_differentiableAt_abs_zero

end

end ProofGap.Exercise1016_3

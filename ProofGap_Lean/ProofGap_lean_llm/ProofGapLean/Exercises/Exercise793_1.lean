import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise793_1

def f (x : ℝ) : ℝ := x ^ 2

theorem gap1 (l : ℝ) (hl : 0 < l) (x₁ x₂ : ℝ)
    (h₁ : x₁ ∈ Set.Ioo (-l) l) (h₂ : x₂ ∈ Set.Ioo (-l) l) :
    |f x₁ - f x₂| ≤ 2 * l * |x₁ - x₂| := by
  have hsum : |x₁ + x₂| ≤ 2 * l := by
    rw [abs_le]
    constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]
  have hfactor : f x₁ - f x₂ = (x₁ + x₂) * (x₁ - x₂) := by
    unfold f
    ring
  rw [hfactor, abs_mul]
  exact mul_le_mul_of_nonneg_right hsum (abs_nonneg _)
theorem gap2 (l ε : ℝ) (hl : 0 < l) (hε : 0 < ε) :
    ∃ δ > 0, ∀ x₁ x₂ : ℝ, x₁ ∈ Set.Ioo (-l) l →
      x₂ ∈ Set.Ioo (-l) l → |x₁ - x₂| < δ → |f x₁ - f x₂| < ε := by
  have hc : 0 < 2 * l := mul_pos zero_lt_two hl
  refine ⟨ε / (2 * l), div_pos hε hc, ?_⟩
  intro x₁ x₂ hx₁ hx₂ hdist
  have hbound := gap1 l hl x₁ x₂ hx₁ hx₂
  have hprod : 2 * l * |x₁ - x₂| < ε := by
    have h := (lt_div_iff₀ hc).1 hdist
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  exact lt_of_le_of_lt hbound hprod
theorem gap3 (l : ℝ) (hl : 0 < l) : UniformContinuousOn f (Set.Ioo (-l) l) := by
  rw [Metric.uniformContinuousOn_iff]
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := gap2 l ε hl hε
  refine ⟨δ, hδ, ?_⟩
  intro x₁ hx₁ x₂ hx₂ hdist
  have hout := h x₁ x₂ hx₁ hx₂ (by simpa [Real.dist_eq] using hdist)
  simpa [Real.dist_eq] using hout
theorem gap4 (l : ℝ) (hl : 0 < l) : UniformContinuousOn f (Set.Ioo (-l) l) := by
  exact gap3 l hl

end ProofGap.Exercise793_1

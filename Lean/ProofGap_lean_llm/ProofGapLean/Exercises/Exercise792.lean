import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace ProofGap.Exercise792

noncomputable section

def f (x : ℝ) : ℝ := x + Real.sin x

theorem gap1 (x₁ x₂ : ℝ) :
    |f x₁ - f x₂| = |x₁ - x₂ + Real.sin x₁ - Real.sin x₂| := by
  congr 1
  unfold f
  ring
theorem gap2 (x₁ x₂ : ℝ) :
    |x₁ - x₂ + Real.sin x₁ - Real.sin x₂| ≤
      |x₁ - x₂| + |Real.sin x₁ - Real.sin x₂| := by
  convert abs_add_le (x₁ - x₂) (Real.sin x₁ - Real.sin x₂) using 1 <;>
    ring
theorem gap3 (x₁ x₂ : ℝ) :
    |x₁ - x₂| + |Real.sin x₁ - Real.sin x₂| ≤ 2 * |x₁ - x₂| := by
  linarith [Real.abs_sin_sub_sin_le x₁ x₂]
theorem gap4 (x₁ x₂ : ℝ) : |f x₁ - f x₂| ≤ 2 * |x₁ - x₂| := by
  rw [gap1]
  exact (gap2 x₁ x₂).trans (gap3 x₁ x₂)
theorem gap5 (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ x₁ x₂ : ℝ, |x₁ - x₂| < δ → |f x₁ - f x₂| < ε := by
  refine ⟨ε / 2, by positivity, ?_⟩
  intro x₁ x₂ hdist
  exact lt_of_le_of_lt (gap4 x₁ x₂) (by linarith)
theorem gap6 : UniformContinuous f := by
  have hlip : LipschitzWith 2 f :=
    LipschitzWith.of_dist_le_mul fun x₁ x₂ => by
      simpa [Real.dist_eq] using gap4 x₁ x₂
  exact hlip.uniformContinuous
theorem gap7 : UniformContinuous f := by
  exact gap6

end
end ProofGap.Exercise792

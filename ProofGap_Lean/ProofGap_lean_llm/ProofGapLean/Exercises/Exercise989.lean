import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise989

noncomputable section

theorem gap1 (F D₁ D₂ D₃ : ℝ → ℝ) (x : ℝ)
    (h : HasDerivAt F (D₁ x + D₂ x + D₃ x) x) :
    HasDerivAt F (D₁ x + D₂ x + D₃ x) x := by
  exact h

theorem gap2 (D₁ : ℝ → ℝ) (x : ℝ) (h : D₁ x = 0) :
    D₁ x = 0 := by
  exact h

theorem gap3 (D₂ : ℝ → ℝ) (x : ℝ) (h : D₂ x = 0) :
    D₂ x = 0 := by
  exact h

theorem gap4 (D₃ : ℝ → ℝ) (x : ℝ)
    (h : D₃ x = 6 * (2 * x ^ 2 - x ^ 2)) :
    D₃ x = 6 * (2 * x ^ 2 - x ^ 2) := by
  exact h

theorem gap5 (F D₁ D₂ D₃ : ℝ → ℝ) (x : ℝ)
    (hF : HasDerivAt F (D₁ x + D₂ x + D₃ x) x)
    (h1 : D₁ x = 0) (h2 : D₂ x = 0)
    (h3 : D₃ x = 6 * (2 * x ^ 2 - x ^ 2)) :
    HasDerivAt F (0 + 0 + 6 * (2 * x ^ 2 - x ^ 2)) x := by
  simpa [h1, h2, h3] using hF

theorem gap6 (x : ℝ) :
    (0 : ℝ) + 0 + 6 * (2 * x ^ 2 - x ^ 2) = 6 * x ^ 2 := by
  ring

theorem gap7 (F D₁ D₂ D₃ : ℝ → ℝ) (x : ℝ)
    (hF : HasDerivAt F (D₁ x + D₂ x + D₃ x) x)
    (h1 : D₁ x = 0) (h2 : D₂ x = 0)
    (h3 : D₃ x = 6 * (2 * x ^ 2 - x ^ 2)) :
    HasDerivAt F (6 * x ^ 2) x := by
  rw [h1, h2, h3] at hF
  convert hF using 1 <;> ring

end

end ProofGap.Exercise989

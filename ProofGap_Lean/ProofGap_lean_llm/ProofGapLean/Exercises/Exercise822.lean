import ProofGapLean.Prelude.Core
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise822

/-- Exercise 822, gap 1. -/
theorem gap1 (Δx : ℝ) (h : Δx = 0.001 - 0.01) : Δx = 0.001 - 0.01 := h

/-- Exercise 822, gap 2. -/
theorem gap2 : (0.001 : ℝ) - 0.01 = -0.009 := by norm_num

/-- Exercise 822, gap 3. -/
theorem gap3 (Δx : ℝ) (h : Δx = 0.001 - 0.01) : Δx = -0.009 := by
  rw [h]
  norm_num

/-- Exercise 822, gap 4. -/
theorem gap4 (Δy : ℝ) (h : Δy = 1 / (0.001 : ℝ) ^ 2 - 1 / (0.01 : ℝ) ^ 2) :
    Δy = 1 / (0.001 : ℝ) ^ 2 - 1 / (0.01 : ℝ) ^ 2 := h

/-- Exercise 822, gap 5. -/
theorem gap5 : 1 / (0.001 : ℝ) ^ 2 - 1 / (0.01 : ℝ) ^ 2 = 990000 := by
  norm_num

/-- Exercise 822, gap 6. -/
theorem gap6 (Δy : ℝ) (h : Δy = 1 / (0.001 : ℝ) ^ 2 - 1 / (0.01 : ℝ) ^ 2) :
    Δy = 990000 := by
  rw [h]
  norm_num

end ProofGap.Exercise822

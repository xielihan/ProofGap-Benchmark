import ProofGapLean.Prelude.Core
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise822

/-- Source: `proof_gap/exercise_822/1.txt`. -/
theorem gap1 (Δx : ℝ) (h : Δx = 0.001 - 0.01) : Δx = 0.001 - 0.01 := h

/-- Source: `proof_gap/exercise_822/2.txt`. -/
theorem gap2 : (0.001 : ℝ) - 0.01 = -0.009 := by norm_num

/-- Source: `proof_gap/exercise_822/3.txt`. -/
theorem gap3 (Δx : ℝ) (h : Δx = 0.001 - 0.01) : Δx = -0.009 := by
  rw [h]
  norm_num

/-- Source: `proof_gap/exercise_822/4.txt`. -/
theorem gap4 (Δy : ℝ) (h : Δy = 1 / (0.001 : ℝ) ^ 2 - 1 / (0.01 : ℝ) ^ 2) :
    Δy = 1 / (0.001 : ℝ) ^ 2 - 1 / (0.01 : ℝ) ^ 2 := h

/-- Source: `proof_gap/exercise_822/5.txt`. -/
theorem gap5 : 1 / (0.001 : ℝ) ^ 2 - 1 / (0.01 : ℝ) ^ 2 = 990000 := by
  norm_num

/-- Source: `proof_gap/exercise_822/6.txt`. -/
theorem gap6 (Δy : ℝ) (h : Δy = 1 / (0.001 : ℝ) ^ 2 - 1 / (0.01 : ℝ) ^ 2) :
    Δy = 990000 := by
  rw [h]
  norm_num

end ProofGap.Exercise822

import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise821

noncomputable section

def y (x : ℝ) : ℝ := Real.logb 10 x

def Δx : ℝ := 1000 - 1

def Δy : ℝ := y 1000 - y 1

/-- Source: `proof_gap/exercise_821/1.txt`; define the increment from the two endpoints. -/
theorem gap1 : Δx = (1000 : ℝ) - 1 := by
  rfl

/-- Source: `proof_gap/exercise_821/2.txt`. -/
theorem gap2 : (1000 : ℝ) - 1 = 999 := by
  norm_num

/-- Source: `proof_gap/exercise_821/3.txt`; identify `Δx` with the endpoint difference. -/
theorem gap3 : Δx = 999 := by
  exact gap1.trans gap2

/-- Source: `proof_gap/exercise_821/4.txt`; define the output increment. -/
theorem gap4 : Δy = Real.logb 10 1000 - Real.logb 10 1 := by
  rfl

/-- Source: `proof_gap/exercise_821/5.txt`. -/
theorem gap5 : Real.logb 10 1000 - Real.logb 10 1 = 3 := by
  have hlog : Real.log (10 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  rw [show (1000 : ℝ) = 10 ^ 3 by norm_num]
  simp [Real.logb, Real.log_pow, hlog]

/-- Source: `proof_gap/exercise_821/6.txt`; identify `Δy` with the endpoint difference. -/
theorem gap6 : Δy = 3 := by
  exact gap4.trans gap5

end

end ProofGap.Exercise821

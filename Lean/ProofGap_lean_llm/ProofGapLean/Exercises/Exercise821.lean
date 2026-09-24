import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise821

noncomputable section

def y (x : ℝ) : ℝ := Real.logb 10 x

def Δx : ℝ := 1000 - 1

def Δy : ℝ := y 1000 - y 1

/-- Exercise 821, gap 1; define the increment from the two endpoints. -/
theorem gap1 : Δx = (1000 : ℝ) - 1 := by
  rfl

/-- Exercise 821, gap 2. -/
theorem gap2 : (1000 : ℝ) - 1 = 999 := by
  norm_num

/-- Exercise 821, gap 3; identify `Δx` with the endpoint difference. -/
theorem gap3 : Δx = 999 := by
  exact gap1.trans gap2

/-- Exercise 821, gap 4; define the output increment. -/
theorem gap4 : Δy = Real.logb 10 1000 - Real.logb 10 1 := by
  rfl

/-- Exercise 821, gap 5. -/
theorem gap5 : Real.logb 10 1000 - Real.logb 10 1 = 3 := by
  have hlog : Real.log (10 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  rw [show (1000 : ℝ) = 10 ^ 3 by norm_num]
  simp [Real.logb, Real.log_pow, hlog]

/-- Exercise 821, gap 6; identify `Δy` with the endpoint difference. -/
theorem gap6 : Δy = 3 := by
  exact gap4.trans gap5

end

end ProofGap.Exercise821

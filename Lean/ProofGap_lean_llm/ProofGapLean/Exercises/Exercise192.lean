import ProofGapLean.Prelude.Elementary

namespace ProofGap.Exercise192

noncomputable section

def f (x : ℝ) : ℝ := if x ≤ 0 then 1 + x else Real.rpow 2 x

/-- Source: `proof_gap/exercise_192/1.txt`. -/
theorem gap1 : f (-2) = 1 - 2 := by
  norm_num [f]

/-- Source: `proof_gap/exercise_192/2.txt`. -/
theorem gap2 : (1 : ℝ) - 2 = -1 := by
  norm_num

/-- Source: `proof_gap/exercise_192/3.txt`. -/
theorem gap3 : f (-2) = -1 := by
  rw [gap1, gap2]

/-- Source: `proof_gap/exercise_192/4.txt`. -/
theorem gap4 : f (-1) = 1 - 1 := by
  norm_num [f]

/-- Source: `proof_gap/exercise_192/5.txt`. -/
theorem gap5 : (1 : ℝ) - 1 = 0 := by
  norm_num

/-- Source: `proof_gap/exercise_192/6.txt`. -/
theorem gap6 : f (-1) = 0 := by
  rw [gap4, gap5]

/-- Source: `proof_gap/exercise_192/7.txt`. -/
theorem gap7 : f 0 = 1 + 0 := by
  norm_num [f]

/-- Source: `proof_gap/exercise_192/8.txt`. -/
theorem gap8 : (1 : ℝ) + 0 = 1 := by
  norm_num

/-- Source: `proof_gap/exercise_192/9.txt`. -/
theorem gap9 : f 0 = 1 := by
  rw [gap7, gap8]

/-- Source: `proof_gap/exercise_192/10.txt`. -/
theorem gap10 : f 1 = Real.rpow 2 1 := by
  norm_num [f]

/-- Source: `proof_gap/exercise_192/11.txt`. -/
theorem gap11 : Real.rpow 2 1 = 2 := by
  norm_num

/-- Source: `proof_gap/exercise_192/12.txt`. -/
theorem gap12 : f 1 = 2 := by
  rw [gap10, gap11]

/-- Source: `proof_gap/exercise_192/13.txt`. -/
theorem gap13 : f 2 = Real.rpow 2 2 := by
  norm_num [f]

/-- Source: `proof_gap/exercise_192/14.txt`. -/
theorem gap14 : Real.rpow 2 2 = 4 := by
  norm_num [Real.rpow_natCast]

/-- Source: `proof_gap/exercise_192/15.txt`. -/
theorem gap15 : f 2 = 4 := by
  rw [gap13, gap14]

end

end ProofGap.Exercise192

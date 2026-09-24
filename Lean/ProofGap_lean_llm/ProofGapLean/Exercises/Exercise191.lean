import ProofGapLean.Prelude.Discrete

namespace ProofGap.Exercise191

noncomputable section

def f (x : ℝ) : ℝ := 1 + (⌊x⌋ : ℤ)

/-- Source: `proof_gap/exercise_191/1.txt`. -/
theorem gap1 : f 0.9 = f 0.99 := by
  norm_num [f]

/-- Source: `proof_gap/exercise_191/2.txt`. -/
theorem gap2 : f 0.99 = f 0.999 := by
  norm_num [f]

/-- Source: `proof_gap/exercise_191/3.txt`. -/
theorem gap3 : f 0.999 = 1 := by
  norm_num [f]

/-- Source: `proof_gap/exercise_191/4.txt`. -/
theorem gap4 : f 0.9 = 1 := by
  norm_num [f]

/-- Source: `proof_gap/exercise_191/5.txt`. -/
theorem gap5 : f 1 = 2 := by
  norm_num [f]

end

end ProofGap.Exercise191

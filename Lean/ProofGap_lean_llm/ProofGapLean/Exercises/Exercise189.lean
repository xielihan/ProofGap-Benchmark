import ProofGapLean.Prelude.Core
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise189

def f (x : ℝ) : ℝ := x ^ 4 - 6 * x ^ 3 + 11 * x ^ 2 - 6 * x

/-- Source: `proof_gap/exercise_189/1.txt`. -/
theorem gap1 : ∀ x : ℝ, f x = x * (x - 1) * (x - 2) * (x - 3) := by
  intro x
  unfold f
  ring

/-- Source: `proof_gap/exercise_189/2.txt`. -/
theorem gap2 : f 0 = f 1 := by
  norm_num [f]

/-- Source: `proof_gap/exercise_189/3.txt`. -/
theorem gap3 : f 1 = f 2 := by
  norm_num [f]

/-- Source: `proof_gap/exercise_189/4.txt`. -/
theorem gap4 : f 2 = f 3 := by
  norm_num [f]

/-- Source: `proof_gap/exercise_189/5.txt`. -/
theorem gap5 : f 3 = 0 := by
  norm_num [f]

/-- Source: `proof_gap/exercise_189/6.txt`. -/
theorem gap6 : f 0 = 0 := by
  norm_num [f]

/-- Source: `proof_gap/exercise_189/7.txt`. -/
theorem gap7 : f 4 = 24 := by
  norm_num [f]

end ProofGap.Exercise189

import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise190

noncomputable section

def lg (x : ℝ) : ℝ := Real.log x / Real.log 10
def f (x : ℝ) : ℝ := lg (x ^ 2)

/-- Source: `proof_gap/exercise_190/1.txt`. -/
theorem gap1 : f (-1) = lg 1 := by
  norm_num [f]

/-- Source: `proof_gap/exercise_190/2.txt`. -/
theorem gap2 : lg 1 = 0 := by
  simp [lg]

/-- Source: `proof_gap/exercise_190/3.txt`. -/
theorem gap3 : f (-1) = 0 := by
  rw [gap1, gap2]

/-- Source: `proof_gap/exercise_190/4.txt`. -/
theorem gap4 : f (-0.001) = lg 0.000001 := by
  norm_num [f]

/-- Source: `proof_gap/exercise_190/5.txt`. -/
theorem gap5 : lg 0.000001 = -6 := by
  unfold lg
  rw [show (0.000001 : ℝ) = ((10 : ℝ) ^ 6)⁻¹ by norm_num,
    Real.log_inv, Real.log_pow]
  have hlog10 : Real.log 10 ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  field_simp [hlog10]
  norm_num

/-- Source: `proof_gap/exercise_190/6.txt`. -/
theorem gap6 : f (-0.001) = -6 := by
  rw [gap4, gap5]

/-- Source: `proof_gap/exercise_190/7.txt`. -/
theorem gap7 : f 100 = lg 10000 := by
  norm_num [f]

/-- Source: `proof_gap/exercise_190/8.txt`. -/
theorem gap8 : lg 10000 = 4 := by
  unfold lg
  rw [show (10000 : ℝ) = 10 ^ 4 by norm_num, Real.log_pow]
  have hlog10 : Real.log 10 ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  field_simp [hlog10]
  norm_num

/-- Source: `proof_gap/exercise_190/9.txt`. -/
theorem gap9 : f 100 = 4 := by
  rw [gap7, gap8]

end

end ProofGap.Exercise190

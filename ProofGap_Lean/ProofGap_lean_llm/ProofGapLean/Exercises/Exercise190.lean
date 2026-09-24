import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise190

noncomputable section

def lg (x : ℝ) : ℝ := Real.log x / Real.log 10
def f (x : ℝ) : ℝ := lg (x ^ 2)

/-- Exercise 190, gap 1. -/
theorem gap1 : f (-1) = lg 1 := by
  norm_num [f]

/-- Exercise 190, gap 2. -/
theorem gap2 : lg 1 = 0 := by
  simp [lg]

/-- Exercise 190, gap 3. -/
theorem gap3 : f (-1) = 0 := by
  rw [gap1, gap2]

/-- Exercise 190, gap 4. -/
theorem gap4 : f (-0.001) = lg 0.000001 := by
  norm_num [f]

/-- Exercise 190, gap 5. -/
theorem gap5 : lg 0.000001 = -6 := by
  unfold lg
  rw [show (0.000001 : ℝ) = ((10 : ℝ) ^ 6)⁻¹ by norm_num,
    Real.log_inv, Real.log_pow]
  have hlog10 : Real.log 10 ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  field_simp [hlog10]
  norm_num

/-- Exercise 190, gap 6. -/
theorem gap6 : f (-0.001) = -6 := by
  rw [gap4, gap5]

/-- Exercise 190, gap 7. -/
theorem gap7 : f 100 = lg 10000 := by
  norm_num [f]

/-- Exercise 190, gap 8. -/
theorem gap8 : lg 10000 = 4 := by
  unfold lg
  rw [show (10000 : ℝ) = 10 ^ 4 by norm_num, Real.log_pow]
  have hlog10 : Real.log 10 ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  field_simp [hlog10]
  norm_num

/-- Exercise 190, gap 9. -/
theorem gap9 : f 100 = 4 := by
  rw [gap7, gap8]

end

end ProofGap.Exercise190

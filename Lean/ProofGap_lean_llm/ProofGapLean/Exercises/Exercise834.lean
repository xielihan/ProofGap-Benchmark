import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise834

def y (x : ℝ) : ℝ := 2 + x - x ^ 2

/-- Exercise 834, gap 1. -/
theorem gap1 (x : ℝ) : HasDerivAt y (1 - 2 * x) x := by
  convert
    (((hasDerivAt_const x (2 : ℝ)).add (hasDerivAt_id x)).sub
      ((hasDerivAt_id x).mul (hasDerivAt_id x))) using 1
  · funext z
    simp [y, pow_two]
  · simp [id, two_mul]

/-- Exercise 834, gap 2. -/
theorem gap2 : HasDerivAt y 1 0 := by
  convert gap1 (0 : ℝ) using 1 <;> norm_num

/-- Exercise 834, gap 3. -/
theorem gap3 : HasDerivAt y 0 ((1 : ℝ) / 2) := by
  convert gap1 ((1 : ℝ) / 2) using 1 <;> norm_num

/-- Exercise 834, gap 4. -/
theorem gap4 : HasDerivAt y (-1) 1 := by
  convert gap1 (1 : ℝ) using 1 <;> norm_num

/-- Exercise 834, gap 5. -/
theorem gap5 : HasDerivAt y 21 (-10) := by
  convert gap1 (-10 : ℝ) using 1 <;> norm_num

end ProofGap.Exercise834

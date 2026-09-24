import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise845

noncomputable section

def y (x : ℝ) : ℝ := 2 * x / (1 - x ^ 2)

/-- Source: `proof_gap/exercise_845/1.txt`; add the omitted condition
`1 - x^2 ≠ 0`. -/
theorem gap1 (x : ℝ) (hden : 1 - x ^ 2 ≠ 0) :
    HasDerivAt y
      ((2 * (1 - x ^ 2) + 4 * x ^ 2) / (1 - x ^ 2) ^ 2) x := by
  unfold y
  have hnum : HasDerivAt (fun z : ℝ => 2 * z) 2 x := by
    simpa only [zero_mul, zero_add, mul_one] using
      (hasDerivAt_const x (2 : ℝ)).mul (hasDerivAt_id x)
  have hsq : HasDerivAt (fun z : ℝ => z * z) (x + x) x := by
    simpa only [one_mul, mul_one] using
      (hasDerivAt_id x).mul (hasDerivAt_id x)
  have hden' : HasDerivAt (fun z : ℝ => 1 - z ^ 2) (-(x + x)) x := by
    simpa only [pow_two, zero_sub] using
      (hasDerivAt_const x (1 : ℝ)).sub hsq
  convert hnum.div hden' hden using 1 <;> ring

/-- Source: `proof_gap/exercise_845/2.txt`; retain the rational expression's
domain condition. -/
theorem gap2 (x : ℝ) (hden : 1 - x ^ 2 ≠ 0) :
    (2 * (1 - x ^ 2) + 4 * x ^ 2) / (1 - x ^ 2) ^ 2 =
      2 * (1 + x ^ 2) / (1 - x ^ 2) ^ 2 := by
  ring

/-- Source: `proof_gap/exercise_845/3.txt`; add the omitted condition
`|x| ≠ 1`, equivalently `1 - x^2 ≠ 0`. -/
theorem gap3 (x : ℝ) (hden : 1 - x ^ 2 ≠ 0) :
    HasDerivAt y (2 * (1 + x ^ 2) / (1 - x ^ 2) ^ 2) x := by
  simpa only [gap2 x hden] using gap1 x hden

end

end ProofGap.Exercise845

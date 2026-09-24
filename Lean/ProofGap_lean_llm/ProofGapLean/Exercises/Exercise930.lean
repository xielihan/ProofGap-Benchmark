import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise930

noncomputable section

def y (x : ℝ) : ℝ :=
  Real.arctan x + (1 / 3) * Real.arctan (x ^ 3)

def expandedDerivative (x : ℝ) : ℝ :=
  1 / (1 + x ^ 2) + x ^ 2 / (1 + x ^ 6)

def finalDerivative (x : ℝ) : ℝ :=
  (1 + x ^ 4) / (1 + x ^ 6)

/-- Source: `proof_gap/exercise_930/1.txt`. -/
theorem gap1 (x : ℝ) :
    HasDerivAt y (expandedDerivative x) x := by
  unfold y expandedDerivative
  have hden3 : 1 + (x ^ 3) ^ 2 ≠ 0 := by positivity
  have hden6 : 1 + x ^ 6 ≠ 0 := by positivity
  have hCubic :
      HasDerivAt (fun t : ℝ => (1 / 3) * Real.arctan (t ^ 3))
        (x ^ 2 / (1 + x ^ 6)) x := by
    convert (((Real.hasDerivAt_arctan (x ^ 3)).comp x
      (hasDerivAt_pow 3 x)).const_mul (1 / 3)) using 1 <;>
      field_simp [hden3, hden6] <;> ring
  exact (Real.hasDerivAt_arctan x).add hCubic

/-- Source: `proof_gap/exercise_930/2.txt`. -/
theorem gap2 (x : ℝ) :
    expandedDerivative x = finalDerivative x := by
  unfold expandedDerivative finalDerivative
  have h2 : 0 < 1 + x ^ 2 := by positivity
  have h6 : 0 < 1 + x ^ 6 := by positivity
  field_simp [ne_of_gt h2, ne_of_gt h6]
  ring

/-- Source: `proof_gap/exercise_930/3.txt`. -/
theorem gap3 (x : ℝ) :
    HasDerivAt y (finalDerivative x) x := by
  rw [← gap2 x]
  exact gap1 x

end

end ProofGap.Exercise930

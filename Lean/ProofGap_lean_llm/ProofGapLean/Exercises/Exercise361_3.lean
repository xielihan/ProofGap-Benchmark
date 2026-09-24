import ProofGapLean.Prelude.Core

namespace ProofGap.Exercise361_3

noncomputable section

def cubic (a b c d x : ℝ) : ℝ :=
  a * x ^ 3 + b * x ^ 2 + c * x + d

def centerX (a b : ℝ) : ℝ := -b / (3 * a)
def centerY (a b c d : ℝ) : ℝ := cubic a b c d (centerX a b)

/-- Source: `proof_gap/exercise_361_3/1.txt`; a genuine cubic requires `a≠0`. -/
theorem gap1 (a b : ℝ) (ha : a ≠ 0) :
    centerX a b = -b / (3 * a) := by
  rfl

/-- Source: `proof_gap/exercise_361_3/2.txt`. -/
theorem gap2 (a b c d : ℝ) (ha : a ≠ 0) :
    centerY a b c d =
      a * centerX a b ^ 3 + b * centerX a b ^ 2 +
        c * centerX a b + d := by
  rfl

end

end ProofGap.Exercise361_3

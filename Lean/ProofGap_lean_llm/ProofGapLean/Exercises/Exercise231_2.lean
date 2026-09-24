import ProofGapLean.Prelude.Elementary

namespace ProofGap.Exercise231_2

noncomputable section

def f (x : ℝ) : ℝ :=
  Real.rpow ((1 - x) ^ 2) (1 / 3 : ℝ) +
    Real.rpow ((1 + x) ^ 2) (1 / 3 : ℝ)

/-- Source: `proof_gap/exercise_231_2/1.txt`. -/
theorem gap1 : ∀ x, f (-x) =
    Real.rpow ((1 + x) ^ 2) (1 / 3 : ℝ) +
      Real.rpow ((1 - x) ^ 2) (1 / 3 : ℝ) := by
  intro x
  simp [f]
  congr 1

/-- Source: `proof_gap/exercise_231_2/2.txt`. -/
theorem gap2 : ∀ x,
    Real.rpow ((1 + x) ^ 2) (1 / 3 : ℝ) +
      Real.rpow ((1 - x) ^ 2) (1 / 3 : ℝ) = f x := by
  intro x
  simp [f, add_comm]

/-- Source: `proof_gap/exercise_231_2/3.txt`. -/
theorem gap3 : ∀ x, f (-x) = f x := by
  intro x
  rw [gap1 x, gap2 x]

/-- Source: `proof_gap/exercise_231_2/4.txt`. -/
theorem gap4 : Function.Even f := by
  intro x
  exact gap3 x

end

end ProofGap.Exercise231_2

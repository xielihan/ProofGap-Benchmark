import ProofGapLean.Prelude.Elementary

namespace ProofGap.Exercise231_2

noncomputable section

def f (x : ℝ) : ℝ :=
  Real.rpow ((1 - x) ^ 2) (1 / 3 : ℝ) +
    Real.rpow ((1 + x) ^ 2) (1 / 3 : ℝ)

/-- Exercise 231_2, gap 1. -/
theorem gap1 : ∀ x, f (-x) =
    Real.rpow ((1 + x) ^ 2) (1 / 3 : ℝ) +
      Real.rpow ((1 - x) ^ 2) (1 / 3 : ℝ) := by
  intro x
  simp [f]
  congr 1

/-- Exercise 231_2, gap 2. -/
theorem gap2 : ∀ x,
    Real.rpow ((1 + x) ^ 2) (1 / 3 : ℝ) +
      Real.rpow ((1 - x) ^ 2) (1 / 3 : ℝ) = f x := by
  intro x
  simp [f, add_comm]

/-- Exercise 231_2, gap 3. -/
theorem gap3 : ∀ x, f (-x) = f x := by
  intro x
  rw [gap1 x, gap2 x]

/-- Exercise 231_2, gap 4. -/
theorem gap4 : Function.Even f := by
  intro x
  exact gap3 x

end

end ProofGap.Exercise231_2

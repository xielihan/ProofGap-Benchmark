import ProofGapLean.Prelude.Elementary

namespace ProofGap.Exercise231_3

noncomputable section

def f (a x : ℝ) : ℝ := Real.rpow a x + Real.rpow a (-x)

/-- Exercise 231_3, gap 1. -/
theorem gap1 (a : ℝ) (ha : 0 < a) : ∀ x,
    f a (-x) = Real.rpow a (-x) + Real.rpow a x := by
  intro x
  simp [f]

/-- Exercise 231_3, gap 2. -/
theorem gap2 (a : ℝ) (ha : 0 < a) : ∀ x,
    Real.rpow a (-x) + Real.rpow a x = f a x := by
  intro x
  simp [f, add_comm]

/-- Exercise 231_3, gap 3. -/
theorem gap3 (a : ℝ) (ha : 0 < a) : ∀ x, f a (-x) = f a x := by
  intro x
  rw [gap1 a ha x, gap2 a ha x]

/-- Exercise 231_3, gap 4. -/
theorem gap4 (a : ℝ) (ha : 0 < a) : Function.Even (f a) := by
  intro x
  exact gap3 a ha x

end

end ProofGap.Exercise231_3

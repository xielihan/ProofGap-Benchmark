import ProofGapLean.Prelude.Elementary

namespace ProofGap.Exercise231_5

noncomputable section

def f (x : ℝ) : ℝ := Real.log (x + Real.sqrt (1 + x ^ 2))

/-- Exercise 231_5, gap 1. -/
theorem gap1 : ∀ x,
    f (-x) = Real.log (-x + Real.sqrt (1 + x ^ 2)) := by
  intro x
  simp [f]

/-- Exercise 231_5, gap 2. -/
theorem gap2 : ∀ x,
    Real.log (-x + Real.sqrt (1 + x ^ 2)) =
      Real.log (1 / (x + Real.sqrt (1 + x ^ 2))) := by
  intro x
  apply congrArg Real.log
  have hnonneg : 0 ≤ 1 + x ^ 2 := by
    positivity
  have hsqrt_sq :
      (Real.sqrt (1 + x ^ 2)) ^ 2 = 1 + x ^ 2 :=
    Real.sq_sqrt hnonneg
  have hne : x + Real.sqrt (1 + x ^ 2) ≠ 0 := by
    intro hzero
    have hsqrt_eq : Real.sqrt (1 + x ^ 2) = -x := by
      linarith
    rw [hsqrt_eq] at hsqrt_sq
    nlinarith
  field_simp [hne]
  nlinarith

/-- Exercise 231_5, gap 3. -/
theorem gap3 : ∀ x,
    Real.log (1 / (x + Real.sqrt (1 + x ^ 2))) =
      -Real.log (x + Real.sqrt (1 + x ^ 2)) := by
  intro x
  simpa [one_div] using
    (Real.log_inv (x + Real.sqrt (1 + x ^ 2)))

/-- Exercise 231_5, gap 4. -/
theorem gap4 : ∀ x,
    -Real.log (x + Real.sqrt (1 + x ^ 2)) = -f x := by
  intro x
  rfl

/-- Exercise 231_5, gap 5. -/
theorem gap5 : ∀ x, f (-x) = -f x := by
  intro x
  calc
    f (-x) = Real.log (-x + Real.sqrt (1 + x ^ 2)) := gap1 x
    _ = Real.log (1 / (x + Real.sqrt (1 + x ^ 2))) := gap2 x
    _ = -Real.log (x + Real.sqrt (1 + x ^ 2)) := gap3 x
    _ = -f x := gap4 x

/-- Exercise 231_5, gap 6. -/
theorem gap6 : Function.Odd f := by
  exact gap5

end

end ProofGap.Exercise231_5

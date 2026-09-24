import ProofGapLean.Prelude.Elementary

namespace ProofGap.Exercise231_5

noncomputable section

def f (x : ℝ) : ℝ := Real.log (x + Real.sqrt (1 + x ^ 2))

/-- Source: `proof_gap/exercise_231_5/1.txt`. -/
theorem gap1 : ∀ x,
    f (-x) = Real.log (-x + Real.sqrt (1 + x ^ 2)) := by
  intro x
  simp [f]

/-- Source: `proof_gap/exercise_231_5/2.txt`. -/
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

/-- Source: `proof_gap/exercise_231_5/3.txt`. -/
theorem gap3 : ∀ x,
    Real.log (1 / (x + Real.sqrt (1 + x ^ 2))) =
      -Real.log (x + Real.sqrt (1 + x ^ 2)) := by
  intro x
  simpa [one_div] using
    (Real.log_inv (x + Real.sqrt (1 + x ^ 2)))

/-- Source: `proof_gap/exercise_231_5/4.txt`. -/
theorem gap4 : ∀ x,
    -Real.log (x + Real.sqrt (1 + x ^ 2)) = -f x := by
  intro x
  rfl

/-- Source: `proof_gap/exercise_231_5/5.txt`. -/
theorem gap5 : ∀ x, f (-x) = -f x := by
  intro x
  calc
    f (-x) = Real.log (-x + Real.sqrt (1 + x ^ 2)) := gap1 x
    _ = Real.log (1 / (x + Real.sqrt (1 + x ^ 2))) := gap2 x
    _ = -Real.log (x + Real.sqrt (1 + x ^ 2)) := gap3 x
    _ = -f x := gap4 x

/-- Source: `proof_gap/exercise_231_5/6.txt`. -/
theorem gap6 : Function.Odd f := by
  exact gap5

end

end ProofGap.Exercise231_5

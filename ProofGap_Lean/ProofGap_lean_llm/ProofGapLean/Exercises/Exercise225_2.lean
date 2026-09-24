import ProofGapLean.Prelude.Elementary

namespace ProofGap.Exercise225_2

noncomputable section

def direct (x : ℝ) : ℝ := x ^ 2
def inverse (y : ℝ) : ℝ := Real.sqrt y

/-- Exercise 225_2, gap 1; y is the image of a nonnegative x. -/
theorem gap1 : ∀ x : ℝ, 0 ≤ x → inverse (direct x) = x := by
  intro x hx
  simp [inverse, direct, Real.sqrt_sq_eq_abs, abs_of_nonneg hx]

end

end ProofGap.Exercise225_2

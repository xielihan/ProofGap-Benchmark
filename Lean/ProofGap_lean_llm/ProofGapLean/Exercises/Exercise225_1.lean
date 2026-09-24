import ProofGapLean.Prelude.Elementary

namespace ProofGap.Exercise225_1

noncomputable section

def direct (x : ℝ) : ℝ := x ^ 2
def inverse (y : ℝ) : ℝ := -Real.sqrt y

/-- Source: `proof_gap/exercise_225_1/1.txt`; y is the image of a nonpositive x. -/
theorem gap1 : ∀ x : ℝ, x ≤ 0 → inverse (direct x) = x := by
  intro x hx
  simp [inverse, direct, Real.sqrt_sq_eq_abs, abs_of_nonpos hx]

end

end ProofGap.Exercise225_1

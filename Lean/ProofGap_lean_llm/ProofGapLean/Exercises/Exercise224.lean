import ProofGapLean.Prelude.Core

namespace ProofGap.Exercise224

noncomputable section

def direct (x : ℝ) : ℝ := 2 * x + 3
def inverse (y : ℝ) : ℝ := (y - 3) / 2

/-- Exercise 224, gap 1; bind y as the direct image of x. -/
theorem gap1 : ∀ x, inverse (direct x) = x := by
  intro x
  simp [inverse, direct]

/-- Exercise 224, gap 2; state the inverse function rather than the source's swapped free variables. -/
theorem gap2 : ∀ y, inverse y = (y - 3) / 2 := by
  intro y
  rfl

end

end ProofGap.Exercise224

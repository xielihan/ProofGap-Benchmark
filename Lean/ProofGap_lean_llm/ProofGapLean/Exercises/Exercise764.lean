import ProofGapLean.Prelude.Core

namespace ProofGap.Exercise764

/-- Source: `proof_gap/exercise_764/1.txt`; interpret equality with the inverse
as the standard involution property. -/
theorem gap1 (f : ℝ → ℝ) :
    Function.Involutive f ↔ ∀ x, x = f (f x) := by
  constructor
  · intro h x
    exact (h x).symm
  · intro h x
    exact (h x).symm

/-- Source: `proof_gap/exercise_764/2.txt`. -/
theorem gap2 (f : ℝ → ℝ) :
    f ∈ {g : ℝ → ℝ | ∀ x, x = g (g x)} ↔ Function.Involutive f := by
  constructor
  · intro h x
    exact (h x).symm
  · intro h x
    exact (h x).symm

end ProofGap.Exercise764

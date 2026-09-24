import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ext

namespace ProofGap.Exercise154_1

def domain : Set ℝ := {x | 0 < x ^ 2 - 4}

/-- Source: `proof_gap/exercise_154_1/1.txt`; the source's unguarded universal inequality is a domain condition. -/
theorem gap1 : ∀ x : ℝ, x ∈ domain ↔ 0 < x ^ 2 - 4 := by
  intro x
  rfl

/-- Source: `proof_gap/exercise_154_1/2.txt`. -/
theorem gap2 : ∀ x : ℝ, x ∈ domain ↔ x < -2 ∨ 2 < x := by
  intro x
  change 0 < x ^ 2 - 4 ↔ x < -2 ∨ 2 < x
  constructor
  · intro h
    by_cases hx : x < -2
    · exact Or.inl hx
    · right
      nlinarith
  · rintro (hx | hx) <;> nlinarith

/-- Source: `proof_gap/exercise_154_1/3.txt`. -/
theorem gap3 : domain = Set.Iio (-2) ∪ Set.Ioi 2 := by
  ext x
  exact gap2 x

end ProofGap.Exercise154_1

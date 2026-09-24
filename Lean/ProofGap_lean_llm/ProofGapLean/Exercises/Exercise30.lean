import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exercise 30

Semantic formalization of Exercise 30, gaps 1,...,4.
-/

namespace ProofGap.Exercise30

def ExpandedIdentity : Prop :=
  ∀ x : ℝ,
    ((x + |x|) / 2) ^ 2 + ((x - |x|) / 2) ^ 2 =
      (1 / 2 : ℝ) * x ^ 2 + (1 / 2 : ℝ) * x * |x| +
        (1 / 2 : ℝ) * x ^ 2 - (1 / 2 : ℝ) * x * |x|

def SimplifiedMiddle : Prop :=
  ∀ x : ℝ,
    (1 / 2 : ℝ) * x ^ 2 + (1 / 2 : ℝ) * x * |x| +
      (1 / 2 : ℝ) * x ^ 2 - (1 / 2 : ℝ) * x * |x| = x ^ 2

def Identity : Prop :=
  ∀ x : ℝ, ((x + |x|) / 2) ^ 2 + ((x - |x|) / 2) ^ 2 = x ^ 2

/-- Exercise 30, gap 1. -/
theorem gap1 : ExpandedIdentity := by
  intro x
  nlinarith [sq_abs x]

/-- Exercise 30, gap 2. -/
theorem gap2 (h1 : ExpandedIdentity) : SimplifiedMiddle := by
  intro x
  ring

/-- Exercise 30, gap 3. -/
theorem gap3
    (h1 : ExpandedIdentity)
    (h2 : SimplifiedMiddle) :
    Identity := by
  intro x
  rw [h1 x, h2 x]

/-- Exercise 30, gap 4. -/
theorem gap4 (h3 : Identity) : Identity := by
  exact h3

end ProofGap.Exercise30

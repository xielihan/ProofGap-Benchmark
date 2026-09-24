import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exercise 30

Semantic formalization of `proof_gap/exercise_30/{1,...,4}.txt`.
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

/-- Source: `proof_gap/exercise_30/1.txt`. -/
theorem gap1 : ExpandedIdentity := by
  intro x
  nlinarith [sq_abs x]

/-- Source: `proof_gap/exercise_30/2.txt`. -/
theorem gap2 (h1 : ExpandedIdentity) : SimplifiedMiddle := by
  intro x
  ring

/-- Source: `proof_gap/exercise_30/3.txt`. -/
theorem gap3
    (h1 : ExpandedIdentity)
    (h2 : SimplifiedMiddle) :
    Identity := by
  intro x
  rw [h1 x, h2 x]

/-- Source: `proof_gap/exercise_30/4.txt`. -/
theorem gap4 (h3 : Identity) : Identity := by
  exact h3

end ProofGap.Exercise30

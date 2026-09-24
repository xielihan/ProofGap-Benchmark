import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise405_5

noncomputable section

def TendsToNegInfinityFromLeft (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ E > 0, ∃ δ > 0, ∀ x,
    0 < a - x → a - x < δ → f x < -E

def g (x : ℝ) : ℝ := 1 / (x - 1)

/-- Source: `proof_gap/exercise_405_5/1.txt`. -/
theorem gap1 : ∀ a : ℝ, ∀ f : ℝ → ℝ,
    TendsToNegInfinityFromLeft f a ↔
      ∀ E > 0, ∃ δ > 0, ∀ x,
        0 < a - x → a - x < δ → f x < -E := by
  intro a f
  rfl

/-- Source: `proof_gap/exercise_405_5/2.txt`; define the previously free example. -/
theorem gap2 : TendsToNegInfinityFromLeft g 1 := by
  intro E hE
  refine ⟨1 / E, one_div_pos.mpr hE, ?_⟩
  intro x hx0 hx
  have hmul : E * (1 - x) < 1 := by
    have := (lt_div_iff₀ hE).mp hx
    nlinarith
  have hdiv : E < 1 / (1 - x) := (lt_div_iff₀ hx0).2 hmul
  have heq : 1 / (x - 1) = -(1 / (1 - x)) := by
    rw [show x - 1 = -(1 - x) by ring, div_neg]
  rw [g, heq]
  linarith

end

end ProofGap.Exercise405_5

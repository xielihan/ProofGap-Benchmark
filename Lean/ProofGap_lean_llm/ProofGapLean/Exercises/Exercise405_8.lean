import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise405_8

noncomputable section

def TendsToNegInfinityFromRight (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ E > 0, ∃ δ > 0, ∀ x,
    0 < x - a → x - a < δ → f x < -E

def g (x : ℝ) : ℝ := -1 / (x - 1)

/-- Exercise 405_8, gap 1. -/
theorem gap1 : ∀ a : ℝ, ∀ f : ℝ → ℝ,
    TendsToNegInfinityFromRight f a ↔
      ∀ E > 0, ∃ δ > 0, ∀ x,
        0 < x - a → x - a < δ → f x < -E := by
  intro a f
  rfl

/-- Exercise 405_8, gap 2; define the previously free example. -/
theorem gap2 : TendsToNegInfinityFromRight g 1 := by
  intro E hE
  refine ⟨1 / E, one_div_pos.mpr hE, ?_⟩
  intro x hx0 hx
  have hmul : E * (x - 1) < 1 := by
    have := (lt_div_iff₀ hE).mp hx
    nlinarith
  have hdiv : E < 1 / (x - 1) := (lt_div_iff₀ hx0).2 hmul
  have heq : -1 / (x - 1) = -(1 / (x - 1)) := by ring
  rw [g, heq]
  nlinarith

end

end ProofGap.Exercise405_8

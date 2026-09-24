import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise405_6

noncomputable section

def TendsToPosInfinityFromLeft (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ E > 0, ∃ δ > 0, ∀ x,
    0 < a - x → a - x < δ → E < f x

def g (x : ℝ) : ℝ := 1 / (1 - x)

/-- Exercise 405_6, gap 1. -/
theorem gap1 : ∀ a : ℝ, ∀ f : ℝ → ℝ,
    TendsToPosInfinityFromLeft f a ↔
      ∀ E > 0, ∃ δ > 0, ∀ x,
        0 < a - x → a - x < δ → E < f x := by
  intro a f
  rfl

/-- Exercise 405_6, gap 2; define the previously free example. -/
theorem gap2 : TendsToPosInfinityFromLeft g 1 := by
  intro E hE
  refine ⟨1 / E, one_div_pos.mpr hE, ?_⟩
  intro x hx0 hx
  have hmul : E * (1 - x) < 1 := by
    have := (lt_div_iff₀ hE).mp hx
    nlinarith
  simpa only [g] using (lt_div_iff₀ hx0).2 hmul

end

end ProofGap.Exercise405_6

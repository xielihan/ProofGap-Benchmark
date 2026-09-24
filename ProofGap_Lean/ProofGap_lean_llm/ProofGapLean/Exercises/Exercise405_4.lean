import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise405_4

noncomputable section

def AbsTendsToInfinityFromLeft (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ E > 0, ∃ δ > 0, ∀ x,
    0 < a - x → a - x < δ → E < |f x|

def g (x : ℝ) : ℝ := 1 / (x - 1)

/-- Exercise 405_4, gap 1. -/
theorem gap1 : ∀ a : ℝ, ∀ f : ℝ → ℝ,
    AbsTendsToInfinityFromLeft f a ↔
      ∀ E > 0, ∃ δ > 0, ∀ x,
        0 < a - x → a - x < δ → E < |f x| := by
  intro a f
  rfl

/-- Exercise 405_4, gap 2; define the previously free example. -/
theorem gap2 : AbsTendsToInfinityFromLeft g 1 := by
  intro E hE
  refine ⟨1 / E, one_div_pos.mpr hE, ?_⟩
  intro x hx0 hx
  have habs : |x - 1| = 1 - x := by
    rw [abs_of_nonpos (by linarith)]
    ring
  have hmul : E * |x - 1| < 1 := by
    rw [habs]
    have := (lt_div_iff₀ hE).mp hx
    nlinarith
  rw [g, abs_div, abs_one]
  exact (lt_div_iff₀ (by simpa [habs] using hx0)).2 hmul

end

end ProofGap.Exercise405_4

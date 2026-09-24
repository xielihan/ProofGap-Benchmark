import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise405_7

noncomputable section

def AbsTendsToInfinityFromRight (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ E > 0, ∃ δ > 0, ∀ x,
    0 < x - a → x - a < δ → E < |f x|

def g (x : ℝ) : ℝ := 1 / (x - 1)

/-- Source: `proof_gap/exercise_405_7/1.txt`. -/
theorem gap1 : ∀ a : ℝ, ∀ f : ℝ → ℝ,
    AbsTendsToInfinityFromRight f a ↔
      ∀ E > 0, ∃ δ > 0, ∀ x,
        0 < x - a → x - a < δ → E < |f x| := by
  intro a f
  rfl

/-- Source: `proof_gap/exercise_405_7/2.txt`; define the previously free example. -/
theorem gap2 : AbsTendsToInfinityFromRight g 1 := by
  intro E hE
  refine ⟨1 / E, one_div_pos.mpr hE, ?_⟩
  intro x hx0 hx
  have hmul : E * |x - 1| < 1 := by
    rw [abs_of_pos hx0]
    have := (lt_div_iff₀ hE).mp hx
    nlinarith
  rw [g, abs_div, abs_one]
  exact (lt_div_iff₀ (by simpa [abs_of_pos hx0] using hx0)).2 hmul

end

end ProofGap.Exercise405_7

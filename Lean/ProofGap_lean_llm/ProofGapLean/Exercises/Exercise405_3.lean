import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise405_3

noncomputable section

def TendsToPosInfinityAt (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ E > 0, ∃ δ > 0, ∀ x,
    0 < |x - a| → |x - a| < δ → E < f x

def g (x : ℝ) : ℝ := 1 / (x - 1) ^ 2

/-- Source: `proof_gap/exercise_405_3/1.txt`. -/
theorem gap1 : ∀ a : ℝ, ∀ f : ℝ → ℝ,
    TendsToPosInfinityAt f a ↔
      ∀ E > 0, ∃ δ > 0, ∀ x,
        0 < |x - a| → |x - a| < δ → E < f x := by
  intro a f
  rfl

/-- Source: `proof_gap/exercise_405_3/2.txt`; define the previously free example. -/
theorem gap2 : TendsToPosInfinityAt g 1 := by
  intro E hE
  refine ⟨1 / (E + 1), one_div_pos.mpr (by linarith), ?_⟩
  intro x hx0 hx
  have ha0 : 0 ≤ |x - 1| := abs_nonneg _
  have hmul : |x - 1| * (E + 1) < 1 :=
    (lt_div_iff₀ (by linarith : 0 < E + 1)).mp hx
  have hlt1 : |x - 1| < 1 := by nlinarith
  have hEabs : E * |x - 1| < 1 := by nlinarith
  have hsquare : E * (x - 1) ^ 2 < 1 := by
    nlinarith [sq_abs (x - 1)]
  have hsq0 : 0 < (x - 1) ^ 2 := sq_pos_of_ne_zero (abs_pos.mp hx0)
  simpa only [g] using (lt_div_iff₀ hsq0).2 hsquare

end

end ProofGap.Exercise405_3

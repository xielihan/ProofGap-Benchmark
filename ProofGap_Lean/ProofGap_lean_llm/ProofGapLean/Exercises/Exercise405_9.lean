import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise405_9

noncomputable section

def TendsToPosInfinityFromRight (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ E > 0, ∃ δ > 0, ∀ x,
    0 < x - a → x - a < δ → E < f x

def f (x : ℝ) : ℝ := 1 / (x - 1)

/-- Exercise 405_9, gap 1; bind `a` and the chosen `δ` instead of re-quantifying them inside. -/
theorem gap1 : ∀ E > 0, ∃ δ > 0, ∀ x,
    0 < x - 1 → x - 1 < δ → E < f x := by
  intro E hE
  refine ⟨1 / E, one_div_pos.mpr hE, ?_⟩
  intro x hx0 hx
  have hmul : E * (x - 1) < 1 := by
    have := (lt_div_iff₀ hE).mp hx
    nlinarith
  simpa only [f] using (lt_div_iff₀ hx0).2 hmul

/-- Exercise 405_9, gap 2; replace the false universal claim by the defining equivalence. -/
theorem gap2 : TendsToPosInfinityFromRight f 1 ↔
    ∀ E > 0, ∃ δ > 0, ∀ x,
      0 < x - 1 → x - 1 < δ → E < f x := by
  rfl

/-- Exercise 405_9, gap 3; define the previously free function. -/
theorem gap3 : TendsToPosInfinityFromRight f 1 := by
  exact gap1

end

end ProofGap.Exercise405_9

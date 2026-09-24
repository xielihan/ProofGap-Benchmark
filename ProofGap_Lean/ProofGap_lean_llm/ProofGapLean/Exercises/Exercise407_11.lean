import ProofGapLean.Prelude.Core
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise407_11

noncomputable section

def ApproachesAboveAtNegInfinity (f : ℝ → ℝ) (b : ℝ) : Prop :=
  ∀ ε > 0, ∃ N > 0, ∀ x, x < -N →
    0 < f x - b ∧ f x - b < ε

def f (x : ℝ) : ℝ := -1 / x

/-- Exercise 407_11, gap 1; bind `y=f(x)` and remove the shadowed threshold. -/
theorem gap1 : ∀ ε > 0, ∃ N > 0, ∀ x, x < -N →
    0 < f x ∧ f x < ε := by
  intro ε hε
  refine ⟨1 / ε, one_div_pos.mpr hε, ?_⟩
  intro x hx
  have hNpos : 0 < (1 / ε : ℝ) := one_div_pos.mpr hε
  have hx0 : x < 0 := lt_trans hx (neg_neg_of_pos hNpos)
  constructor
  · exact div_pos_of_neg_of_neg neg_one_lt_zero hx0
  · apply (div_lt_iff_of_neg hx0).2
    have hmul : ε * x < ε * (-(1 / ε)) :=
      mul_lt_mul_of_pos_left hx hε
    have hsimp : ε * (-(1 / ε)) = -1 := by
      field_simp [ne_of_gt hε]
    rw [hsimp] at hmul
    exact hmul

/-- Exercise 407_11, gap 2; replace the false universal limit claim by its defining equivalence. -/
theorem gap2 (g : ℝ → ℝ) (b : ℝ) :
    ApproachesAboveAtNegInfinity g b ↔
      ∀ ε > 0, ∃ N > 0, ∀ x, x < -N →
        0 < g x - b ∧ g x - b < ε := by
  rfl

/-- Exercise 407_11, gap 3; restrict the sign to the negative half-line. -/
theorem gap3 : ∀ x : ℝ, x < 0 → 0 < f x := by
  intro x hx
  unfold f
  exact div_pos_of_neg_of_neg neg_one_lt_zero hx

/-- Exercise 407_11, gap 4; define the previously free function. -/
theorem gap4 : ApproachesAboveAtNegInfinity f 0 := by
  simpa [ApproachesAboveAtNegInfinity] using gap1

/-- Exercise 407_11, gap 5; restrict the sign to the negative half-line. -/
theorem gap5 : ∀ x : ℝ, x < 0 → 0 < f x := by
  exact gap3

end

end ProofGap.Exercise407_11

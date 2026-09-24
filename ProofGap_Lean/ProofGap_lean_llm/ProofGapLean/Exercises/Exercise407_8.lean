import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise407_8

noncomputable section

def ApproachesBelowAtNegInfinity (f : ℝ → ℝ) (b : ℝ) : Prop :=
  ∀ ε > 0, ∃ N > 0, ∀ x, x < -N →
    0 < b - f x ∧ b - f x < ε

def f (x : ℝ) : ℝ := 1 / x

/-- Exercise 407_8, gap 1; bind `y=f(x)` and remove the shadowed threshold. -/
theorem gap1 : ∀ ε > 0, ∃ N > 0, ∀ x, x < -N →
    0 < -f x ∧ -f x < ε := by
  intro ε hε
  let N : ℝ := 1 / ε
  have hN : 0 < N := by
    dsimp [N]
    exact one_div_pos.mpr hε
  refine ⟨N, hN, ?_⟩
  intro x hx
  have hx0 : x < 0 := by
    linarith
  have hfx : f x < 0 := by
    dsimp [f]
    exact one_div_neg.mpr hx0
  constructor
  · exact neg_pos.mpr hfx
  · have hε0 : ε ≠ 0 := ne_of_gt hε
    have hmul : ε * x < -1 := by
      calc
        ε * x < ε * (-N) := mul_lt_mul_of_pos_left hx hε
        _ = -1 := by
          dsimp [N]
          field_simp [hε0]
    have hquot : (-1 : ℝ) / x < ε := by
      exact (div_lt_iff_of_neg hx0).2 hmul
    simpa only [f, neg_div] using hquot

/-- Exercise 407_8, gap 2; replace the false universal limit claim by its defining equivalence. -/
theorem gap2 (g : ℝ → ℝ) (b : ℝ) :
    ApproachesBelowAtNegInfinity g b ↔
      ∀ ε > 0, ∃ N > 0, ∀ x, x < -N →
        0 < b - g x ∧ b - g x < ε := by
  rfl

/-- Exercise 407_8, gap 3; restrict the sign to the negative half-line. -/
theorem gap3 : ∀ x : ℝ, x < 0 → f x < 0 := by
  intro x hx
  dsimp [f]
  exact one_div_neg.mpr hx

/-- Exercise 407_8, gap 4; define the previously free function. -/
theorem gap4 : ApproachesBelowAtNegInfinity f 0 := by
  simpa [ApproachesBelowAtNegInfinity] using gap1

/-- Exercise 407_8, gap 5; restrict the sign to the negative half-line. -/
theorem gap5 : ∀ x : ℝ, x < 0 → f x < 0 := by
  exact gap3

end

end ProofGap.Exercise407_8

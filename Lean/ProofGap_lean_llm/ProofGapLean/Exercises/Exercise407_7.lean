import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise407_7

noncomputable section

def ApproachesBelowAtInfinity (f : ℝ → ℝ) (b : ℝ) : Prop :=
  ∀ ε > 0, ∃ N > 0, ∀ x, N < |x| →
    0 < b - f x ∧ b - f x < ε

def f (x : ℝ) : ℝ := -1 / (1 + x ^ 2)

/-- Source: `proof_gap/exercise_407_7/1.txt`; bind `y=f(x)` and remove the shadowed threshold. -/
theorem gap1 : ∀ ε > 0, ∃ N > 0, ∀ x, N < |x| →
    0 < -f x ∧ -f x < ε := by
  intro ε hε
  let N : ℝ := 1 + 1 / ε
  have hε0 : ε ≠ 0 := ne_of_gt hε
  have hinv : 0 < 1 / ε := one_div_pos.mpr hε
  have hN : 0 < N := by
    dsimp [N]
    linarith
  refine ⟨N, hN, ?_⟩
  intro x hx
  have hεN : ε * N = ε + 1 := by
    dsimp [N]
    field_simp [hε0]
  have hscaled := mul_lt_mul_of_pos_left hx hε
  have hεabs : 1 < ε * |x| := by
    rw [hεN] at hscaled
    linarith
  have hxone : 1 < |x| := by
    dsimp [N] at hx
    linarith
  have hprod : 0 < (ε * |x| - 1) * (|x| - 1) :=
    mul_pos (sub_pos.mpr hεabs) (sub_pos.mpr hxone)
  have hquad : 1 < ε * (|x| ^ 2) := by
    nlinarith [hprod]
  have habs_sq : |x| ^ 2 = x ^ 2 := sq_abs x
  rw [habs_sq] at hquad
  have hden : 0 < 1 + x ^ 2 := by
    nlinarith [sq_nonneg x]
  have hpos : 0 < 1 / (1 + x ^ 2) := one_div_pos.mpr hden
  have hsmall : 1 / (1 + x ^ 2) < ε := by
    apply (div_lt_iff₀ hden).2
    nlinarith
  constructor
  · simpa only [f, neg_div, neg_neg] using hpos
  · simpa only [f, neg_div, neg_neg] using hsmall

/-- Source: `proof_gap/exercise_407_7/2.txt`; replace the false universal limit claim by its defining equivalence. -/
theorem gap2 (g : ℝ → ℝ) (b : ℝ) :
    ApproachesBelowAtInfinity g b ↔
      ∀ ε > 0, ∃ N > 0, ∀ x, N < |x| →
        0 < b - g x ∧ b - g x < ε := by
  rfl

/-- Source: `proof_gap/exercise_407_7/3.txt`; state the sign for the defined example. -/
theorem gap3 : ∀ x : ℝ, f x < 0 := by
  intro x
  have hden : 0 < 1 + x ^ 2 := by
    nlinarith [sq_nonneg x]
  have hpos : 0 < 1 / (1 + x ^ 2) := one_div_pos.mpr hden
  have hneg : -(1 / (1 + x ^ 2)) < 0 := neg_lt_zero.mpr hpos
  simpa only [f, neg_div] using hneg

/-- Source: `proof_gap/exercise_407_7/4.txt`; define the previously free function. -/
theorem gap4 : ApproachesBelowAtInfinity f 0 := by
  unfold ApproachesBelowAtInfinity
  simpa only [zero_sub] using gap1

/-- Source: `proof_gap/exercise_407_7/5.txt`. -/
theorem gap5 : ∀ x : ℝ, f x < 0 := by
  exact gap3

end

end ProofGap.Exercise407_7

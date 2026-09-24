import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise407_10

noncomputable section

def ApproachesAboveAtInfinity (f : ℝ → ℝ) (b : ℝ) : Prop :=
  ∀ ε > 0, ∃ N > 0, ∀ x, N < |x| →
    0 < f x - b ∧ f x - b < ε

def f (x : ℝ) : ℝ := 1 / (1 + x ^ 2)

/-- Source: `proof_gap/exercise_407_10/1.txt`; bind `y=f(x)` and remove the shadowed threshold. -/
theorem gap1 : ∀ ε > 0, ∃ N > 0, ∀ x, N < |x| →
    0 < f x ∧ f x < ε := by
  intro ε hε
  let N : ℝ := max 1 (1 / ε)
  have hN1 : (1 : ℝ) ≤ N := by
    simp [N]
  have hNe : 1 / ε ≤ N := by
    simp [N]
  refine ⟨N, lt_of_lt_of_le zero_lt_one hN1, ?_⟩
  intro x hx
  have hx1 : (1 : ℝ) < |x| := lt_of_le_of_lt hN1 hx
  have hxe : 1 / ε < |x| := lt_of_le_of_lt hNe hx
  have habs_sq : |x| ^ 2 = x ^ 2 := sq_abs x
  have haxsq : |x| < x ^ 2 := by
    rw [← habs_sq]
    have ha0 : 0 < |x| := lt_trans zero_lt_one hx1
    have hp : 0 < |x| * (|x| - 1) :=
      mul_pos ha0 (sub_pos.mpr hx1)
    nlinarith
  have hmul : 1 < ε * |x| := by
    have h := (div_lt_iff₀ hε).mp hxe
    simpa [mul_comm] using h
  have hmul2 : ε * |x| < ε * (x ^ 2) :=
    mul_lt_mul_of_pos_left haxsq hε
  have hquad : 1 < ε * (x ^ 2) := lt_trans hmul hmul2
  have hstep : ε * (x ^ 2) < ε * (1 + x ^ 2) := by
    apply mul_lt_mul_of_pos_left _ hε
    linarith
  have hone : 1 < ε * (1 + x ^ 2) := lt_trans hquad hstep
  have hden : 0 < 1 + x ^ 2 := by
    nlinarith [sq_nonneg x]
  constructor
  · unfold f
    exact one_div_pos.mpr hden
  · unfold f
    exact (div_lt_iff₀ hden).2 hone

/-- Source: `proof_gap/exercise_407_10/2.txt`; replace the false universal limit claim by its defining equivalence. -/
theorem gap2 (g : ℝ → ℝ) (b : ℝ) :
    ApproachesAboveAtInfinity g b ↔
      ∀ ε > 0, ∃ N > 0, ∀ x, N < |x| →
        0 < g x - b ∧ g x - b < ε := by
  rfl

/-- Source: `proof_gap/exercise_407_10/3.txt`; state the sign for the defined example. -/
theorem gap3 : ∀ x : ℝ, 0 < f x := by
  intro x
  unfold f
  apply one_div_pos.mpr
  nlinarith [sq_nonneg x]

/-- Source: `proof_gap/exercise_407_10/4.txt`; define the previously free function. -/
theorem gap4 : ApproachesAboveAtInfinity f 0 := by
  intro ε hε
  obtain ⟨N, hN, hbound⟩ := gap1 ε hε
  refine ⟨N, hN, ?_⟩
  intro x hx
  simpa using hbound x hx

/-- Source: `proof_gap/exercise_407_10/5.txt`. -/
theorem gap5 : ∀ x : ℝ, 0 < f x := by
  exact gap3

end

end ProofGap.Exercise407_10

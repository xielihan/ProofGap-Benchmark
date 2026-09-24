import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise669_1

def EpsilonCondition (f : ℝ → ℝ) (x₀ : ℝ) (E : Set ℝ) : Prop :=
  ∀ ε ∈ E, 0 < ε → ∃ δ > 0, ∀ x,
    |x - x₀| < δ → |f x - f x₀| < ε

/-- Exercise 669_1, gap 1; correct the reversed implication: finitely many epsilon tests do not imply continuity. -/
theorem gap1 :
    ∃ (f : ℝ → ℝ) (x₀ : ℝ) (E : Set ℝ),
      E.Finite ∧ EpsilonCondition f x₀ E ∧ ¬ ContinuousAt f x₀ := by
  refine ⟨(fun x : ℝ => if x = 0 then 0 else 1), 0, {2}, by simp, ?_, ?_⟩
  · intro ε hε _
    have he : ε = 2 := by simpa using hε
    subst ε
    refine ⟨1, by norm_num, ?_⟩
    intro x _
    by_cases hx : x = 0
    · simp [hx]
    · norm_num [hx]
  · intro hcont
    rw [Metric.continuousAt_iff] at hcont
    obtain ⟨δ, hδ, hclose⟩ := hcont (1 / 2) (by norm_num)
    have hxpos : 0 < δ / 2 := by linarith
    have hx0 : δ / 2 ≠ 0 := ne_of_gt hxpos
    have hxd : dist (δ / 2) 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hxpos]
      linarith
    have hout := hclose hxd
    rw [if_neg hx0, if_pos rfl] at hout
    norm_num [Real.dist_eq] at hout

/-- Exercise 669_1, gap 2; bind the finite test set in the counterexample. -/
theorem gap2 :
    ∃ E : Set ℝ, E.Finite ∧ E.Nonempty := by
  refine ⟨{0}, ?_, ?_⟩ <;> simp

/-- Exercise 669_1, gap 3; state the noncontinuous counterexample with its finite epsilon tests. -/
theorem gap3 :
    ∃ (f : ℝ → ℝ) (x₀ : ℝ) (E : Set ℝ),
      E.Finite ∧ EpsilonCondition f x₀ E ∧ ¬ ContinuousAt f x₀ := by
  exact gap1

/-- Exercise 669_1, gap 4; corrected final counterexample theorem. -/
theorem gap4 :
    ¬ (∀ (f : ℝ → ℝ) (x₀ : ℝ) (E : Set ℝ),
      E.Finite → EpsilonCondition f x₀ E → ContinuousAt f x₀) := by
  intro h
  obtain ⟨f, x₀, E, hE, hε, hncont⟩ := gap1
  exact hncont (h f x₀ E hE hε)

end ProofGap.Exercise669_1

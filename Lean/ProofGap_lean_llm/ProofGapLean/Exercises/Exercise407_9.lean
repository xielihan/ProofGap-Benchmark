import ProofGapLean.Prelude.Core

namespace ProofGap.Exercise407_9

noncomputable section

def ApproachesBelowAtPosInfinity (f : ℝ → ℝ) (b : ℝ) : Prop :=
  ∀ ε > 0, ∃ N > 0, ∀ x, N < x →
    0 < b - f x ∧ b - f x < ε

def f (x : ℝ) : ℝ := -1 / x

/-- Source: `proof_gap/exercise_407_9/1.txt`; bind `y=f(x)` and remove the shadowed threshold. -/
theorem gap1 : ∀ ε > 0, ∃ N > 0, ∀ x, N < x →
    0 < -f x ∧ -f x < ε := by
  intro ε hε
  refine ⟨1 / ε, one_div_pos.mpr hε, ?_⟩
  intro x hx
  have hx0 : 0 < x := lt_trans (one_div_pos.mpr hε) hx
  have hmul : 1 < x * ε := (div_lt_iff₀ hε).mp hx
  have hdiv : 1 / x < ε := (div_lt_iff₀ hx0).2 (by
    simpa [mul_comm] using hmul)
  constructor
  · simpa only [f, neg_div, neg_neg] using (one_div_pos.mpr hx0)
  · simpa only [f, neg_div, neg_neg] using hdiv

/-- Source: `proof_gap/exercise_407_9/2.txt`; replace the false universal limit claim by its defining equivalence. -/
theorem gap2 (g : ℝ → ℝ) (b : ℝ) :
    ApproachesBelowAtPosInfinity g b ↔
      ∀ ε > 0, ∃ N > 0, ∀ x, N < x →
        0 < b - g x ∧ b - g x < ε := by
  rfl

/-- Source: `proof_gap/exercise_407_9/3.txt`; restrict the sign to the positive half-line. -/
theorem gap3 : ∀ x : ℝ, 0 < x → f x < 0 := by
  intro x hx
  simp only [f, neg_div]
  exact neg_lt_zero.mpr (one_div_pos.mpr hx)

/-- Source: `proof_gap/exercise_407_9/4.txt`; define the previously free function. -/
theorem gap4 : ApproachesBelowAtPosInfinity f 0 := by
  unfold ApproachesBelowAtPosInfinity
  simpa only [zero_sub] using gap1

/-- Source: `proof_gap/exercise_407_9/5.txt`; restrict the sign to the positive half-line. -/
theorem gap5 : ∀ x : ℝ, 0 < x → f x < 0 := by
  exact gap3

end

end ProofGap.Exercise407_9

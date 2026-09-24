import ProofGapLean.Prelude.Core

namespace ProofGap.Exercise407_12

noncomputable section

def ApproachesAboveAtPosInfinity (f : ℝ → ℝ) (b : ℝ) : Prop :=
  ∀ ε > 0, ∃ N > 0, ∀ x, N < x →
    0 < f x - b ∧ f x - b < ε

def f (x : ℝ) : ℝ := 1 / x

/-- Source: `proof_gap/exercise_407_12/1.txt`; bind `y=f(x)` and remove the shadowed threshold. -/
theorem gap1 : ∀ ε > 0, ∃ N > 0, ∀ x, N < x →
    0 < f x ∧ f x < ε := by
  intro ε hε
  refine ⟨1 / ε, one_div_pos.mpr hε, ?_⟩
  intro x hx
  have hxpos : 0 < x := lt_trans (one_div_pos.mpr hε) hx
  constructor
  · simpa [f] using (one_div_pos.mpr hxpos)
  · change 1 / x < ε
    apply (div_lt_iff₀ hxpos).2
    have h := (div_lt_iff₀ hε).1 hx
    simpa [mul_comm] using h

/-- Source: `proof_gap/exercise_407_12/2.txt`; replace the false universal limit claim by its defining equivalence. -/
theorem gap2 (g : ℝ → ℝ) (b : ℝ) :
    ApproachesAboveAtPosInfinity g b ↔
      ∀ ε > 0, ∃ N > 0, ∀ x, N < x →
        0 < g x - b ∧ g x - b < ε := by
  rfl

/-- Source: `proof_gap/exercise_407_12/3.txt`; restrict the sign to the positive half-line. -/
theorem gap3 : ∀ x : ℝ, 0 < x → 0 < f x := by
  intro x hx
  simpa [f] using (one_div_pos.mpr hx)

/-- Source: `proof_gap/exercise_407_12/4.txt`; define the previously free function. -/
theorem gap4 : ApproachesAboveAtPosInfinity f 0 := by
  unfold ApproachesAboveAtPosInfinity
  simpa only [sub_zero] using gap1

/-- Source: `proof_gap/exercise_407_12/5.txt`; restrict the sign to the positive half-line. -/
theorem gap5 : ∀ x : ℝ, 0 < x → 0 < f x := by
  exact gap3

end

end ProofGap.Exercise407_12

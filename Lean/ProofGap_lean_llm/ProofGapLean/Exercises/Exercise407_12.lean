import ProofGapLean.Prelude.Core

namespace ProofGap.Exercise407_12

noncomputable section

def ApproachesAboveAtPosInfinity (f : ℝ → ℝ) (b : ℝ) : Prop :=
  ∀ ε > 0, ∃ N > 0, ∀ x, N < x →
    0 < f x - b ∧ f x - b < ε

def f (x : ℝ) : ℝ := 1 / x

/-- Exercise 407_12, gap 1; bind `y=f(x)` and remove the shadowed threshold. -/
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

/-- Exercise 407_12, gap 2; replace the false universal limit claim by its defining equivalence. -/
theorem gap2 (g : ℝ → ℝ) (b : ℝ) :
    ApproachesAboveAtPosInfinity g b ↔
      ∀ ε > 0, ∃ N > 0, ∀ x, N < x →
        0 < g x - b ∧ g x - b < ε := by
  rfl

/-- Exercise 407_12, gap 3; restrict the sign to the positive half-line. -/
theorem gap3 : ∀ x : ℝ, 0 < x → 0 < f x := by
  intro x hx
  simpa [f] using (one_div_pos.mpr hx)

/-- Exercise 407_12, gap 4; define the previously free function. -/
theorem gap4 : ApproachesAboveAtPosInfinity f 0 := by
  unfold ApproachesAboveAtPosInfinity
  simpa only [sub_zero] using gap1

/-- Exercise 407_12, gap 5; restrict the sign to the positive half-line. -/
theorem gap5 : ∀ x : ℝ, 0 < x → 0 < f x := by
  exact gap3

end

end ProofGap.Exercise407_12

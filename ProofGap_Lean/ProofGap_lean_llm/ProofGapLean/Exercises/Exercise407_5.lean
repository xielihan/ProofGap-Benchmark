import ProofGapLean.Prelude.Core

namespace ProofGap.Exercise407_5

noncomputable section

def ApproachesAboveFromLeft (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x,
    0 < a - x → a - x < δ →
      0 < f x - b ∧ f x - b < ε

def f (x : ℝ) : ℝ := -x

/-- Exercise 407_5, gap 1; bind `y=f(x)` and the fixed limit point. -/
theorem gap1 : ∀ ε > 0, ∃ δ > 0, ∀ x,
    0 < -x → -x < δ → 0 < f x ∧ f x < ε := by
  intro ε hε
  refine ⟨ε, hε, ?_⟩
  intro x hx hδε
  simpa [f] using And.intro hx hδε

/-- Exercise 407_5, gap 2; replace the false universal limit claim by its defining equivalence. -/
theorem gap2 (g : ℝ → ℝ) (a b : ℝ) :
    ApproachesAboveFromLeft g a b ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x,
        0 < a - x → a - x < δ →
          0 < g x - b ∧ g x - b < ε := by
  rfl

/-- Exercise 407_5, gap 3; restrict the inequality to the left side. -/
theorem gap3 : ∀ x : ℝ, x < 0 → 0 < f x := by
  intro x hx
  simpa [f] using (neg_pos.mpr hx)

/-- Exercise 407_5, gap 4; define the previously free function. -/
theorem gap4 : ApproachesAboveFromLeft f 0 0 := by
  simpa [ApproachesAboveFromLeft] using gap1

/-- Exercise 407_5, gap 5; restrict the inequality to the left side. -/
theorem gap5 : ∀ x : ℝ, x < 0 → 0 < f x := by
  exact gap3

end

end ProofGap.Exercise407_5

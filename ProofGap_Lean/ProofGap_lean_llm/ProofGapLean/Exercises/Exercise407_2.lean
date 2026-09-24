import ProofGapLean.Prelude.Core

namespace ProofGap.Exercise407_2

noncomputable section

def ApproachesBelowFromLeft (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x,
    0 < a - x → a - x < δ →
      0 < b - f x ∧ b - f x < ε

def f (x : ℝ) : ℝ := x

/-- Exercise 407_2, gap 1; bind `y=f(x)` and the fixed limit point. -/
theorem gap1 : ∀ ε > 0, ∃ δ > 0, ∀ x,
    0 < -x → -x < δ → 0 < -f x ∧ -f x < ε := by
  intro ε hε
  refine ⟨ε, hε, ?_⟩
  intro x hx hδ
  constructor
  · simpa [f] using hx
  · simpa [f] using hδ

/-- Exercise 407_2, gap 2; replace the false universal limit claim by its defining equivalence. -/
theorem gap2 (g : ℝ → ℝ) (a b : ℝ) :
    ApproachesBelowFromLeft g a b ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x,
        0 < a - x → a - x < δ →
          0 < b - g x ∧ b - g x < ε := by
  rfl

/-- Exercise 407_2, gap 3; restrict the inequality to the left side. -/
theorem gap3 : ∀ x : ℝ, x < 0 → f x < 0 := by
  intro x hx
  simpa [f] using hx

/-- Exercise 407_2, gap 4; define the previously free function. -/
theorem gap4 : ApproachesBelowFromLeft f 0 0 := by
  simpa [ApproachesBelowFromLeft] using gap1

/-- Exercise 407_2, gap 5; restrict the inequality to the left side. -/
theorem gap5 : ∀ x : ℝ, x < 0 → f x < 0 := by
  exact gap3

end

end ProofGap.Exercise407_2

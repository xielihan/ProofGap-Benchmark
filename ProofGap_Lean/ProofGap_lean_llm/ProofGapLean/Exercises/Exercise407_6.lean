import ProofGapLean.Prelude.Core

namespace ProofGap.Exercise407_6

noncomputable section

def ApproachesAboveFromRight (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x,
    0 < x - a → x - a < δ →
      0 < f x - b ∧ f x - b < ε

def f (x : ℝ) : ℝ := x

/-- Exercise 407_6, gap 1; bind `y=f(x)` and the fixed limit point. -/
theorem gap1 : ∀ ε > 0, ∃ δ > 0, ∀ x,
    0 < x → x < δ → 0 < f x ∧ f x < ε := by
  intro ε hε
  refine ⟨ε, hε, ?_⟩
  intro x hx hxe
  simpa [f] using And.intro hx hxe

/-- Exercise 407_6, gap 2; replace the false universal limit claim by its defining equivalence. -/
theorem gap2 (g : ℝ → ℝ) (a b : ℝ) :
    ApproachesAboveFromRight g a b ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x,
        0 < x - a → x - a < δ →
          0 < g x - b ∧ g x - b < ε := by
  rfl

/-- Exercise 407_6, gap 3; restrict the inequality to the right side. -/
theorem gap3 : ∀ x : ℝ, 0 < x → 0 < f x := by
  intro x hx
  simpa [f] using hx

/-- Exercise 407_6, gap 4; define the previously free function. -/
theorem gap4 : ApproachesAboveFromRight f 0 0 := by
  simpa [ApproachesAboveFromRight, sub_zero] using gap1

/-- Exercise 407_6, gap 5; restrict the inequality to the right side. -/
theorem gap5 : ∀ x : ℝ, 0 < x → 0 < f x := by
  exact gap3

end

end ProofGap.Exercise407_6

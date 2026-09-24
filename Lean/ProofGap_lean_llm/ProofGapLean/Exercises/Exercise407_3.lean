import ProofGapLean.Prelude.Core

namespace ProofGap.Exercise407_3

noncomputable section

def ApproachesBelowFromRight (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x,
    0 < x - a → x - a < δ →
      0 < b - f x ∧ b - f x < ε

def f (x : ℝ) : ℝ := -x

/-- Source: `proof_gap/exercise_407_3/1.txt`; bind `y=f(x)` and the fixed limit point. -/
theorem gap1 : ∀ ε > 0, ∃ δ > 0, ∀ x,
    0 < x → x < δ → 0 < -f x ∧ -f x < ε := by
  intro ε hε
  refine ⟨ε, hε, ?_⟩
  intro x hx hδε
  constructor
  · simpa [f] using hx
  · simpa [f] using hδε

/-- Source: `proof_gap/exercise_407_3/2.txt`; replace the false universal limit claim by its defining equivalence. -/
theorem gap2 (g : ℝ → ℝ) (a b : ℝ) :
    ApproachesBelowFromRight g a b ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x,
        0 < x - a → x - a < δ →
          0 < b - g x ∧ b - g x < ε := by
  rfl

/-- Source: `proof_gap/exercise_407_3/3.txt`; restrict the inequality to the right side. -/
theorem gap3 : ∀ x : ℝ, 0 < x → f x < 0 := by
  intro x hx
  simpa [f] using hx

/-- Source: `proof_gap/exercise_407_3/4.txt`; define the previously free function. -/
theorem gap4 : ApproachesBelowFromRight f 0 0 := by
  simpa [ApproachesBelowFromRight] using gap1

/-- Source: `proof_gap/exercise_407_3/5.txt`; restrict the inequality to the right side. -/
theorem gap5 : ∀ x : ℝ, 0 < x → f x < 0 := by
  exact gap3

end

end ProofGap.Exercise407_3

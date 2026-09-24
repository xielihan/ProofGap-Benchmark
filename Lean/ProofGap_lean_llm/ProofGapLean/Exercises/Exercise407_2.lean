import ProofGapLean.Prelude.Core

namespace ProofGap.Exercise407_2

noncomputable section

def ApproachesBelowFromLeft (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x,
    0 < a - x → a - x < δ →
      0 < b - f x ∧ b - f x < ε

def f (x : ℝ) : ℝ := x

/-- Source: `proof_gap/exercise_407_2/1.txt`; bind `y=f(x)` and the fixed limit point. -/
theorem gap1 : ∀ ε > 0, ∃ δ > 0, ∀ x,
    0 < -x → -x < δ → 0 < -f x ∧ -f x < ε := by
  intro ε hε
  refine ⟨ε, hε, ?_⟩
  intro x hx hδ
  constructor
  · simpa [f] using hx
  · simpa [f] using hδ

/-- Source: `proof_gap/exercise_407_2/2.txt`; replace the false universal limit claim by its defining equivalence. -/
theorem gap2 (g : ℝ → ℝ) (a b : ℝ) :
    ApproachesBelowFromLeft g a b ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x,
        0 < a - x → a - x < δ →
          0 < b - g x ∧ b - g x < ε := by
  rfl

/-- Source: `proof_gap/exercise_407_2/3.txt`; restrict the inequality to the left side. -/
theorem gap3 : ∀ x : ℝ, x < 0 → f x < 0 := by
  intro x hx
  simpa [f] using hx

/-- Source: `proof_gap/exercise_407_2/4.txt`; define the previously free function. -/
theorem gap4 : ApproachesBelowFromLeft f 0 0 := by
  simpa [ApproachesBelowFromLeft] using gap1

/-- Source: `proof_gap/exercise_407_2/5.txt`; restrict the inequality to the left side. -/
theorem gap5 : ∀ x : ℝ, x < 0 → f x < 0 := by
  exact gap3

end

end ProofGap.Exercise407_2

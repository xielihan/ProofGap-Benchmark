import ProofGapLean.Prelude.Core

namespace ProofGap.Exercise407_6

noncomputable section

def ApproachesAboveFromRight (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x,
    0 < x - a → x - a < δ →
      0 < f x - b ∧ f x - b < ε

def f (x : ℝ) : ℝ := x

/-- Source: `proof_gap/exercise_407_6/1.txt`; bind `y=f(x)` and the fixed limit point. -/
theorem gap1 : ∀ ε > 0, ∃ δ > 0, ∀ x,
    0 < x → x < δ → 0 < f x ∧ f x < ε := by
  intro ε hε
  refine ⟨ε, hε, ?_⟩
  intro x hx hxe
  simpa [f] using And.intro hx hxe

/-- Source: `proof_gap/exercise_407_6/2.txt`; replace the false universal limit claim by its defining equivalence. -/
theorem gap2 (g : ℝ → ℝ) (a b : ℝ) :
    ApproachesAboveFromRight g a b ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x,
        0 < x - a → x - a < δ →
          0 < g x - b ∧ g x - b < ε := by
  rfl

/-- Source: `proof_gap/exercise_407_6/3.txt`; restrict the inequality to the right side. -/
theorem gap3 : ∀ x : ℝ, 0 < x → 0 < f x := by
  intro x hx
  simpa [f] using hx

/-- Source: `proof_gap/exercise_407_6/4.txt`; define the previously free function. -/
theorem gap4 : ApproachesAboveFromRight f 0 0 := by
  simpa [ApproachesAboveFromRight, sub_zero] using gap1

/-- Source: `proof_gap/exercise_407_6/5.txt`; restrict the inequality to the right side. -/
theorem gap5 : ∀ x : ℝ, 0 < x → 0 < f x := by
  exact gap3

end

end ProofGap.Exercise407_6

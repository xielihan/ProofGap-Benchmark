import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise231_4

noncomputable section

def domain : Set ℝ := Set.Ioo (-1) 1
def f (x : ℝ) : ℝ := Real.log ((1 - x) / (1 + x))
def OddOn (g : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x, x ∈ s → g (-x) = -g x

/-- Source: `proof_gap/exercise_231_4/1.txt`; restore the logarithm's real domain. -/
theorem gap1 : ∀ x ∈ domain,
    f (-x) = Real.log ((1 + x) / (1 - x)) := by
  intro x hx
  simpa [f, sub_eq_add_neg]

/-- Source: `proof_gap/exercise_231_4/2.txt`; restore the logarithm's real domain. -/
theorem gap2 : ∀ x ∈ domain,
    Real.log ((1 + x) / (1 - x)) =
      -Real.log ((1 - x) / (1 + x)) := by
  intro x hx
  change -1 < x ∧ x < 1 at hx
  have hminus : 1 - x ≠ 0 := by
    linarith [hx.2]
  have hplus : 1 + x ≠ 0 := by
    linarith [hx.1]
  rw [Real.log_div hplus hminus, Real.log_div hminus hplus]
  ring

/-- Source: `proof_gap/exercise_231_4/3.txt`; restore the logarithm's real domain. -/
theorem gap3 : ∀ x ∈ domain,
    -Real.log ((1 - x) / (1 + x)) = -f x := by
  intro x hx
  rfl

/-- Source: `proof_gap/exercise_231_4/4.txt`; restore the logarithm's real domain. -/
theorem gap4 : ∀ x ∈ domain, f (-x) = -f x := by
  intro x hx
  calc
    f (-x) = Real.log ((1 + x) / (1 - x)) := gap1 x hx
    _ = -Real.log ((1 - x) / (1 + x)) := gap2 x hx
    _ = -f x := gap3 x hx

/-- Source: `proof_gap/exercise_231_4/5.txt`; oddness is on the natural domain `(-1,1)`. -/
theorem gap5 : OddOn f domain := by
  intro x hx
  exact gap4 x hx

end

end ProofGap.Exercise231_4

import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3122

noncomputable section

def lagrangeInterpolant (values : ℤ → ℝ) (x₀ h x : ℝ) : ℝ :=
  ((x - x₀) * (x - x₀ - h)) /
      ((x₀ - h - x₀) * (x₀ - h - (x₀ + h))) * values (-1) +
    ((x - x₀ + h) * (x - x₀ - h)) /
      ((x₀ - (x₀ - h)) * (x₀ - (x₀ + h))) * values 0 +
    ((x - x₀ + h) * (x - x₀)) /
      ((x₀ + h - (x₀ - h)) * (x₀ + h - x₀)) * values 1

def centeredForm (values : ℤ → ℝ) (x₀ h x : ℝ) : ℝ :=
  values 0 +
    (values 1 - values (-1)) / (2 * h) * (x - x₀) +
    (values 1 - 2 * values 0 + values (-1)) / (2 * h ^ 2) *
      (x - x₀) ^ 2

/--
Source: `proof_gap/exercise_3122/1.txt`; the left node carries `y(-1)`,
and `h ≠ 0` makes the three interpolation nodes distinct.
-/
theorem gap1 (values : ℤ → ℝ) (x₀ h : ℝ) (hh : h ≠ 0) :
    ∀ x : ℝ,
      lagrangeInterpolant values x₀ h x =
        ((x - x₀) * (x - x₀ - h)) /
            ((x₀ - h - x₀) * (x₀ - h - (x₀ + h))) * values (-1) +
          ((x - x₀ + h) * (x - x₀ - h)) /
            ((x₀ - (x₀ - h)) * (x₀ - (x₀ + h))) * values 0 +
          ((x - x₀ + h) * (x - x₀)) /
            ((x₀ + h - (x₀ - h)) * (x₀ + h - x₀)) * values 1 := by
  intro x
  rfl

/-- Source: `proof_gap/exercise_3122/2.txt`; simplify the same interpolant. -/
theorem gap2 (values : ℤ → ℝ) (x₀ h : ℝ) (hh : h ≠ 0) :
    ∀ x : ℝ,
      lagrangeInterpolant values x₀ h x =
        centeredForm values x₀ h x := by
  intro x
  unfold lagrangeInterpolant centeredForm
  have hleft :
      (x₀ - h - x₀) * (x₀ - h - (x₀ + h)) = 2 * h ^ 2 := by
    ring
  have hmiddle :
      (x₀ - (x₀ - h)) * (x₀ - (x₀ + h)) = -(h ^ 2) := by
    ring
  have hright :
      (x₀ + h - (x₀ - h)) * (x₀ + h - x₀) = 2 * h ^ 2 := by
    ring
  rw [hleft, hmiddle, hright]
  field_simp [hh] <;> ring

end

end ProofGap.Exercise3122

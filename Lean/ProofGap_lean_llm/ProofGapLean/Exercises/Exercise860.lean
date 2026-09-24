import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise860

noncomputable section

def r₁ (x : ℝ) : ℝ :=
  Real.sqrt x

def r₂ (x : ℝ) : ℝ :=
  Real.sqrt (x + r₁ x)

def y (x : ℝ) : ℝ :=
  Real.sqrt (x + r₂ x)

/-- Source: `proof_gap/exercise_860/1.txt`.
The nested square roots are differentiated on their natural open domain. -/
private theorem nestedRoots_pos (x : ℝ) (hx : 0 < x) :
    0 < r₁ x ∧ 0 < r₂ x ∧ 0 < y x := by
  have hr1_pos : 0 < r₁ x := by
    simpa [r₁] using Real.sqrt_pos.2 hx
  have hr2_pos : 0 < r₂ x := by
    simpa [r₂] using Real.sqrt_pos.2 (add_pos hx hr1_pos)
  have hy_pos : 0 < y x := by
    simpa [y] using Real.sqrt_pos.2 (add_pos hx hr2_pos)
  exact ⟨hr1_pos, hr2_pos, hy_pos⟩

private theorem hasDerivAtSqrtOfPos (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun z : ℝ => Real.sqrt z) (1 / (2 * Real.sqrt x)) x := by
  simpa [one_div] using Real.hasDerivAt_sqrt (ne_of_gt hx)

theorem gap1 (x : ℝ) (hx : 0 < x) :
    HasDerivAt y
      (1 / (2 * y x) *
        (1 + 1 / (2 * r₂ x) * (1 + 1 / (2 * r₁ x)))) x := by
  obtain ⟨hr1_pos, hr2_pos, _⟩ := nestedRoots_pos x hx
  have hr1_deriv :
      HasDerivAt r₁ (1 / (2 * r₁ x)) x := by
    simpa [r₁] using hasDerivAtSqrtOfPos x hx
  have harg2 :
      HasDerivAt (fun z : ℝ => z + r₁ z)
        (1 + 1 / (2 * r₁ x)) x := by
    simpa using (hasDerivAt_id x).add hr1_deriv
  have hr2_deriv :
      HasDerivAt r₂
        (1 / (2 * r₂ x) * (1 + 1 / (2 * r₁ x))) x := by
    have hsqrt := hasDerivAtSqrtOfPos (x + r₁ x) (add_pos hx hr1_pos)
    simpa [r₂] using hsqrt.comp x harg2
  have harg3 :
      HasDerivAt (fun z : ℝ => z + r₂ z)
        (1 + 1 / (2 * r₂ x) * (1 + 1 / (2 * r₁ x))) x := by
    simpa using (hasDerivAt_id x).add hr2_deriv
  have hsqrt := hasDerivAtSqrtOfPos (x + r₂ x) (add_pos hx hr2_pos)
  simpa [y] using hsqrt.comp x harg3

/-- Source: `proof_gap/exercise_860/2.txt`.
The positive-domain hypothesis supplies all omitted nonzero denominators. -/
theorem gap2 (x : ℝ) (hx : 0 < x) :
    1 / (2 * y x) *
          (1 + 1 / (2 * r₂ x) * (1 + 1 / (2 * r₁ x))) =
      (1 + 2 * r₁ x + 4 * r₁ x * r₂ x) /
        (8 * r₁ x * r₂ x * y x) := by
  obtain ⟨hr1_pos, hr2_pos, hy_pos⟩ := nestedRoots_pos x hx
  have hr1_ne : r₁ x ≠ 0 := ne_of_gt hr1_pos
  have hr2_ne : r₂ x ≠ 0 := ne_of_gt hr2_pos
  have hy_ne : y x ≠ 0 := ne_of_gt hy_pos
  field_simp [hr1_ne, hr2_ne, hy_ne]
  ring

/-- Source: `proof_gap/exercise_860/3.txt`.
The nested square roots are differentiated on their natural open domain. -/
theorem gap3 (x : ℝ) (hx : 0 < x) :
    HasDerivAt y
      ((1 + 2 * r₁ x + 4 * r₁ x * r₂ x) /
        (8 * r₁ x * r₂ x * y x)) x := by
  rw [← gap2 x hx]
  exact gap1 x hx

end

end ProofGap.Exercise860

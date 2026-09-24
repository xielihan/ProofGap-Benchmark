import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise204

noncomputable section

def φ (x : ℝ) : ℝ := x ^ 2
def ψ (x : ℝ) : ℝ := Real.rpow 2 x

/-- Exercise 204, gap 1. -/
theorem gap1 : ∀ x, φ (φ x) = (x ^ 2) ^ 2 := by
  intro x
  rfl

/-- Exercise 204, gap 2. -/
theorem gap2 : ∀ x : ℝ, (x ^ 2) ^ 2 = x ^ 4 := by
  intro x
  ring

/-- Exercise 204, gap 3. -/
theorem gap3 : ∀ x, φ (φ x) = x ^ 4 := by
  intro x
  rw [gap1, gap2]

/-- Exercise 204, gap 4. -/
theorem gap4 : ∀ x, φ (ψ x) = (Real.rpow 2 x) ^ 2 := by
  intro x
  rfl

/-- Exercise 204, gap 5. -/
theorem gap5 : ∀ x, (Real.rpow 2 x) ^ 2 = Real.rpow 2 (2 * x) := by
  intro x
  calc
    (Real.rpow 2 x) ^ 2 =
        Real.rpow (Real.rpow 2 x) (2 : ℝ) :=
      (Real.rpow_natCast _ 2).symm
    _ = Real.rpow 2 (x * 2) :=
      (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) x 2).symm
    _ = Real.rpow 2 (2 * x) := by ring_nf

/-- Exercise 204, gap 6. -/
theorem gap6 : ∀ x, φ (ψ x) = Real.rpow 2 (2 * x) := by
  intro x
  rw [gap4, gap5]

/-- Exercise 204, gap 7. -/
theorem gap7 : ∀ x, ψ (ψ x) = Real.rpow 2 (Real.rpow 2 x) := by
  intro x
  rfl

/-- Exercise 204, gap 8. -/
theorem gap8 : ∀ x, ψ (φ x) = Real.rpow 2 (x ^ 2) := by
  intro x
  rfl

end

end ProofGap.Exercise204

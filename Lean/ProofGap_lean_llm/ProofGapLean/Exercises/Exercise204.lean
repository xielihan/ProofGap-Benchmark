import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise204

noncomputable section

def φ (x : ℝ) : ℝ := x ^ 2
def ψ (x : ℝ) : ℝ := Real.rpow 2 x

/-- Source: `proof_gap/exercise_204/1.txt`. -/
theorem gap1 : ∀ x, φ (φ x) = (x ^ 2) ^ 2 := by
  intro x
  rfl

/-- Source: `proof_gap/exercise_204/2.txt`. -/
theorem gap2 : ∀ x : ℝ, (x ^ 2) ^ 2 = x ^ 4 := by
  intro x
  ring

/-- Source: `proof_gap/exercise_204/3.txt`. -/
theorem gap3 : ∀ x, φ (φ x) = x ^ 4 := by
  intro x
  rw [gap1, gap2]

/-- Source: `proof_gap/exercise_204/4.txt`. -/
theorem gap4 : ∀ x, φ (ψ x) = (Real.rpow 2 x) ^ 2 := by
  intro x
  rfl

/-- Source: `proof_gap/exercise_204/5.txt`. -/
theorem gap5 : ∀ x, (Real.rpow 2 x) ^ 2 = Real.rpow 2 (2 * x) := by
  intro x
  calc
    (Real.rpow 2 x) ^ 2 =
        Real.rpow (Real.rpow 2 x) (2 : ℝ) :=
      (Real.rpow_natCast _ 2).symm
    _ = Real.rpow 2 (x * 2) :=
      (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) x 2).symm
    _ = Real.rpow 2 (2 * x) := by ring_nf

/-- Source: `proof_gap/exercise_204/6.txt`. -/
theorem gap6 : ∀ x, φ (ψ x) = Real.rpow 2 (2 * x) := by
  intro x
  rw [gap4, gap5]

/-- Source: `proof_gap/exercise_204/7.txt`. -/
theorem gap7 : ∀ x, ψ (ψ x) = Real.rpow 2 (Real.rpow 2 x) := by
  intro x
  rfl

/-- Source: `proof_gap/exercise_204/8.txt`. -/
theorem gap8 : ∀ x, ψ (φ x) = Real.rpow 2 (x ^ 2) := by
  intro x
  rfl

end

end ProofGap.Exercise204

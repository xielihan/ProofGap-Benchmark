import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise361_5

noncomputable section

def signedCbrt (x : ℝ) : ℝ :=
  if 0 ≤ x then Real.rpow x (1 / 3 : ℝ)
  else -Real.rpow (-x) (1 / 3 : ℝ)

def f (x : ℝ) : ℝ := 1 + signedCbrt (x - 2)

def IsCenter (g : ℝ → ℝ) (x₀ y₀ : ℝ) : Prop :=
  ∀ t, g (x₀ + t) + g (x₀ - t) = 2 * y₀

/-- Source: `proof_gap/exercise_361_5/1.txt`; state the actual reflected-value identity directly. -/
theorem gap1 : ∀ t, f (2 + t) + f (2 - t) = 2 := by
  intro t
  change (1 + signedCbrt ((2 + t) - 2)) +
      (1 + signedCbrt ((2 - t) - 2)) = 2
  have hplus : (2 + t) - 2 = t := by ring
  have hminus : (2 - t) - 2 = -t := by ring
  rw [hplus, hminus]
  rcases lt_trichotomy t 0 with ht | ht | ht
  · have htn : ¬ 0 ≤ t := not_le_of_gt ht
    have hneg : 0 ≤ -t := neg_nonneg.mpr (le_of_lt ht)
    simp [signedCbrt, htn, hneg] <;> ring
  · subst t
    norm_num [signedCbrt]
  · have ht0 : 0 ≤ t := le_of_lt ht
    have hneg : ¬ 0 ≤ -t := by
      rw [neg_nonneg]
      exact not_le_of_gt ht
    simp [signedCbrt, ht0, hneg] <;> ring

/-- Source: `proof_gap/exercise_361_5/2.txt`. -/
theorem gap2 : IsCenter f 2 1 := by
  simpa [IsCenter] using gap1

end

end ProofGap.Exercise361_5

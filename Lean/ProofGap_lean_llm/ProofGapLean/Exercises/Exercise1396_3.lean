import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ProofGap.Exercise1396_3

noncomputable section

def root (n : ℕ) (x : ℝ) : ℝ := Real.rpow x (1 / (n : ℝ))

def exactValue : ℝ :=
  2 * Real.rpow (1 - (3 / 128 : ℝ)) (1 / 12 : ℝ)

def taylorValue : ℝ :=
  2 * (1 - (1 / 12 : ℝ) * (3 / 128 : ℝ))

def errorBound : ℝ :=
  (3 / 128 : ℝ) ^ 2 * (1 / (1 - (3 / 128 : ℝ)))

def ApproxWithin (a b ε : ℝ) : Prop := |a - b| < ε

private lemma twelfthRootBounds :
    (499 / 500 : ℝ) < Real.rpow (125 / 128 : ℝ) (1 / 12 : ℝ) ∧
      Real.rpow (125 / 128 : ℝ) (1 / 12 : ℝ) < (3993 / 4000 : ℝ) := by
  constructor
  · have hp : Real.rpow (499 / 500 : ℝ) 12 < (125 / 128 : ℝ) := by
      norm_num [Real.rpow_natCast]
    have hcollapse :
        Real.rpow (Real.rpow (499 / 500 : ℝ) (12 : ℝ)) (1 / 12 : ℝ) =
          Real.rpow (499 / 500 : ℝ) ((12 : ℝ) * (1 / 12 : ℝ)) := by
      simpa only using
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 499 / 500)
          (12 : ℝ) (1 / 12 : ℝ)).symm
    calc
      (499 / 500 : ℝ) =
          Real.rpow (Real.rpow (499 / 500 : ℝ) 12) (1 / 12 : ℝ) := by
            rw [hcollapse]
            norm_num
      _ < Real.rpow (125 / 128 : ℝ) (1 / 12 : ℝ) := by
        apply Real.rpow_lt_rpow
        · norm_num
        · exact hp
        · norm_num
  · have hp : (125 / 128 : ℝ) < Real.rpow (3993 / 4000 : ℝ) 12 := by
      norm_num [Real.rpow_natCast]
    have hcollapse :
        Real.rpow (Real.rpow (3993 / 4000 : ℝ) (12 : ℝ)) (1 / 12 : ℝ) =
          Real.rpow (3993 / 4000 : ℝ) ((12 : ℝ) * (1 / 12 : ℝ)) := by
      simpa only using
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3993 / 4000)
          (12 : ℝ) (1 / 12 : ℝ)).symm
    calc
      Real.rpow (125 / 128 : ℝ) (1 / 12 : ℝ) <
          Real.rpow (Real.rpow (3993 / 4000 : ℝ) 12) (1 / 12 : ℝ) := by
        apply Real.rpow_lt_rpow
        · norm_num
        · exact hp
        · norm_num
      _ = (3993 / 4000 : ℝ) := by
        rw [hcollapse]
        norm_num

theorem gap1 :
    root 12 4000 = exactValue := by
  unfold root exactValue
  have hbase : (1 - (3 / 128 : ℝ)) = 125 / 128 := by
    norm_num
  rw [hbase]
  have h4096 : (4096 : ℝ) = Real.rpow 2 12 := by
    norm_num [Real.rpow_natCast]
  have htwo : Real.rpow (4096 : ℝ) (1 / 12 : ℝ) = 2 := by
    rw [h4096]
    have hcollapse :
        Real.rpow (Real.rpow (2 : ℝ) (12 : ℝ)) (1 / 12 : ℝ) =
          Real.rpow (2 : ℝ) ((12 : ℝ) * (1 / 12 : ℝ)) := by
      simpa only using
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)
          (12 : ℝ) (1 / 12 : ℝ)).symm
    rw [hcollapse]
    norm_num
  calc
    Real.rpow 4000 (1 / 12 : ℝ) =
        Real.rpow ((4096 : ℝ) * (125 / 128 : ℝ)) (1 / 12 : ℝ) := by
          congr 1
          norm_num
    _ = Real.rpow (4096 : ℝ) (1 / 12 : ℝ) *
          Real.rpow (125 / 128 : ℝ) (1 / 12 : ℝ) := by
          apply Real.mul_rpow
          · norm_num
          · norm_num
    _ = 2 * Real.rpow (125 / 128 : ℝ) (1 / 12 : ℝ) := by
          rw [htwo]

theorem gap2 :
    ApproxWithin exactValue taylorValue errorBound := by
  unfold ApproxWithin exactValue taylorValue errorBound
  have hbase : (1 - (3 / 128 : ℝ)) = 125 / 128 := by
    norm_num
  rw [hbase]
  have h := twelfthRootBounds
  rw [abs_lt]
  constructor <;> norm_num at h ⊢ <;> linarith [h.1, h.2]

theorem gap3 :
    ApproxWithin taylorValue (1.9960 : ℝ) (1 / 10000 : ℝ) := by
  unfold ApproxWithin taylorValue
  norm_num [abs_of_nonneg]

theorem gap4 :
    ApproxWithin (root 12 4000) (1.9960 : ℝ)
      (errorBound + 1 / 10000) := by
  have h2 := gap2
  have h3 := gap3
  unfold ApproxWithin at h2 h3 ⊢
  rw [gap1]
  calc
    |exactValue - (1.9960 : ℝ)| =
        |(exactValue - taylorValue) +
          (taylorValue - (1.9960 : ℝ))| := by
            congr 1
            ring
    _ ≤ |exactValue - taylorValue| +
          |taylorValue - (1.9960 : ℝ)| := abs_add_le _ _
    _ < errorBound + 1 / 10000 := add_lt_add h2 h3

theorem gap5 :
    let Δ := |exactValue - taylorValue|
    0 ≤ Δ ∧ Δ < errorBound := by
  dsimp
  exact ⟨abs_nonneg _, by simpa [ApproxWithin] using gap2⟩

theorem gap6 :
    ApproxWithin errorBound (0.0005625 : ℝ) (1 / 1000000 : ℝ) := by
  norm_num [ApproxWithin, errorBound, abs_of_nonneg]

end

end ProofGap.Exercise1396_3

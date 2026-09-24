import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise401

noncomputable section

def HasLimitAt (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x,
    0 < |x - a| → |x - a| < δ → |f x - b| < ε

/-- Source: `proof_gap/exercise_401/1.txt`. -/
theorem gap1 : ∀ x : ℝ, |x ^ 2 - 4| = |x - 2| * |x + 2| := by
  intro x
  rw [show x ^ 2 - 4 = (x - 2) * (x + 2) by ring, abs_mul]

/-- Source: `proof_gap/exercise_401/2.txt`. -/
theorem gap2 : ∀ x : ℝ, |x - 2| < 1 → 1 < x := by
  intro x hx
  have h := (abs_lt.mp hx).1
  linarith

/-- Source: `proof_gap/exercise_401/3.txt`. -/
theorem gap3 : ∀ x : ℝ, |x - 2| < 1 → x < 3 := by
  intro x hx
  have h := (abs_lt.mp hx).2
  linarith

/-- Source: `proof_gap/exercise_401/4.txt`. -/
theorem gap4 : ∀ x : ℝ, |x - 2| < 1 → (1 : ℝ) < 3 := by
  intro x hx
  norm_num

/-- Source: `proof_gap/exercise_401/5.txt`. -/
theorem gap5 : ∀ x : ℝ, |x - 2| < 1 →
    |x ^ 2 - 4| = |x - 2| * |x + 2| := by
  intro x hx
  exact gap1 x

/-- Source: `proof_gap/exercise_401/6.txt`. -/
theorem gap6 : ∀ x : ℝ, 0 < |x - 2| → |x - 2| < 1 →
    |x - 2| * |x + 2| < 5 * |x - 2| := by
  intro x hx0 hx
  have hxplus : |x + 2| < 5 := by
    rw [abs_of_nonneg]
    · linarith [gap3 x hx]
    · linarith [gap2 x hx]
  have hprod :
      |x - 2| * |x + 2| < |x - 2| * 5 :=
    mul_lt_mul_of_pos_left hxplus hx0
  simpa [mul_comm] using hprod

/-- Source: `proof_gap/exercise_401/7.txt`. -/
theorem gap7 : ∀ x : ℝ, 0 < |x - 2| → |x - 2| < 1 →
    |x ^ 2 - 4| < 5 * |x - 2| := by
  intro x hx0 hx
  rw [gap1 x]
  exact gap6 x hx0 hx

/-- Source: `proof_gap/exercise_401/8.txt`; choose `δ` after `ε`, not uniformly for every tolerance. -/
theorem gap8 : ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ,
    0 < |x - 2| → |x - 2| < δ → |x ^ 2 - 4| < ε := by
  intro ε hε
  have hδ : 0 < min (1 : ℝ) (ε / 5) := by
    rw [lt_min_iff]
    constructor
    · norm_num
    · exact div_pos hε (by norm_num)
  refine ⟨min 1 (ε / 5), hδ, ?_⟩
  intro x hx0 hxδ
  have hsmall : |x - 2| < 1 :=
    lt_of_lt_of_le hxδ (min_le_left _ _)
  have heps : |x - 2| < ε / 5 :=
    lt_of_lt_of_le hxδ (min_le_right _ _)
  have hxplus : |x + 2| < 5 := by
    rw [abs_of_nonneg]
    · linarith [gap3 x hsmall]
    · linarith [gap2 x hsmall]
  have hprod : |x - 2| * |x + 2| < |x - 2| * 5 :=
    mul_lt_mul_of_pos_left hxplus hx0
  have hscale : |x - 2| * 5 < ε := by
    linarith
  rw [gap1 x]
  exact lt_trans hprod hscale

/-- Source: `proof_gap/exercise_401/9.txt`. -/
theorem gap9 : HasLimitAt (fun x : ℝ => x ^ 2) 2 4 := by
  unfold HasLimitAt
  simpa using gap8

/-- Source: `proof_gap/exercise_401/10.txt`. -/
theorem gap10 : ∃ δ : ℝ, δ = 0.02 := by
  exact ⟨0.02, rfl⟩

/-- Source: `proof_gap/exercise_401/11.txt`. -/
theorem gap11 : ∃ δ : ℝ, δ = 0.002 := by
  exact ⟨0.002, rfl⟩

/-- Source: `proof_gap/exercise_401/12.txt`. -/
theorem gap12 : ∃ δ : ℝ, δ = 0.0002 := by
  exact ⟨0.0002, rfl⟩

/-- Source: `proof_gap/exercise_401/13.txt`. -/
theorem gap13 : ∃ δ : ℝ, δ = 0.00002 := by
  exact ⟨0.00002, rfl⟩

/-- Source: `proof_gap/exercise_401/14.txt`. -/
theorem gap14 : HasLimitAt (fun x : ℝ => x ^ 2) 2 4 := by
  exact gap9

end

end ProofGap.Exercise401

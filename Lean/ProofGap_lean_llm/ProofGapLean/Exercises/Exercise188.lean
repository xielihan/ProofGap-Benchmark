import ProofGapLean.Prelude.Discrete
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise188

noncomputable section

def y (x : ℝ) : ℝ := x + (⌊2 * x⌋ : ℤ)
def domain : Set ℝ := Set.Ioo 0 1
def valueSet : Set ℝ := {t | ∃ x ∈ domain, t = y x}

/-- Source: `proof_gap/exercise_188/1.txt`. -/
theorem gap1 : ∀ x : ℝ, 0 < x → x < 1 / 2 → ⌊2 * x⌋ = (0 : ℤ) := by
  intro x hx0 hx1
  apply Int.floor_eq_iff.mpr
  norm_num
  constructor <;> linarith

/-- Source: `proof_gap/exercise_188/2.txt`. -/
theorem gap2 : ∀ x : ℝ, 0 < x → x < 1 / 2 → y x = x := by
  intro x hx0 hx1
  rw [y, gap1 x hx0 hx1]
  norm_num

/-- Source: `proof_gap/exercise_188/3.txt`. -/
theorem gap3 : ∀ x : ℝ, 1 / 2 ≤ x → x < 1 → ⌊2 * x⌋ = (1 : ℤ) := by
  intro x hx0 hx1
  apply Int.floor_eq_iff.mpr
  norm_num
  constructor <;> linarith

/-- Source: `proof_gap/exercise_188/4.txt`. -/
theorem gap4 : ∀ x : ℝ, 1 / 2 ≤ x → x < 1 → y x = x + 1 := by
  intro x hx0 hx1
  rw [y, gap3 x hx0 hx1]
  norm_num

/-- Source: `proof_gap/exercise_188/5.txt`; remove the irrelevant universal x. -/
theorem gap5 : y (1 / 2) = 3 / 2 := by
  rw [gap4 (1 / 2) (by norm_num) (by norm_num)]
  norm_num

/-- Source: `proof_gap/exercise_188/6.txt`; replace the free family `E_x`. -/
theorem gap6 : valueSet = Set.Ioo 0 (1 / 2) ∪ Set.Ico (3 / 2) 2 := by
  ext t
  constructor
  · rintro ⟨x, ⟨hx0, hx1⟩, rfl⟩
    by_cases hx : x < 1 / 2
    · left
      rw [gap2 x hx0 hx]
      exact ⟨hx0, hx⟩
    · right
      have hxhalf : 1 / 2 ≤ x := not_lt.mp hx
      rw [gap4 x hxhalf hx1]
      constructor <;> linarith
  · rintro (ht | ht)
    · refine ⟨t, ⟨ht.1, lt_trans ht.2 (by norm_num)⟩, ?_⟩
      exact (gap2 t ht.1 ht.2).symm
    · let x := t - 1
      have hxhalf : 1 / 2 ≤ x := by
        dsimp [x]
        linarith [ht.1]
      have hx1 : x < 1 := by
        dsimp [x]
        linarith [ht.2]
      have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hxhalf
      refine ⟨x, ⟨hx0, hx1⟩, ?_⟩
      rw [gap4 x hxhalf hx1]
      dsimp [x]
      ring

end

end ProofGap.Exercise188

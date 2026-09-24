import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise194_1

def f (x : ℝ) : ℝ := x - x ^ 3

/-- Source: `proof_gap/exercise_194_1/1.txt`. -/
theorem gap1 : ∃ x : ℝ, f x = 0 := by
  refine ⟨0, ?_⟩
  norm_num [f]

/-- Source: `proof_gap/exercise_194_1/2.txt`. -/
theorem gap2 : {x : ℝ | f x = 0} = ({-1, 0, 1} : Set ℝ) := by
  apply Set.ext
  intro x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [show f x = x * (1 - x) * (1 + x) by unfold f; ring]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (by linarith))
    · exact Or.inl (by linarith)
  · rintro (h | h | h)
    · subst x
      norm_num
    · subst x
      norm_num
    · subst x
      norm_num

/-- Source: `proof_gap/exercise_194_1/3.txt`. -/
theorem gap3 : ∀ x : ℝ,
    f x > 0 ↔ x * (1 - x) * (1 + x) > 0 := by
  intro x
  rw [show f x = x * (1 - x) * (1 + x) by unfold f; ring]

/-- Source: `proof_gap/exercise_194_1/4.txt`. -/
theorem gap4 :
    {x : ℝ | f x > 0} = Set.Iio (-1) ∪ Set.Ioo 0 1 := by
  apply Set.ext
  intro x
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioo]
  rw [gap3]
  constructor
  · intro h
    rcases mul_pos_iff.mp h with ⟨hxy, hz⟩ | ⟨hxy, hz⟩
    · rcases mul_pos_iff.mp hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · exact Or.inr ⟨by linarith, by linarith⟩
      · exfalso
        linarith
    · rcases mul_neg_iff.mp hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · exfalso
        linarith
      · exact Or.inl (by linarith)
  · rintro (hx | ⟨hx0, hx1⟩)
    · exact mul_pos_of_neg_of_neg
        (mul_neg_of_neg_of_pos (by linarith) (by linarith))
        (by linarith)
    · exact mul_pos
        (mul_pos (by linarith) (by linarith))
        (by linarith)

/-- Source: `proof_gap/exercise_194_1/5.txt`. -/
theorem gap5 : ∃ x : ℝ, x * (1 - x) * (1 + x) < 0 := by
  refine ⟨2, by norm_num⟩

/-- Source: `proof_gap/exercise_194_1/6.txt`. -/
theorem gap6 :
    {x : ℝ | f x < 0} = Set.Ioo (-1) 0 ∪ Set.Ioi 1 := by
  apply Set.ext
  intro x
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Ioo, Set.mem_Ioi]
  rw [show f x = x * (1 - x) * (1 + x) by unfold f; ring]
  constructor
  · intro h
    rcases mul_neg_iff.mp h with ⟨hxy, hz⟩ | ⟨hxy, hz⟩
    · rcases mul_pos_iff.mp hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;>
        exfalso <;> linarith
    · rcases mul_neg_iff.mp hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · exact Or.inr (by linarith)
      · exact Or.inl ⟨by linarith, by linarith⟩
  · rintro (⟨hxm, hx0⟩ | hx1)
    · exact mul_neg_of_neg_of_pos
        (mul_neg_of_neg_of_pos (by linarith) (by linarith))
        (by linarith)
    · exact mul_neg_of_neg_of_pos
        (mul_neg_of_pos_of_neg (by linarith) (by linarith))
        (by linarith)

end ProofGap.Exercise194_1

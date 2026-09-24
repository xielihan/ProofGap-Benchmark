import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise194_3

def f (x : ℝ) : ℝ := (x + |x|) * (1 - x)

/-- Exercise 194_3, gap 1. -/
theorem gap1 : ∃ x : ℝ, f x = 0 := by
  exact ⟨0, by norm_num [f]⟩

/-- Exercise 194_3, gap 2. -/
theorem gap2 : {x : ℝ | f x = 0} = Set.Iic 0 ∪ ({1} : Set ℝ) := by
  apply Set.ext
  intro x
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Iic,
    Set.mem_singleton_iff]
  constructor
  · intro hf
    by_cases hx : x ≤ 0
    · exact Or.inl hx
    · right
      have hxpos : 0 < x := lt_of_not_ge hx
      rw [f, abs_of_pos hxpos] at hf
      rcases mul_eq_zero.mp hf with h | h
      · linarith
      · linarith
  · rintro (hx | rfl)
    · rw [f, abs_of_nonpos hx]
      ring
    · norm_num [f]

/-- Exercise 194_3, gap 3. -/
theorem gap3 : ∀ x : ℝ, 0 ≤ x + |x| := by
  intro x
  linarith [neg_le_abs x]

/-- Exercise 194_3, gap 4. -/
theorem gap4 : ∀ x : ℝ, f x > 0 → 0 < 1 - x ∧ 0 < x + |x| := by
  intro x hf
  rcases mul_pos_iff.mp hf with h | h
  · exact ⟨h.2, h.1⟩
  · exfalso
    linarith [gap3 x]

/-- Exercise 194_3, gap 5. -/
theorem gap5 : {x : ℝ | f x > 0} = Set.Ioo 0 1 := by
  apply Set.ext
  intro x
  simp only [Set.mem_setOf_eq, Set.mem_Ioo]
  constructor
  · intro hf
    have h := gap4 x hf
    refine ⟨?_, by linarith [h.1]⟩
    by_contra hx
    have hxnonpos : x ≤ 0 := le_of_not_gt hx
    rw [abs_of_nonpos hxnonpos] at h
    linarith
  · rintro ⟨hx0, hx1⟩
    rw [f, abs_of_pos hx0]
    exact mul_pos (by linarith) (by linarith)

/-- Exercise 194_3, gap 6. -/
theorem gap6 : ∃ x : ℝ, f x < 0 := by
  exact ⟨2, by norm_num [f]⟩

/-- Exercise 194_3, gap 7. -/
theorem gap7 : ∃ x : ℝ, 0 < x := by
  exact ⟨1, by norm_num⟩

/-- Exercise 194_3, gap 8. -/
theorem gap8 : ∃ x : ℝ, 1 - x < 0 := by
  exact ⟨2, by norm_num⟩

/-- Exercise 194_3, gap 9. -/
theorem gap9 : {x : ℝ | f x < 0} = Set.Ioi 1 := by
  apply Set.ext
  intro x
  simp only [Set.mem_setOf_eq, Set.mem_Ioi]
  constructor
  · intro hf
    rcases mul_neg_iff.mp hf with h | h
    · linarith
    · exfalso
      linarith [gap3 x]
  · intro hx
    have hxpos : 0 < x := by linarith
    rw [f, abs_of_pos hxpos]
    exact mul_neg_of_pos_of_neg (by linarith) (by linarith)

end ProofGap.Exercise194_3

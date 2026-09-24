import ProofGapLean.Prelude.Elementary

namespace ProofGap.Exercise817

noncomputable section

def f (x : ℝ) : ℝ := Real.sign x

/-- Exercise 817, gap 1. -/
theorem gap1 (x y : ℝ) : f (x * y) = Real.sign (x * y) := by
  rfl

/-- Exercise 817, gap 2. -/
theorem gap2 (x y : ℝ) (h : x * y > 0) : x * y > 0 := by
  exact h

/-- Exercise 817, gap 3. -/
theorem gap3 (x y : ℝ) (h : x * y > 0) :
    Real.sign (x * y) = Real.sign x * Real.sign y := by
  have hx : x ≠ 0 := by
    intro hx
    subst x
    simp at h
  have hy : y ≠ 0 := by
    intro hy
    subst y
    simp at h
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · rcases lt_or_gt_of_ne hy with hyneg | hypos
    · simp [Real.sign_of_pos h, Real.sign_of_neg hxneg,
        Real.sign_of_neg hyneg]
    · have hprodneg : x * y < 0 := mul_neg_of_neg_of_pos hxneg hypos
      exfalso
      exact (not_lt_of_ge (le_of_lt h)) hprodneg
  · rcases lt_or_gt_of_ne hy with hyneg | hypos
    · have hprodneg : x * y < 0 := mul_neg_of_pos_of_neg hxpos hyneg
      exfalso
      exact (not_lt_of_ge (le_of_lt h)) hprodneg
    · simp [Real.sign_of_pos h, Real.sign_of_pos hxpos,
        Real.sign_of_pos hypos]

/-- Exercise 817, gap 4. -/
theorem gap4 (x y : ℝ) (h : x * y > 0) :
    Real.sign x * Real.sign y = 1 := by
  calc
    Real.sign x * Real.sign y = Real.sign (x * y) := (gap3 x y h).symm
    _ = 1 := Real.sign_of_pos h

/-- Exercise 817, gap 5. -/
theorem gap5 (x y : ℝ) (h : x * y > 0) : Real.sign (x * y) = 1 := by
  calc
    Real.sign (x * y) = Real.sign x * Real.sign y := gap3 x y h
    _ = 1 := gap4 x y h

/-- Exercise 817, gap 6. -/
theorem gap6 (x y : ℝ) (h : x * y < 0) : x * y < 0 := by
  exact h

/-- Exercise 817, gap 7. -/
theorem gap7 (x y : ℝ) (h : x * y < 0) :
    Real.sign (x * y) = Real.sign x * Real.sign y := by
  have hx : x ≠ 0 := by
    intro hx
    subst x
    simp at h
  have hy : y ≠ 0 := by
    intro hy
    subst y
    simp at h
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · rcases lt_or_gt_of_ne hy with hyneg | hypos
    · have hprodpos : 0 < x * y := mul_pos_of_neg_of_neg hxneg hyneg
      exfalso
      exact (not_lt_of_ge (le_of_lt hprodpos)) h
    · simp [Real.sign_of_neg h, Real.sign_of_neg hxneg,
        Real.sign_of_pos hypos]
  · rcases lt_or_gt_of_ne hy with hyneg | hypos
    · simp [Real.sign_of_neg h, Real.sign_of_pos hxpos,
        Real.sign_of_neg hyneg]
    · have hprodpos : 0 < x * y := mul_pos hxpos hypos
      exfalso
      exact (not_lt_of_ge (le_of_lt hprodpos)) h

/-- Exercise 817, gap 8. -/
theorem gap8 (x y : ℝ) (h : x * y < 0) :
    Real.sign x * Real.sign y = -1 := by
  calc
    Real.sign x * Real.sign y = Real.sign (x * y) := (gap7 x y h).symm
    _ = -1 := Real.sign_of_neg h

/-- Exercise 817, gap 9. -/
theorem gap9 (x y : ℝ) (h : x * y < 0) : Real.sign (x * y) = -1 := by
  calc
    Real.sign (x * y) = Real.sign x * Real.sign y := gap7 x y h
    _ = -1 := gap8 x y h

/-- Exercise 817, gap 10. -/
theorem gap10 (x y : ℝ) (h : x * y = 0) : x = 0 ∨ y = 0 := by
  exact mul_eq_zero.mp h

/-- Exercise 817, gap 11. -/
theorem gap11 (x y : ℝ) (h : x * y = 0) :
    Real.sign (x * y) = Real.sign x * Real.sign y := by
  rcases gap10 x y h with hx | hy
  · simp [hx]
  · simp [hy]

/-- Exercise 817, gap 12. -/
theorem gap12 (x y : ℝ) (h : x * y = 0) :
    Real.sign x * Real.sign y = 0 := by
  rcases gap10 x y h with hx | hy
  · simp [hx]
  · simp [hy]

/-- Exercise 817, gap 13. -/
theorem gap13 (x y : ℝ) (h : x * y = 0) : Real.sign (x * y) = 0 := by
  simp [h]

/-- Exercise 817, gap 14. -/
theorem gap14 (x y : ℝ) :
    Real.sign (x * y) = Real.sign x * Real.sign y := by
  rcases lt_trichotomy (x * y) 0 with hneg | hzero | hpos
  · exact gap7 x y hneg
  · exact gap11 x y hzero
  · exact gap3 x y hpos

/-- Exercise 817, gap 15. -/
theorem gap15 (x y : ℝ) : f (x * y) = f x * f y := by
  simpa [f] using (gap14 x y)

/-- Exercise 817, gap 16; remove vacuous real-set membership premises. -/
theorem gap16 : ∀ x y : ℝ, f (x * y) = f x * f y := by
  intro x y
  exact gap15 x y

end

end ProofGap.Exercise817

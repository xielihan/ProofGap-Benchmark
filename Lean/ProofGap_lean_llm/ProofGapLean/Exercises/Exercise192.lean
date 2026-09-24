import ProofGapLean.Prelude.Elementary

namespace ProofGap.Exercise192

noncomputable section

def f (x : ℝ) : ℝ := if x ≤ 0 then 1 + x else Real.rpow 2 x

/-- Exercise 192, gap 1. -/
theorem gap1 : f (-2) = 1 - 2 := by
  norm_num [f]

/-- Exercise 192, gap 2. -/
theorem gap2 : (1 : ℝ) - 2 = -1 := by
  norm_num

/-- Exercise 192, gap 3. -/
theorem gap3 : f (-2) = -1 := by
  rw [gap1, gap2]

/-- Exercise 192, gap 4. -/
theorem gap4 : f (-1) = 1 - 1 := by
  norm_num [f]

/-- Exercise 192, gap 5. -/
theorem gap5 : (1 : ℝ) - 1 = 0 := by
  norm_num

/-- Exercise 192, gap 6. -/
theorem gap6 : f (-1) = 0 := by
  rw [gap4, gap5]

/-- Exercise 192, gap 7. -/
theorem gap7 : f 0 = 1 + 0 := by
  norm_num [f]

/-- Exercise 192, gap 8. -/
theorem gap8 : (1 : ℝ) + 0 = 1 := by
  norm_num

/-- Exercise 192, gap 9. -/
theorem gap9 : f 0 = 1 := by
  rw [gap7, gap8]

/-- Exercise 192, gap 10. -/
theorem gap10 : f 1 = Real.rpow 2 1 := by
  norm_num [f]

/-- Exercise 192, gap 11. -/
theorem gap11 : Real.rpow 2 1 = 2 := by
  norm_num

/-- Exercise 192, gap 12. -/
theorem gap12 : f 1 = 2 := by
  rw [gap10, gap11]

/-- Exercise 192, gap 13. -/
theorem gap13 : f 2 = Real.rpow 2 2 := by
  norm_num [f]

/-- Exercise 192, gap 14. -/
theorem gap14 : Real.rpow 2 2 = 4 := by
  norm_num [Real.rpow_natCast]

/-- Exercise 192, gap 15. -/
theorem gap15 : f 2 = 4 := by
  rw [gap13, gap14]

end

end ProofGap.Exercise192

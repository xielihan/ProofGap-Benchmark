import ProofGapLean.Prelude.Discrete

namespace ProofGap.Exercise191

noncomputable section

def f (x : ℝ) : ℝ := 1 + (⌊x⌋ : ℤ)

/-- Exercise 191, gap 1. -/
theorem gap1 : f 0.9 = f 0.99 := by
  norm_num [f]

/-- Exercise 191, gap 2. -/
theorem gap2 : f 0.99 = f 0.999 := by
  norm_num [f]

/-- Exercise 191, gap 3. -/
theorem gap3 : f 0.999 = 1 := by
  norm_num [f]

/-- Exercise 191, gap 4. -/
theorem gap4 : f 0.9 = 1 := by
  norm_num [f]

/-- Exercise 191, gap 5. -/
theorem gap5 : f 1 = 2 := by
  norm_num [f]

end

end ProofGap.Exercise191

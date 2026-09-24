import ProofGapLean.Prelude.Analysis

namespace ProofGap.Exercise650_3

noncomputable section

def target (x : ℝ) : ℝ := x * Real.sin (1 / x)

/-- Exercise 650_3, gap 1. -/
theorem gap1 (x : ℝ) : |target x| ≤ |x| := by
  rw [target, abs_mul]
  calc
    |x| * |Real.sin (1 / x)| ≤ |x| * 1 :=
      mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg x)
    _ = |x| := mul_one _

/-- Exercise 650_3, gap 2. -/
theorem gap2 :
    Asymptotics.IsBigO (nhdsWithin 0 (Set.Ioi 0))
      target (fun x : ℝ => |x|) := by
  refine Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun x => ?_)
  simpa only [Real.norm_eq_abs, abs_abs, one_mul] using gap1 x

/-- Exercise 650_3, gap 3. -/
theorem gap3 :
    Asymptotics.IsBigO (nhdsWithin 0 (Set.Ioi 0))
      target (fun x : ℝ => |x|) := by
  exact gap2

end

end ProofGap.Exercise650_3

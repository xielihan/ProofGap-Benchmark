import ProofGapLean.Prelude.Analysis

namespace ProofGap.Exercise650_6

noncomputable section

def target (x : ℝ) : ℝ := Real.arctan (1 / x)

/-- Exercise 650_6, gap 1. -/
theorem gap1 (x : ℝ) : |target x| ≤ Real.pi / 2 := by
  unfold target
  rw [abs_le]
  exact
    ⟨le_of_lt (Real.neg_pi_div_two_lt_arctan _),
      le_of_lt (Real.arctan_lt_pi_div_two _)⟩

/-- Exercise 650_6, gap 2. -/
theorem gap2 :
    Asymptotics.IsBigO (nhdsWithin 0 (Set.Ioi 0))
      target (fun _ : ℝ => (1 : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound (Real.pi / 2)
  exact Filter.Eventually.of_forall (fun x => by
    simpa only [Real.norm_eq_abs, norm_one, mul_one] using gap1 x)

/-- Exercise 650_6, gap 3. -/
theorem gap3 :
    Asymptotics.IsBigO (nhdsWithin 0 (Set.Ioi 0))
      target (fun _ : ℝ => (1 : ℝ)) := by
  exact gap2

end

end ProofGap.Exercise650_6

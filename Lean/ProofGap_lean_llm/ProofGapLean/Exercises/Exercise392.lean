import ProofGapLean.Prelude.Elementary

namespace ProofGap.Exercise392

noncomputable section

def f (x : ℝ) : ℝ := Real.sin x
def rangeOnPositive : Set ℝ :=
  {y | ∃ x ∈ Set.Ioi (0 : ℝ), y = f x}

/-- Exercise 392, gap 1. -/
private theorem rangeOnPositive_extrema :
    (∀ y ∈ rangeOnPositive, (-1 : ℝ) ≤ y) ∧
      (∀ y ∈ rangeOnPositive, y ≤ (1 : ℝ)) ∧
        (-1 : ℝ) ∈ rangeOnPositive ∧
          (1 : ℝ) ∈ rangeOnPositive := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y hy
    change ∃ x ∈ Set.Ioi (0 : ℝ), y = f x at hy
    rcases hy with ⟨x, _, rfl⟩
    simpa [f] using Real.neg_one_le_sin x
  · intro y hy
    change ∃ x ∈ Set.Ioi (0 : ℝ), y = f x at hy
    rcases hy with ⟨x, _, rfl⟩
    simpa [f] using Real.sin_le_one x
  · change ∃ x ∈ Set.Ioi (0 : ℝ), (-1 : ℝ) = f x
    refine ⟨Real.pi + Real.pi / 2, ?_, ?_⟩
    · show (0 : ℝ) < Real.pi + Real.pi / 2
      exact add_pos Real.pi_pos (half_pos Real.pi_pos)
    · simp [f, Real.sin_add]
  · change ∃ x ∈ Set.Ioi (0 : ℝ), (1 : ℝ) = f x
    refine ⟨Real.pi / 2, ?_, ?_⟩
    · show (0 : ℝ) < Real.pi / 2
      exact half_pos Real.pi_pos
    · simpa [f] using Real.sin_pi_div_two.symm

theorem gap1 : sInf rangeOnPositive = -1 := by
  rcases rangeOnPositive_extrema with ⟨h_lower, _, h_min, _⟩
  apply le_antisymm
  · exact csInf_le ⟨(-1 : ℝ), h_lower⟩ h_min
  · exact le_csInf ⟨(-1 : ℝ), h_min⟩ h_lower

/-- Exercise 392, gap 2. -/
theorem gap2 : sSup rangeOnPositive = 1 := by
  rcases rangeOnPositive_extrema with ⟨_, h_upper, _, h_max⟩
  apply le_antisymm
  · exact csSup_le ⟨(1 : ℝ), h_max⟩ h_upper
  · exact le_csSup ⟨(1 : ℝ), h_upper⟩ h_max

end

end ProofGap.Exercise392

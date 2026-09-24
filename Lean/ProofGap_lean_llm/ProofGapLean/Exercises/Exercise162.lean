import ProofGapLean.Prelude.Elementary

namespace ProofGap.Exercise162

noncomputable section

def domain : Set ℝ := {x | 0 ≤ -(Real.sin (Real.pi * x)) ^ 2}

/-- Exercise 162, gap 1. -/
theorem gap1 : ∀ x : ℝ, 0 ≤ (Real.sin (Real.pi * x)) ^ 2 := by
  intro x
  exact sq_nonneg _

/-- Exercise 162, gap 2. -/
theorem gap2 : ∀ x : ℝ,
    0 ≤ -(Real.sin (Real.pi * x)) ^ 2 ↔ Real.sin (Real.pi * x) = 0 := by
  intro x
  constructor
  · intro h
    have hsquare : (Real.sin (Real.pi * x)) ^ 2 = 0 :=
      le_antisymm (neg_nonneg.mp h) (gap1 x)
    exact (sq_eq_zero_iff).1 hsquare
  · intro h
    simp [h]

/-- Exercise 162, gap 3. -/
theorem gap3 : ∀ x : ℝ,
    Real.sin (Real.pi * x) = 0 ↔ ∃ k : ℤ, x = k := by
  intro x
  constructor
  · intro h
    rcases Real.sin_eq_zero_iff.mp h with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    apply mul_left_cancel₀ Real.pi_ne_zero
    simpa [mul_comm] using hk.symm
  · rintro ⟨k, rfl⟩
    apply Real.sin_eq_zero_iff.mpr
    exact ⟨k, mul_comm _ _⟩

/-- Exercise 162, gap 4. -/
theorem gap4 : domain = {x : ℝ | ∃ k : ℤ, x = k} := by
  ext x
  exact (gap2 x).trans (gap3 x)

end

end ProofGap.Exercise162

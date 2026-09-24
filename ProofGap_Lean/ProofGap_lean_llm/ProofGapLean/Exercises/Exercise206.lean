import ProofGapLean.Prelude.Core

namespace ProofGap.Exercise206

noncomputable section

def sgn (x : ℝ) : ℝ := if x < 0 then -1 else if x = 0 then 0 else 1
def φ (x : ℝ) : ℝ := sgn x
def ψ (x : ℝ) : ℝ := 1 / x

/-- Exercise 206, gap 1. -/
theorem gap1 : ∀ x, φ (φ x) = sgn (sgn x) := by
  intro x
  rfl

/-- Exercise 206, gap 2. -/
theorem gap2 : ∀ x : ℝ, sgn (sgn x) = sgn x := by
  intro x
  by_cases hx : x < 0
  · simp [sgn, hx]
  · by_cases hx0 : x = 0
    · simp [sgn, hx0]
    · simp [sgn, hx, hx0]

/-- Exercise 206, gap 3. -/
theorem gap3 : ∀ x, φ (φ x) = sgn x := by
  intro x
  rw [gap1, gap2]

/-- Exercise 206, gap 4; reciprocal composition is restricted to x≠0. -/
theorem gap4 : ∀ x : ℝ, x ≠ 0 → ψ (ψ x) = 1 / (1 / x) := by
  intro x _
  rfl

/-- Exercise 206, gap 5. -/
theorem gap5 : ∀ x : ℝ, x ≠ 0 → 1 / (1 / x) = x := by
  intro x hx
  simp [hx]

/-- Exercise 206, gap 6. -/
theorem gap6 : ∀ x : ℝ, x ≠ 0 → ψ (ψ x) = x := by
  intro x hx
  rw [gap4 x hx, gap5 x hx]

/-- Exercise 206, gap 7. -/
theorem gap7 : ∀ x : ℝ, x ≠ 0 → φ (ψ x) = sgn (1 / x) := by
  intro x _
  rfl

/-- Exercise 206, gap 8. -/
theorem gap8 : ∀ x : ℝ, x ≠ 0 → sgn (1 / x) = sgn x := by
  intro x hx
  by_cases hneg : x < 0
  · have hinvneg : 1 / x < 0 := one_div_neg.mpr hneg
    simp [sgn, hneg, hinvneg]
  · have hpos : 0 < x := lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hx)
    have hinvpos : 0 < 1 / x := one_div_pos.mpr hpos
    have hinv0 : 1 / x ≠ 0 := ne_of_gt hinvpos
    simp [sgn, hneg, hx, not_lt_of_ge hinvpos.le, hinv0]

/-- Exercise 206, gap 9. -/
theorem gap9 : ∀ x : ℝ, x ≠ 0 → φ (ψ x) = sgn x := by
  intro x hx
  rw [gap7 x hx, gap8 x hx]

/-- Exercise 206, gap 10. -/
theorem gap10 : ∀ x : ℝ, x ≠ 0 → ψ (φ x) = 1 / sgn x := by
  intro x _
  rfl

/-- Exercise 206, gap 11. -/
theorem gap11 : ∀ x : ℝ, x ≠ 0 → 1 / sgn x = sgn x := by
  intro x hx
  by_cases hneg : x < 0
  · simp [sgn, hneg]
  · simp [sgn, hneg, hx]

/-- Exercise 206, gap 12. -/
theorem gap12 : ∀ x : ℝ, x ≠ 0 → ψ (φ x) = sgn x := by
  intro x hx
  rw [gap10 x hx, gap11 x hx]

end

end ProofGap.Exercise206

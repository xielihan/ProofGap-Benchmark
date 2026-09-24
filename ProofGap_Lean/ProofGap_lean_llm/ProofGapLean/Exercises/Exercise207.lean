import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise207

noncomputable section

def φ (x : ℝ) : ℝ := if x ≤ 0 then 0 else x
def ψ (x : ℝ) : ℝ := if x ≤ 0 then 0 else -x ^ 2

/-- Exercise 207, gap 1. -/
theorem gap1 : ∀ x, φ (φ x) = φ x := by
  intro x
  simp only [φ]
  split_ifs <;> linarith

/-- Exercise 207, gap 2. -/
theorem gap2 : ∀ x, ψ (ψ x) = 0 := by
  intro x
  simp only [ψ]
  split_ifs <;> nlinarith [sq_nonneg x]

/-- Exercise 207, gap 3. -/
theorem gap3 : ∀ x, φ (ψ x) = 0 := by
  intro x
  simp only [φ, ψ]
  split_ifs <;> nlinarith [sq_nonneg x]

/-- Exercise 207, gap 4. -/
theorem gap4 : ∀ x, ψ (φ x) = ψ x := by
  intro x
  simp only [φ, ψ]
  split_ifs <;> nlinarith

end

end ProofGap.Exercise207

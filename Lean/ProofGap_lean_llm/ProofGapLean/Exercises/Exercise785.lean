import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise785

def Modulus (δ ε : ℝ) : Prop :=
  ∀ x₁ ∈ Set.Icc (1 : ℝ) 10, ∀ x₂ ∈ Set.Icc (1 : ℝ) 10,
    |x₁ - x₂| < δ → |x₁ ^ 2 - x₂ ^ 2| < ε

/-- Exercise 785, gap 1; add interval membership for the
displayed `x₁,x₂`. -/
theorem gap1 (x₁ x₂ : ℝ) (hx₁ : x₁ ∈ Set.Icc (1 : ℝ) 10)
    (hx₂ : x₂ ∈ Set.Icc (1 : ℝ) 10) :
    |x₁ ^ 2 - x₂ ^ 2| = |x₁ - x₂| * |x₁ + x₂| := by
  have h : x₁ ^ 2 - x₂ ^ 2 = (x₁ - x₂) * (x₁ + x₂) := by
    ring
  rw [h, abs_mul]

/-- Exercise 785, gap 2; add interval membership. -/
theorem gap2 (x₁ x₂ : ℝ) (hx₁ : x₁ ∈ Set.Icc (1 : ℝ) 10)
    (hx₂ : x₂ ∈ Set.Icc (1 : ℝ) 10) :
    |x₁ - x₂| * |x₁ + x₂| ≤ 20 * |x₁ - x₂| := by
  rcases hx₁ with ⟨hx₁_lower, hx₁_upper⟩
  rcases hx₂ with ⟨hx₂_lower, hx₂_upper⟩
  have hsum_nonneg : 0 ≤ x₁ + x₂ := by
    linarith
  have hsum : |x₁ + x₂| ≤ 20 := by
    rw [abs_of_nonneg hsum_nonneg]
    linarith
  simpa [mul_comm] using
    (mul_le_mul_of_nonneg_left hsum (abs_nonneg (x₁ - x₂)))

/-- Exercise 785, gap 3; add interval membership. -/
theorem gap3 (x₁ x₂ : ℝ) (hx₁ : x₁ ∈ Set.Icc (1 : ℝ) 10)
    (hx₂ : x₂ ∈ Set.Icc (1 : ℝ) 10) :
    |x₁ ^ 2 - x₂ ^ 2| ≤ 20 * |x₁ - x₂| := by
  rw [gap1 x₁ x₂ hx₁ hx₂]
  exact gap2 x₁ x₂ hx₁ hx₂

/-- Exercise 785, gap 4; add interval membership. -/
theorem gap4 (x₁ x₂ ε : ℝ) (hx₁ : x₁ ∈ Set.Icc (1 : ℝ) 10)
    (hx₂ : x₂ ∈ Set.Icc (1 : ℝ) 10) (hε : 0 < ε)
    (hδ : |x₁ - x₂| < ε / 20) :
    |x₁ ^ 2 - x₂ ^ 2| < ε := by
  have hbound := gap3 x₁ x₂ hx₁ hx₂
  have hstrict : 20 * |x₁ - x₂| < ε := by
    nlinarith [hδ]
  exact lt_of_le_of_lt hbound hstrict

/-- Exercise 785, gap 5. -/
theorem gap5 (ε : ℝ) (hε : 0 < ε) : Modulus (ε / 20) ε := by
  unfold Modulus
  intro x₁ hx₁ x₂ hx₂ hdist
  exact gap4 x₁ x₂ ε hx₁ hx₂ hε hdist

/-- Exercise 785, gap 6; reverse the false necessity claim:
`δ≤ε/20` is a sufficient condition. -/
theorem gap6 (δ ε : ℝ) (hδ0 : 0 < δ) (hδε : δ ≤ ε / 20)
    (hε : 0 < ε) : Modulus δ ε := by
  unfold Modulus
  intro x₁ hx₁ x₂ hx₂ hdist
  exact gap4 x₁ x₂ ε hx₁ hx₂ hε (lt_of_lt_of_le hdist hδε)

/-- Exercise 785, gap 7; use the sufficient direction. -/
theorem gap7 (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ (1 : ℝ) / 20) :
    Modulus δ 1 := by
  exact gap6 δ 1 hδ0 hδ (by norm_num)

/-- Exercise 785, gap 8. -/
theorem gap8 : (1 : ℝ) / 20 = 0.05 := by
  norm_num

/-- Exercise 785, gap 9. -/
theorem gap9 (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 0.05) :
    Modulus δ 1 := by
  apply gap7 δ hδ0
  simpa only [gap8] using hδ

/-- Exercise 785, gap 10; use the sufficient direction. -/
theorem gap10 (δ : ℝ) (hδ0 : 0 < δ)
    (hδ : δ ≤ (0.01 : ℝ) / 20) : Modulus δ 0.01 := by
  exact gap6 δ 0.01 hδ0 hδ (by norm_num)

/-- Exercise 785, gap 11. -/
theorem gap11 : (0.01 : ℝ) / 20 = 0.0005 := by
  norm_num

/-- Exercise 785, gap 12. -/
theorem gap12 (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 0.0005) :
    Modulus δ 0.01 := by
  apply gap10 δ hδ0
  simpa only [gap11] using hδ

/-- Exercise 785, gap 13; use the sufficient direction. -/
theorem gap13 (δ : ℝ) (hδ0 : 0 < δ)
    (hδ : δ ≤ (0.0001 : ℝ) / 20) : Modulus δ 0.0001 := by
  exact gap6 δ 0.0001 hδ0 hδ (by norm_num)

/-- Exercise 785, gap 14. -/
theorem gap14 : (0.0001 : ℝ) / 20 = 0.000005 := by
  norm_num

/-- Exercise 785, gap 15. -/
theorem gap15 (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 0.000005) :
    Modulus δ 0.0001 := by
  apply gap13 δ hδ0
  simpa only [gap14] using hδ

/-- Exercise 785, gap 16; the claimed biconditional is not
sharp, so retain its valid sufficient direction. -/
theorem gap16 (δ ε : ℝ) (hε : 0 < ε) :
    δ ∈ {d : ℝ | 0 < d ∧ d ≤ ε / 20} → Modulus δ ε := by
  intro hδ
  exact gap6 δ ε hδ.1 hδ.2 hε

end ProofGap.Exercise785

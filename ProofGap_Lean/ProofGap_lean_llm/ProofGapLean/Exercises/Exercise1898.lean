import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise1898

noncomputable section

def q (x : ℝ) : ℝ := x ^ 4 + x ^ 2 + 1
def integrand (x : ℝ) : ℝ := (x ^ 2 + 1) / q x ^ 2
def algebraicPart (x : ℝ) : ℝ := (x ^ 3 + 2 * x) / (6 * q x)
def residual (x : ℝ) : ℝ :=
  ((1 / 6 : ℝ) * x ^ 2 + 2 / 3) / q x
def CoeffIdentity (A B C D A₁ B₁ C₁ D₁ : ℝ) : Prop :=
  ∀ x, x ^ 2 + 1 =
    (3 * A * x ^ 2 + 2 * B * x + C) * q x -
      (4 * x ^ 3 + 2 * x) * (A * x ^ 3 + B * x ^ 2 + C * x + D) +
      (A₁ * x ^ 3 + B₁ * x ^ 2 + C₁ * x + D₁) * q x

private theorem coefficient_values
    (A B C D A₁ B₁ C₁ D₁ : ℝ)
    (h : CoeffIdentity A B C D A₁ B₁ C₁ D₁) :
    A = 1 / 6 ∧ B = 0 ∧ C = 1 / 3 ∧ D = 0 ∧
      A₁ = 0 ∧ B₁ = 1 / 6 ∧ C₁ = 0 ∧ D₁ = 2 / 3 := by
  have h0 := h 0
  have h1 := h 1
  have hm1 := h (-1)
  have h2 := h 2
  have hm2 := h (-2)
  have h3 := h 3
  have hm3 := h (-3)
  have h4 := h 4
  norm_num [q] at h0 h1 hm1 h2 hm2 h3 hm3 h4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    linarith [h0, h1, hm1, h2, hm2, h3, hm3, h4]

theorem gap1 :
    ∃ A B C D A₁ B₁ C₁ D₁ : ℝ,
      CoeffIdentity A B C D A₁ B₁ C₁ D₁ := by
  refine ⟨1 / 6, 0, 1 / 3, 0, 0, 1 / 6, 0, 2 / 3, ?_⟩
  intro x
  unfold q
  ring

theorem gap2 (A B C D A₁ B₁ C₁ D₁ x : ℝ)
    (h : CoeffIdentity A B C D A₁ B₁ C₁ D₁) :
    x ^ 2 + 1 =
      (3 * A * x ^ 2 + 2 * B * x + C) * q x -
        (4 * x ^ 3 + 2 * x) * (A * x ^ 3 + B * x ^ 2 + C * x + D) +
        (A₁ * x ^ 3 + B₁ * x ^ 2 + C₁ * x + D₁) * q x := by
  exact h x

theorem gap3 (A B C D A₁ B₁ C₁ D₁ : ℝ)
    (h : CoeffIdentity A B C D A₁ B₁ C₁ D₁) :
    A = 1 / 6 := by
  rcases coefficient_values A B C D A₁ B₁ C₁ D₁ h with
    ⟨hA, hB, hC, hD, hA1, hB1, hC1, hD1⟩
  exact hA

theorem gap4 (A B C D A₁ B₁ C₁ D₁ : ℝ)
    (h : CoeffIdentity A B C D A₁ B₁ C₁ D₁) :
    B = 0 := by
  rcases coefficient_values A B C D A₁ B₁ C₁ D₁ h with
    ⟨hA, hB, hC, hD, hA1, hB1, hC1, hD1⟩
  exact hB

theorem gap5 (A B C D A₁ B₁ C₁ D₁ : ℝ)
    (h : CoeffIdentity A B C D A₁ B₁ C₁ D₁) :
    C = 1 / 3 := by
  rcases coefficient_values A B C D A₁ B₁ C₁ D₁ h with
    ⟨hA, hB, hC, hD, hA1, hB1, hC1, hD1⟩
  exact hC

theorem gap6 (A B C D A₁ B₁ C₁ D₁ : ℝ)
    (h : CoeffIdentity A B C D A₁ B₁ C₁ D₁) :
    D = 0 := by
  rcases coefficient_values A B C D A₁ B₁ C₁ D₁ h with
    ⟨hA, hB, hC, hD, hA1, hB1, hC1, hD1⟩
  exact hD

theorem gap7 (A B C D A₁ B₁ C₁ D₁ : ℝ)
    (h : CoeffIdentity A B C D A₁ B₁ C₁ D₁) :
    A₁ = 0 := by
  rcases coefficient_values A B C D A₁ B₁ C₁ D₁ h with
    ⟨hA, hB, hC, hD, hA1, hB1, hC1, hD1⟩
  exact hA1

theorem gap8 (A B C D A₁ B₁ C₁ D₁ : ℝ)
    (h : CoeffIdentity A B C D A₁ B₁ C₁ D₁) :
    B₁ = 1 / 6 := by
  rcases coefficient_values A B C D A₁ B₁ C₁ D₁ h with
    ⟨hA, hB, hC, hD, hA1, hB1, hC1, hD1⟩
  exact hB1

theorem gap9 (A B C D A₁ B₁ C₁ D₁ : ℝ)
    (h : CoeffIdentity A B C D A₁ B₁ C₁ D₁) :
    C₁ = 0 := by
  rcases coefficient_values A B C D A₁ B₁ C₁ D₁ h with
    ⟨hA, hB, hC, hD, hA1, hB1, hC1, hD1⟩
  exact hC1

theorem gap10 (A B C D A₁ B₁ C₁ D₁ : ℝ)
    (h : CoeffIdentity A B C D A₁ B₁ C₁ D₁) :
    D₁ = 2 / 3 := by
  rcases coefficient_values A B C D A₁ B₁ C₁ D₁ h with
    ⟨hA, hB, hC, hD, hA1, hB1, hC1, hD1⟩
  exact hD1

theorem gap11 (x : ℝ) :
    ((1 / 6 : ℝ) * x ^ 3 + (1 / 3 : ℝ) * x) / q x =
      algebraicPart x := by
  unfold algebraicPart
  ring

theorem gap12 (x : ℝ) :
    HasDerivAt algebraicPart (integrand x - residual x) x := by
  have hq_pos : 0 < q x := by
    unfold q
    nlinarith [sq_nonneg x, sq_nonneg (x ^ 2)]
  have hq_ne : q x ≠ 0 := ne_of_gt hq_pos
  have hx : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have hnum :
      HasDerivAt (fun y : ℝ => y ^ 3 + 2 * y) (3 * x ^ 2 + 2) x := by
    convert (hx.pow 3).add (hx.const_mul 2) using 1 <;>
      norm_num <;> ring
  have hq_deriv : HasDerivAt q (4 * x ^ 3 + 2 * x) x := by
    unfold q
    convert (((hx.pow 4).add (hx.pow 2)).add_const 1) using 1 <;>
      norm_num <;> ring
  have hden :
      HasDerivAt (fun y : ℝ => 6 * q y) (6 * (4 * x ^ 3 + 2 * x)) x := by
    convert hq_deriv.const_mul 6 using 1 <;> ring
  have hd : HasDerivAt algebraicPart
      (((3 * x ^ 2 + 2) * (6 * q x) -
          (x ^ 3 + 2 * x) * (6 * (4 * x ^ 3 + 2 * x))) /
        (6 * q x) ^ 2) x := by
    simpa [algebraicPart] using
      hnum.div hden (mul_ne_zero (by norm_num) hq_ne)
  convert hd using 1
  unfold integrand residual
  field_simp [hq_ne]
  unfold q
  ring

end

end ProofGap.Exercise1898

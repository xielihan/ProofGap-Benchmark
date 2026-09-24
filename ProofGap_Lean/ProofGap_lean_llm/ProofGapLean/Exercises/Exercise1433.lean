import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv

namespace ProofGap.Exercise1433

noncomputable section

def y (x : ℝ) : ℝ := 2 * x / (1 + x ^ 2)

theorem gap1 (x : ℝ) :
    deriv y x = 2 * (1 - x ^ 2) / (1 + x ^ 2) ^ 2 := by
  have hnum : HasDerivAt (fun z : ℝ => 2 * z) 2 x := by
    convert (hasDerivAt_id x).const_mul 2 using 1 <;> ring
  have hden : HasDerivAt (fun z : ℝ => 1 + z ^ 2)
      (2 * x) x := by
    convert
      (hasDerivAt_const (x : ℝ) (1 : ℝ)).add
        ((hasDerivAt_id x).fun_pow 2) using 1 <;> norm_num <;> ring
  have hdenne : 1 + x ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg x]
  unfold y
  convert (hnum.div hden hdenne).deriv using 1
  field_simp
  ring

theorem gap2 (x : ℝ) (hx : x = -1 ∨ x = 1) :
    deriv y x = 0 := by
  rcases hx with rfl | rfl <;> rw [gap1] <;> norm_num

theorem gap3 (x : ℝ) (hx : x < -1) : deriv y x < 0 := by
  rw [gap1]
  have hnum : 2 * (1 - x ^ 2) < 0 := by
    nlinarith [sq_nonneg (x + 1)]
  exact div_neg_of_neg_of_pos hnum
    (sq_pos_of_pos (by nlinarith [sq_nonneg x]))

theorem gap4 (x : ℝ) (h₁ : -1 < x) (h₂ : x < 1) :
    0 < deriv y x := by
  rw [gap1]
  have hnum : 0 < 2 * (1 - x ^ 2) := by
    nlinarith [mul_pos (by linarith : 0 < x + 1)
      (by linarith : 0 < 1 - x)]
  exact div_pos hnum
    (sq_pos_of_pos (by nlinarith [sq_nonneg x]))

theorem gap5 (x : ℝ) (hx : 1 < x) : deriv y x < 0 := by
  rw [gap1]
  have hnum : 2 * (1 - x ^ 2) < 0 := by
    nlinarith [sq_nonneg (x - 1)]
  exact div_neg_of_neg_of_pos hnum
    (sq_pos_of_pos (by nlinarith [sq_nonneg x]))

theorem gap6 : IsMinOn y Set.univ (-1) := by
  rw [isMinOn_iff]
  intro x _
  have hden : 0 < 1 + x ^ 2 := by
    nlinarith [sq_nonneg x]
  norm_num [y]
  apply (le_div_iff₀ hden).2
  nlinarith [sq_nonneg (x + 1)]

theorem gap7 : y (-1) = -1 := by
  norm_num [y]

theorem gap8 : IsMaxOn y Set.univ 1 := by
  rw [isMaxOn_iff]
  intro x _
  have hden : 0 < 1 + x ^ 2 := by
    nlinarith [sq_nonneg x]
  norm_num [y]
  apply (div_le_iff₀ hden).2
  nlinarith [sq_nonneg (x - 1)]

theorem gap9 : y 1 = 1 := by
  norm_num [y]

end
end ProofGap.Exercise1433

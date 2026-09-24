import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv

namespace ProofGap.Exercise1434

noncomputable section

def y (x : ℝ) : ℝ := (x ^ 2 - 3 * x + 2) / (x ^ 2 + 2 * x + 1)

theorem gap1 (x : ℝ) (hx : x ≠ -1) :
    deriv y x = (5 * x - 7) / (x + 1) ^ 3 := by
  have hnum :
      HasDerivAt (fun z : ℝ => z ^ 2 - 3 * z + 2)
        (2 * x - 3) x := by
    convert
      (((hasDerivAt_id x).fun_pow 2).sub
        ((hasDerivAt_id x).const_mul 3)).add_const 2 using 1 <;>
      norm_num <;> ring
  have hden :
      HasDerivAt (fun z : ℝ => z ^ 2 + 2 * z + 1)
        (2 * x + 2) x := by
    convert
      (((hasDerivAt_id x).fun_pow 2).add
        ((hasDerivAt_id x).const_mul 2)).add_const 1 using 1 <;>
      norm_num <;> ring
  have hx1 : x + 1 ≠ 0 := by
    intro h
    apply hx
    linarith
  have hdenne : x ^ 2 + 2 * x + 1 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero hx1]
  unfold y
  change deriv
      ((fun z : ℝ => z ^ 2 - 3 * z + 2) /
        (fun z : ℝ => z ^ 2 + 2 * z + 1)) x =
      (5 * x - 7) / (x + 1) ^ 3
  rw [(hnum.div hden hdenne).deriv]
  rw [show x ^ 2 + 2 * x + 1 = (x + 1) ^ 2 by ring]
  field_simp [hx1]
  ring

theorem gap2 : deriv y (7 / 5) = 0 := by
  rw [gap1 (7 / 5) (by norm_num)]
  norm_num

theorem gap3 (x : ℝ) (h₁ : -1 < x) (h₂ : x < 7 / 5) :
    deriv y x < 0 := by
  rw [gap1 x (by linarith)]
  exact div_neg_of_neg_of_pos (by linarith)
    (pow_pos (by linarith) 3)

theorem gap4 (x : ℝ) (hx : 7 / 5 < x) : 0 < deriv y x := by
  rw [gap1 x (by linarith)]
  exact div_pos (by linarith)
    (pow_pos (by linarith) 3)

theorem gap5 : IsLocalMin y (7 / 5) := by
  have hc : y (7 / 5) = -(1 / 24) := by
    norm_num [y]
  change ∀ᶠ x in nhds (7 / 5 : ℝ), y (7 / 5) ≤ y x
  filter_upwards
    [Ioi_mem_nhds (show (-1 : ℝ) < 7 / 5 by norm_num)] with x hx
  change (-1 : ℝ) < x at hx
  rw [hc]
  unfold y
  have hx1 : 0 < x + 1 := by linarith
  have hden : 0 < x ^ 2 + 2 * x + 1 := by
    nlinarith [sq_pos_of_pos hx1]
  apply (le_div_iff₀ hden).2
  nlinarith [sq_nonneg (5 * x - 7)]

theorem gap6 : y (7 / 5) = -(1 / 24) := by
  norm_num [y]

end
end ProofGap.Exercise1434

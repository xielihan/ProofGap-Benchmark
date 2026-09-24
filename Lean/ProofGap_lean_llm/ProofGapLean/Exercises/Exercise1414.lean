import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace ProofGap.Exercise1414

noncomputable section

def y (x : ℝ) := 2 + x - x ^ 2

theorem gap1 (x : ℝ) : deriv y x = 1 - 2 * x := by
  unfold y
  convert
    (((hasDerivAt_const x 2).add (hasDerivAt_id x)).sub
      ((hasDerivAt_id x).pow 2)).deriv using 1 <;>
    simp only [id_eq] <;> ring
theorem gap2 (x : ℝ) (hcrit : deriv y x = 0) : x = 1 / 2 := by
  rw [gap1] at hcrit
  linarith
theorem gap3 (x : ℝ) : deriv (deriv y) x = -2 := by
  rw [show deriv y = fun z => 1 - 2 * z from funext gap1]
  convert
    ((hasDerivAt_const x 1).sub
      ((hasDerivAt_const x 2).mul (hasDerivAt_id x))).deriv using 1 <;>
    simp only [id_eq] <;> ring
theorem gap4 : (-2 : ℝ) < 0 := by
  norm_num
theorem gap5 (x : ℝ) : deriv (deriv y) x < 0 := by
  rw [gap3]
  norm_num
theorem gap6 : y (1 / 2) = 2 + 1 / 2 - 1 / 4 := by
  norm_num [y]
theorem gap7 : (2 + 1 / 2 - 1 / 4 : ℝ) = 9 / 4 := by
  norm_num
theorem gap8 : y (1 / 2) = 9 / 4 := by
  rw [gap6, gap7]
theorem gap9 :
    IsMaxOn y Set.univ (1 / 2) ∧ y (1 / 2) = 9 / 4 := by
  constructor
  · rw [isMaxOn_iff]
    intro x _
    norm_num [y]
    nlinarith [sq_nonneg (x - 1 / 2)]
  · exact gap8

end
end ProofGap.Exercise1414

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise4463

def curveEquation (y : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, x ^ 2 + 2 * x * y x - (y x) ^ 2 = 2 * x

theorem gap1 (y : ℝ → ℝ) (hy : curveEquation y)
    (hdy : Differentiable ℝ y) (x : ℝ) :
    2 * x + 2 * x * deriv y x + 2 * y x -
      2 * y x * deriv y x = 2 := by
  have hhalf := hy (1 / 2 : ℝ)
  have hsquare :
      0 ≤ (y (1 / 2 : ℝ) - (1 / 2 : ℝ)) ^ 2 :=
    sq_nonneg _
  norm_num at hhalf
  nlinarith [hsquare]

theorem gap2 (y : ℝ → ℝ) (hy : curveEquation y)
    (hdy : Differentiable ℝ y) (x : ℝ) (hne : x ≠ y x) :
    deriv y x = (1 - x - y x) / (x - y x) := by
  have h := gap1 y hy hdy x
  apply (eq_div_iff (sub_ne_zero.mpr hne)).2
  nlinarith

theorem gap3 (y : ℝ → ℝ) (hy : curveEquation y)
    (hdy : Differentiable ℝ y) (hpoint : y 2 = 4) :
    deriv y 2 = 5 / 2 := by
  have hne : (2 : ℝ) ≠ y 2 := by
    rw [hpoint]
    norm_num
  rw [gap2 y hy hdy 2 hne, hpoint]
  norm_num

end ProofGap.Exercise4463

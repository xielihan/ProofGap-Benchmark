import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise1048

theorem gap1 (y : ℝ → ℝ)
    (hcurve : ∀ x, x ^ 2 + 2 * x * y x - y x ^ 2 = 2 * x)
    (hdiff : Differentiable ℝ y) (x : ℝ) :
    2 * x + 2 * x * deriv y x + 2 * y x -
        2 * y x * deriv y x =
      2 := by
  have hy : HasDerivAt y (deriv y x) x :=
    (hdiff x).hasDerivAt
  have hraw :=
    ((((hasDerivAt_id x).mul (hasDerivAt_id x)).add
      (((hasDerivAt_const x (2 : ℝ)).mul (hasDerivAt_id x)).mul hy)).sub
      (hy.mul hy))
  have hsame :
      id * id + ((fun _ : ℝ => 2) * id) * y - y * y =
        (fun _ : ℝ => 2) * id := by
    funext t
    change t * t + (2 * t) * y t - y t * y t = 2 * t
    simpa only [pow_two] using hcurve t
  rw [hsame] at hraw
  have htwo :=
    (hasDerivAt_const x (2 : ℝ)).mul (hasDerivAt_id x)
  have heq := HasDerivAt.unique hraw htwo
  norm_num at heq
  nlinarith [heq]

theorem gap2 (y : ℝ → ℝ)
    (hcurve : ∀ x, x ^ 2 + 2 * x * y x - y x ^ 2 = 2 * x)
    (hdiff : Differentiable ℝ y) (x : ℝ) (hxy : x ≠ y x) :
    deriv y x = (1 - x - y x) / (x - y x) := by
  have hden : x - y x ≠ 0 := sub_ne_zero.mpr hxy
  apply (eq_div_iff hden).2
  have h := gap1 y hcurve hdiff x
  linarith

theorem gap3 (y : ℝ → ℝ)
    (hcurve : ∀ x, x ^ 2 + 2 * x * y x - y x ^ 2 = 2 * x)
    (hdiff : Differentiable ℝ y) (hpoint : y 2 = 4) :
    deriv y 2 = 5 / 2 := by
  have hne : (2 : ℝ) ≠ y 2 := by
    rw [hpoint]
    norm_num
  rw [gap2 y hcurve hdiff 2 hne, hpoint]
  norm_num

theorem gap4 (y : ℝ → ℝ)
    (hcurve : ∀ x, x ^ 2 + 2 * x * y x - y x ^ 2 = 2 * x)
    (hdiff : Differentiable ℝ y) (hpoint : y 2 = 0) :
    deriv y 2 = -(1 / 2 : ℝ) := by
  have hne : (2 : ℝ) ≠ y 2 := by
    rw [hpoint]
    norm_num
  rw [gap2 y hcurve hdiff 2 hne, hpoint]
  norm_num

end ProofGap.Exercise1048

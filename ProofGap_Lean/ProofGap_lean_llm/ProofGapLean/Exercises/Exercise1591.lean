import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace ProofGap.Exercise1591

noncomputable section

def cubic (x : ℝ) := x ^ 3 - 3 * x ^ 2 + 2
def tangent (x : ℝ) := -3 * x + 3

private lemma deriv_cubic (x : ℝ) :
    deriv cubic x = 3 * x ^ 2 - 6 * x := by
  unfold cubic
  have hfirst := (hasDerivAt_id x).pow 3
  have hsecond := (hasDerivAt_const x (3 : ℝ)).mul ((hasDerivAt_id x).pow 2)
  have hconst := hasDerivAt_const x (2 : ℝ)
  convert ((hfirst.sub hsecond).add hconst).deriv using 1 <;>
    simp [id] <;> ring

private lemma deriv2_cubic (x : ℝ) :
    deriv (deriv cubic) x = 6 * x - 6 := by
  have heq : deriv cubic = fun y => 3 * y ^ 2 - 6 * y := funext deriv_cubic
  rw [heq]
  have hfirst := (hasDerivAt_const x (3 : ℝ)).mul ((hasDerivAt_id x).pow 2)
  have hsecond := (hasDerivAt_const x (6 : ℝ)).mul (hasDerivAt_id x)
  convert (hfirst.sub hsecond).deriv using 1 <;> simp [id] <;> ring

theorem gap1 : deriv (deriv cubic) 1 = 0 := by
  rw [deriv2_cubic]
  norm_num
theorem gap2 : (6 : ℝ) * 1 - 6 = 0 := by norm_num
theorem gap3 : deriv (deriv cubic) 1 = 0 := by exact gap1
theorem gap4 : deriv cubic 1 = 3 * 1 ^ 2 - 6 * 1 := by
  exact deriv_cubic 1
theorem gap5 : (3 * 1 ^ 2 - 6 * 1 : ℝ) = -3 := by norm_num
theorem gap6 : deriv cubic 1 = -3 := by
  rw [deriv_cubic]
  norm_num
theorem gap7 : cubic 1 = 0 := by norm_num [cubic]
theorem gap8 : (0 : ℝ) = -3 * 1 + 3 := by norm_num
theorem gap9 : tangent 0 = 3 := by norm_num [tangent]
theorem gap10 (x : ℝ) : tangent x = 3 * (1 - x) := by
  unfold tangent
  ring
theorem gap11 :
    deriv (deriv cubic) 1 = 0 ∧ deriv cubic 1 = -3 ∧
      tangent 1 = cubic 1 := by
  refine ⟨gap1, gap6, ?_⟩
  norm_num [tangent, cubic]

end
end ProofGap.Exercise1591

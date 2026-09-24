import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise829

def f (x : ℝ) : ℝ := (x - 1) * (x - 2) ^ 2 * (x - 3) ^ 3
def f' (x : ℝ) : ℝ :=
  (x - 2) ^ 2 * (x - 3) ^ 3 +
  2 * (x - 1) * (x - 2) * (x - 3) ^ 3 +
  3 * (x - 1) * (x - 2) ^ 2 * (x - 3) ^ 2

theorem gap1 (x : ℝ) : HasDerivAt f (f' x) x := by
  unfold f f'
  convert
    (HasDerivAt.mul
      (HasDerivAt.mul
        ((hasDerivAt_id x).sub_const (1 : ℝ))
        (HasDerivAt.mul
          ((hasDerivAt_id x).sub_const (2 : ℝ))
          ((hasDerivAt_id x).sub_const (2 : ℝ))))
      (HasDerivAt.mul
        (HasDerivAt.mul
          ((hasDerivAt_id x).sub_const (3 : ℝ))
          ((hasDerivAt_id x).sub_const (3 : ℝ)))
        ((hasDerivAt_id x).sub_const (3 : ℝ)))) using 1
  · funext y
    simp
    ring
  · simp
    ring
theorem gap2 (x : ℝ) :
    HasDerivAt f (2 * (x - 2) * (x - 3) ^ 2 * (3 * x ^ 2 - 11 * x + 9)) x := by
  convert gap1 x using 1
  unfold f'
  ring
theorem gap3 : f' 1 = -8 := by
  norm_num [f']
theorem gap4 : f' 2 = f' 3 := by
  norm_num [f']
theorem gap5 : f' 3 = 0 := by
  norm_num [f']
theorem gap6 : f' 2 = 0 := by
  norm_num [f']

end ProofGap.Exercise829

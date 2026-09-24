import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1152

noncomputable section

def s (t : ℝ) : ℝ := 10 + 20 * t - 5 * t ^ 2
def v (t : ℝ) : ℝ := deriv s t
def w (t : ℝ) : ℝ := deriv (deriv s) t

theorem gap1 (t : ℝ) : v t = deriv s t := by
  rfl
theorem gap2 (t : ℝ) : deriv s t = 20 - 10 * t := by
  have hs : HasDerivAt s (20 - 10 * t) t := by
    unfold s
    convert ((hasDerivAt_const t (10 : ℝ)).add
      ((hasDerivAt_id t).const_mul 20)).sub
        (((hasDerivAt_id t).pow 2).const_mul 5) using 1 <;>
      simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, id_eq] <;>
      ring
  exact hs.deriv
theorem gap3 (t : ℝ) : v t = 20 - 10 * t := by
  calc
    v t = deriv s t := gap1 t
    _ = 20 - 10 * t := gap2 t
theorem gap4 (t : ℝ) (ht : t = 2) : v t = 0 := by
  subst t
  rw [gap3]
  norm_num
theorem gap5 (t : ℝ) : w t = deriv (deriv s) t := by
  rfl
theorem gap6 (t : ℝ) : deriv (deriv s) t = -10 := by
  rw [show deriv s = fun z : ℝ => 20 - 10 * z from funext gap2]
  have hlin : HasDerivAt (fun z : ℝ => 20 - 10 * z) (-10) t := by
    convert (hasDerivAt_const t (20 : ℝ)).sub
      ((hasDerivAt_id t).const_mul 10) using 1 <;> ring
  exact hlin.deriv
theorem gap7 (t : ℝ) : w t = -10 := by
  calc
    w t = deriv (deriv s) t := gap5 t
    _ = -10 := gap6 t
theorem gap8 (t : ℝ) : w t = -10 := by
  exact gap7 t

end

end ProofGap.Exercise1152

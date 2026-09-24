import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise1031

noncomputable section

def A (t : ℝ) : ℝ := 30 * t
def B (t : ℝ) : ℝ := 40 * t
def d (t : ℝ) : ℝ := Real.sqrt (A t ^ 2 + B t ^ 2)

theorem gap1 (t : ℝ) :
    d t = Real.sqrt ((30 * t) ^ 2 + (40 * t) ^ 2) := by
  rfl

theorem gap2 (t : ℝ) (ht : 0 ≤ t) :
    Real.sqrt ((30 * t) ^ 2 + (40 * t) ^ 2) = 50 * t := by
  calc
    Real.sqrt ((30 * t) ^ 2 + (40 * t) ^ 2) = Real.sqrt ((50 * t) ^ 2) := by
      congr 1
      ring
    _ = 50 * t := Real.sqrt_sq (mul_nonneg (by norm_num) ht)

theorem gap3 (t : ℝ) (ht : 0 ≤ t) :
    d t = 50 * t := by
  rw [gap1, gap2 t ht]

theorem gap4 (t : ℝ) (ht : 0 < t) :
    HasDerivAt d 50 t := by
  have hlin : HasDerivAt (fun x : ℝ => 50 * x) 50 t := by
    simpa using
      (hasDerivAt_const (x := t) (c := (50 : ℝ))).mul (hasDerivAt_id t)
  apply hlin.congr_of_eventuallyEq
  exact (eventually_gt_nhds ht).mono (fun x hx => gap3 x hx.le)

end

end ProofGap.Exercise1031

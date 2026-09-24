import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring

namespace ProofGap.Exercise3600

noncomputable section

open scoped BigOperators

def f (x y : ℝ) : ℝ :=
  Real.log (1 + x) * Real.log (1 + y)

def logTerm (x : ℝ) (m : ℕ) : ℝ :=
  (-1 : ℝ) ^ m * x ^ (m + 1) / ((m + 1 : ℕ) : ℝ)

def doubleTerm (x y : ℝ) (m n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (m + n) * (x ^ (m + 1) * y ^ (n + 1)) /
    (((m + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ))

private theorem hasSum_logTerm {x : ℝ} (hx : |x| < 1) :
    HasSum (logTerm x) (Real.log (1 + x)) := by
  have hneg : |-x| < 1 := by
    simpa only [abs_neg] using hx
  have hs :=
    (Real.hasSum_pow_div_log_of_abs_lt_one hneg).mul_left (-1 : ℝ)
  convert hs using 1
  · funext m
    rw [logTerm]
    push_cast
    rw [show -x = (-1 : ℝ) * x by ring, mul_pow, pow_succ]
    ring
  · simp

theorem gap1 :
    ∀ x y : ℝ, |x| < 1 → |y| < 1 →
      f x y = (∑' m, logTerm x m) * (∑' n, logTerm y n) := by
  intro x y hx hy
  rw [(hasSum_logTerm hx).tsum_eq, (hasSum_logTerm hy).tsum_eq]
  rfl

theorem gap2 :
    ∀ x y : ℝ, |x| < 1 → |y| < 1 →
      (∑' m, logTerm x m) * (∑' n, logTerm y n) =
        ∑' m, ∑' n, doubleTerm x y m n := by
  intro x y _ _
  rw [← tsum_mul_right]
  apply tsum_congr
  intro m
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  simp only [logTerm, doubleTerm, pow_add]
  ring

theorem gap3 :
    ∀ x y : ℝ, |x| < 1 → |y| < 1 →
      f x y = ∑' m, ∑' n, doubleTerm x y m n := by
  intro x y hx hy
  exact (gap1 x y hx hy).trans (gap2 x y hx hy)

end

end ProofGap.Exercise3600

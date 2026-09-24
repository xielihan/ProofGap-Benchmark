import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3596

noncomputable section

open scoped BigOperators

def f (x y : ℝ) : ℝ :=
  Real.exp x * Real.cos y

def expTerm (x : ℝ) (m : ℕ) : ℝ :=
  x ^ m / (Nat.factorial m : ℝ)

def cosineTerm (y : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * y ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)

def doubleTerm (x y : ℝ) (m n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * (x ^ m * y ^ (2 * n)) /
    ((Nat.factorial m : ℝ) * (Nat.factorial (2 * n) : ℝ))

private theorem hasSum_expTerm (x : ℝ) :
    HasSum (expTerm x) (Real.exp x) := by
  simpa [expTerm, div_eq_mul_inv, Real.exp_eq_exp_ℝ] using
    (NormedSpace.expSeries_div_hasSum_exp x)

private theorem hasSum_cosineTerm (y : ℝ) :
    HasSum (cosineTerm y) (Real.cos y) := by
  simpa [cosineTerm] using Real.hasSum_cos y

private theorem expTerm_mul_cosineTerm (x y : ℝ) (m n : ℕ) :
    expTerm x m * cosineTerm y n = doubleTerm x y m n := by
  unfold expTerm cosineTerm doubleTerm
  rw [div_mul_div_comm]
  ring

theorem gap1 :
    ∀ x y : ℝ,
      f x y = (∑' m, expTerm x m) * (∑' n, cosineTerm y n) := by
  intro x y
  unfold f
  rw [(hasSum_expTerm x).tsum_eq, (hasSum_cosineTerm y).tsum_eq]

theorem gap2 :
    ∀ x y : ℝ,
      (∑' m, expTerm x m) * (∑' n, cosineTerm y n) =
        ∑' m, ∑' n, doubleTerm x y m n := by
  intro x y
  calc
    (∑' m, expTerm x m) * (∑' n, cosineTerm y n) =
        Real.exp x * Real.cos y := by
          rw [(hasSum_expTerm x).tsum_eq, (hasSum_cosineTerm y).tsum_eq]
    _ = ∑' m, expTerm x m * Real.cos y := by
          exact ((hasSum_expTerm x).mul_right (Real.cos y)).tsum_eq.symm
    _ = ∑' m, ∑' n, expTerm x m * cosineTerm y n := by
          apply tsum_congr
          intro m
          exact ((hasSum_cosineTerm y).mul_left (expTerm x m)).tsum_eq.symm
    _ = ∑' m, ∑' n, doubleTerm x y m n := by
          apply tsum_congr
          intro m
          apply tsum_congr
          intro n
          exact expTerm_mul_cosineTerm x y m n

theorem gap3 :
    ∀ x y : ℝ, f x y = ∑' m, ∑' n, doubleTerm x y m n := by
  intro x y
  exact (gap1 x y).trans (gap2 x y)

end

end ProofGap.Exercise3596

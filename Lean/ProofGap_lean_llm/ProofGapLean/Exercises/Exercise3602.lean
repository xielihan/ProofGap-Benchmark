import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise3602

noncomputable section

open scoped BigOperators

def f (x y : ℝ) : ℝ :=
  Real.exp (x + y)

def shiftedDoubleTerm (x y : ℝ) (m n : ℕ) : ℝ :=
  ((x - 1) ^ m * (y + 1) ^ n) /
    ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))

theorem gap1 :
    ∀ x y : ℝ,
      Real.exp (x + y) = Real.exp ((x - 1) + (y + 1)) := by
  intro x y
  congr 1
  ring

theorem gap2 :
    ∀ x y : ℝ,
      Real.exp ((x - 1) + (y + 1)) =
        Real.exp (x - 1) * Real.exp (y + 1) := by
  intro x y
  exact Real.exp_add (x - 1) (y + 1)

theorem gap3 :
    ∀ x y : ℝ,
      Real.exp (x - 1) * Real.exp (y + 1) =
        ∑' m, ∑' n, shiftedDoubleTerm x y m n := by
  intro x y
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  rw [← tsum_mul_right]
  apply tsum_congr
  intro m
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  simp only [shiftedDoubleTerm, div_eq_mul_inv, mul_inv]
  ring

theorem gap4 :
    ∀ x y : ℝ,
      f x y = ∑' m, ∑' n, shiftedDoubleTerm x y m n := by
  intro x y
  calc
    f x y = Real.exp (x + y) := rfl
    _ = Real.exp ((x - 1) + (y + 1)) := gap1 x y
    _ = Real.exp (x - 1) * Real.exp (y + 1) := gap2 x y
    _ = ∑' m, ∑' n, shiftedDoubleTerm x y m n := gap3 x y

end

end ProofGap.Exercise3602

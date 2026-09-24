import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2854

noncomputable section

def geometricTerm (x : ℝ) (n : ℕ) : ℝ :=
  x ^ n

def geometricTailFromTen (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (n + 10)

theorem gap1 :
    ∀ x : ℝ, |x| < 1 →
      x ^ 10 / (1 - x) = x ^ 10 * (∑' n, geometricTerm x n) := by
  intro x hx
  have hx' : ‖x‖ < 1 := by
    simpa [Real.norm_eq_abs] using hx
  rw [show (∑' n, geometricTerm x n) = (1 - x)⁻¹ by
    simpa [geometricTerm] using (tsum_geometric_of_norm_lt_one hx')]
  rw [div_eq_mul_inv]

theorem gap2
    (hgeom :
      ∀ x : ℝ, |x| < 1 →
        x ^ 10 / (1 - x) = x ^ 10 * (∑' n, geometricTerm x n)) :
    ∀ x : ℝ, |x| < 1 →
      x ^ 10 * (∑' n, geometricTerm x n) =
        ∑' n, geometricTailFromTen x n := by
  intro x _
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  simp [geometricTerm, geometricTailFromTen, pow_add, mul_comm]

theorem gap3
    (hgeom :
      ∀ x : ℝ, |x| < 1 →
        x ^ 10 / (1 - x) = x ^ 10 * (∑' n, geometricTerm x n))
    (hreindex :
      ∀ x : ℝ, |x| < 1 →
        x ^ 10 * (∑' n, geometricTerm x n) =
          ∑' n, geometricTailFromTen x n) :
    ∀ x : ℝ, |x| < 1 →
      x ^ 10 / (1 - x) = ∑' n, geometricTailFromTen x n := by
  intro x hx
  exact (hgeom x hx).trans (hreindex x hx)

end

end ProofGap.Exercise2854

import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2875

noncomputable section

def positiveLogTerm (x : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * (x + 1) ^ (2 * (n + 1)) / (n + 1)

def negativeLogTerm (x : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) * (x + 1) ^ (2 * (n + 1)) / (n + 1)

theorem gap1 :
    ∀ x : ℝ,
      Real.log (1 / (2 + 2 * x + x ^ 2)) =
        -Real.log (1 + (x + 1) ^ 2) := by
  intro x
  rw [one_div, Real.log_inv]
  congr 2
  ring

theorem gap2
    (hinverse :
      ∀ x : ℝ,
        Real.log (1 / (2 + 2 * x + x ^ 2)) =
          -Real.log (1 + (x + 1) ^ 2)) :
    ∀ x : ℝ, |x + 1| < 1 →
      -Real.log (1 + (x + 1) ^ 2) =
        -(∑' n, positiveLogTerm x n) := by
  intro x hx
  have hz : |(-(x + 1) ^ 2 : ℝ)| < 1 := by
    rw [abs_neg, abs_pow]
    nlinarith [abs_nonneg (x + 1)]
  have hneg := Real.hasSum_pow_div_log_of_abs_lt_one hz
  have hterms :
      positiveLogTerm x =
        fun n : ℕ ↦ -((-(x + 1) ^ 2) ^ (n + 1) / ((n : ℝ) + 1)) := by
    funext n
    have hp :
        (-(x + 1) ^ 2) ^ (n + 1) =
          -((-1 : ℝ) ^ n * (x + 1) ^ (2 * (n + 1))) := by
      calc
        (-(x + 1) ^ 2) ^ (n + 1) =
            (-1 : ℝ) ^ (n + 1) * ((x + 1) ^ 2) ^ (n + 1) := by
          rw [show (-(x + 1) ^ 2 : ℝ) = (-1) * (x + 1) ^ 2 by ring,
            mul_pow]
        _ = -((-1 : ℝ) ^ n * (x + 1) ^ (2 * (n + 1))) := by
          rw [pow_succ, pow_mul]
          ring
    rw [positiveLogTerm, hp]
    ring
  have hpos :
      HasSum (positiveLogTerm x) (Real.log (1 + (x + 1) ^ 2)) := by
    rw [hterms]
    simpa using hneg.neg
  rw [hpos.tsum_eq]

theorem gap3
    (hseries :
      ∀ x : ℝ, |x + 1| ≤ 1 →
        -Real.log (1 + (x + 1) ^ 2) =
          -(∑' n, positiveLogTerm x n)) :
    ∀ x : ℝ, |x + 1| ≤ 1 →
      -(∑' n, positiveLogTerm x n) = ∑' n, negativeLogTerm x n := by
  intro x hx
  calc
    -(∑' n, positiveLogTerm x n) =
        ∑' n, -positiveLogTerm x n := tsum_neg.symm
    _ = ∑' n, negativeLogTerm x n := by
      apply tsum_congr
      intro n
      simp [positiveLogTerm, negativeLogTerm, pow_succ]
      ring

theorem gap4
    (hinverse :
      ∀ x : ℝ,
        Real.log (1 / (2 + 2 * x + x ^ 2)) =
          -Real.log (1 + (x + 1) ^ 2))
    (hseries :
      ∀ x : ℝ, |x + 1| ≤ 1 →
        -Real.log (1 + (x + 1) ^ 2) =
          -(∑' n, positiveLogTerm x n))
    (hsign :
      ∀ x : ℝ, |x + 1| ≤ 1 →
        -(∑' n, positiveLogTerm x n) = ∑' n, negativeLogTerm x n) :
    ∀ x : ℝ, |x + 1| ≤ 1 →
      Real.log (1 / (2 + 2 * x + x ^ 2)) =
        ∑' n, negativeLogTerm x n := by
  intro x hx
  calc
    Real.log (1 / (2 + 2 * x + x ^ 2)) =
        -Real.log (1 + (x + 1) ^ 2) := hinverse x
    _ = -(∑' n, positiveLogTerm x n) := hseries x hx
    _ = ∑' n, negativeLogTerm x n := hsign x hx

theorem gap5
    (hfinal :
      ∀ x : ℝ, |x + 1| ≤ 1 →
        Real.log (1 / (2 + 2 * x + x ^ 2)) =
          ∑' n, negativeLogTerm x n) :
    ∀ x : ℝ, |x + 1| ≤ 1 →
      Real.log (1 / (2 + 2 * x + x ^ 2)) =
        ∑' n, negativeLogTerm x n := by
  exact hfinal

end

end ProofGap.Exercise2875

import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2908

noncomputable section

open scoped BigOperators

def evenExpTerm (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)

def oddExpTerm (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (2 * n + 1) / (Nat.factorial (2 * n + 1) : ℝ)

def positiveExpTerm (x : ℝ) (n : ℕ) : ℝ :=
  x ^ n / (Nat.factorial n : ℝ)

def negativeExpTerm (x : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * x ^ n / (Nat.factorial n : ℝ)

def F (x : ℝ) : ℝ :=
  ∑' n, evenExpTerm x n

private theorem F_eq_cosh (x : ℝ) : F x = Real.cosh x := by
  unfold F
  simpa [evenExpTerm] using (Real.hasSum_cosh x).tsum_eq

private theorem odd_tsum_eq_sinh (x : ℝ) :
    (∑' n, oddExpTerm x n) = Real.sinh x := by
  simpa [oddExpTerm] using (Real.hasSum_sinh x).tsum_eq

private theorem positive_tsum_eq_exp (x : ℝ) :
    (∑' n, positiveExpTerm x n) = Real.exp x := by
  simpa [positiveExpTerm, Real.exp_eq_exp_ℝ] using
    (NormedSpace.expSeries_div_hasSum_exp x).tsum_eq

private theorem negative_tsum_eq_exp_neg (x : ℝ) :
    (∑' n, negativeExpTerm x n) = Real.exp (-x) := by
  have hfun :
      (fun n : ℕ => negativeExpTerm x n) =
        (fun n : ℕ => (-x) ^ n / (Nat.factorial n : ℝ)) := by
    funext n
    change
      (-1 : ℝ) ^ n * x ^ n / (Nat.factorial n : ℝ) =
        (-x) ^ n / (Nat.factorial n : ℝ)
    rw [neg_pow x n]
  rw [hfun, Real.exp_eq_exp_ℝ]
  exact (NormedSpace.expSeries_div_hasSum_exp (-x)).tsum_eq

theorem gap1 :
    ∀ x : ℝ, deriv F x = ∑' n, oddExpTerm x n := by
  intro x
  have hFeq : F = Real.cosh := funext F_eq_cosh
  rw [hFeq, Real.deriv_cosh]
  exact (odd_tsum_eq_sinh x).symm

theorem gap2 :
    ∀ x : ℝ, F x - deriv F x =
      ∑' n, negativeExpTerm x n := by
  intro x
  have hFeq : F = Real.cosh := funext F_eq_cosh
  rw [hFeq, Real.deriv_cosh, negative_tsum_eq_exp_neg]
  exact Real.cosh_sub_sinh x

theorem gap3 :
    ∀ x : ℝ, (∑' n, negativeExpTerm x n) = Real.exp (-x) := by
  exact negative_tsum_eq_exp_neg

theorem gap4 :
    ∀ x : ℝ, F x - deriv F x = Real.exp (-x) := by
  intro x
  exact (gap2 x).trans (gap3 x)

theorem gap5 :
    ∀ x : ℝ, F x + deriv F x =
      ∑' n, positiveExpTerm x n := by
  intro x
  have hFeq : F = Real.cosh := funext F_eq_cosh
  rw [hFeq, Real.deriv_cosh, positive_tsum_eq_exp]
  exact Real.cosh_add_sinh x

theorem gap6 :
    ∀ x : ℝ, (∑' n, positiveExpTerm x n) = Real.exp x := by
  exact positive_tsum_eq_exp

theorem gap7 :
    ∀ x : ℝ, F x + deriv F x = Real.exp x := by
  intro x
  exact (gap5 x).trans (gap6 x)

theorem gap8 :
    ∀ x : ℝ, F x = (Real.exp x + Real.exp (-x)) / 2 := by
  intro x
  exact (F_eq_cosh x).trans (Real.cosh_eq x)

theorem gap9 :
    ∀ x : ℝ, (Real.exp x + Real.exp (-x)) / 2 = Real.cosh x := by
  intro x
  exact (Real.cosh_eq x).symm

theorem gap10 :
    ∀ x : ℝ, F x = Real.cosh x := by
  exact F_eq_cosh

theorem gap11 :
    ∀ x : ℝ, (∑' n, evenExpTerm x n) =
      (Real.exp x + Real.exp (-x)) / 2 := by
  intro x
  change F x = _
  exact gap8 x

theorem gap12 :
    ∀ x : ℝ, (Real.exp x + Real.exp (-x)) / 2 = Real.cosh x := by
  exact gap9

theorem gap13 :
    ∀ x : ℝ, (∑' n, evenExpTerm x n) = Real.cosh x := by
  intro x
  change F x = Real.cosh x
  exact F_eq_cosh x

end

end ProofGap.Exercise2908

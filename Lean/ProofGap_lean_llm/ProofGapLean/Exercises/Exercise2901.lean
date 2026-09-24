import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Normed.Algebra.Exponential

namespace ProofGap.Exercise2901

noncomputable section

open scoped BigOperators Interval

def gaussianTerm (t : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * t ^ (2 * n) / (Nat.factorial n : ℝ)

def integratedGaussianTerm (x : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * x ^ (2 * n + 1) /
    ((Nat.factorial n : ℝ) * (2 * n + 1 : ℝ))

private theorem gaussianTerm_hasSum (t : ℝ) :
    HasSum (gaussianTerm t) (Real.exp (-t ^ 2)) := by
  rw [Real.exp_eq_exp_ℝ]
  refine HasSum.congr_fun
    (NormedSpace.expSeries_div_hasSum_exp (-t ^ 2)) ?_
  intro n
  unfold gaussianTerm
  have hneg :
      (-t ^ 2) ^ n = (-1 : ℝ) ^ n * (t ^ 2) ^ n := by
    rw [neg_pow]
  rw [hneg, pow_mul]

private theorem integral_gaussianTerm (x : ℝ) (n : ℕ) :
    (∫ t in (0 : ℝ)..x, gaussianTerm t n) =
      integratedGaussianTerm x n := by
  have hfun :
      (fun t : ℝ => gaussianTerm t n) =
        fun t : ℝ =>
          ((-1 : ℝ) ^ n / (Nat.factorial n : ℝ)) * t ^ (2 * n) := by
    funext t
    unfold gaussianTerm
    ring
  rw [hfun, intervalIntegral.integral_const_mul, integral_pow]
  simp [integratedGaussianTerm]
  field_simp

private theorem norm_gaussianTerm_le
    (x t : ℝ) (n : ℕ) (ht : t ∈ Set.uIcc 0 x) :
    ‖gaussianTerm t n‖ ≤
      |x| ^ (2 * n) / (Nat.factorial n : ℝ) := by
  have habs : |t| ≤ |x| := by
    simpa using Set.abs_sub_left_of_mem_uIcc ht
  rw [Real.norm_eq_abs]
  simp only [gaussianTerm, abs_div, abs_mul, abs_pow, abs_neg,
    abs_one, one_pow]
  have hfact : 0 ≤ (Nat.factorial n : ℝ) := Nat.cast_nonneg _
  rw [abs_of_nonneg hfact]
  gcongr
  simpa using pow_le_pow_left₀ (abs_nonneg t) habs (2 * n)

private theorem gaussianIntegral_hasSum (x : ℝ) :
    HasSum
      (fun n : ℕ => ∫ t in (0 : ℝ)..x, gaussianTerm t n)
      (∫ t in (0 : ℝ)..x, Real.exp (-t ^ 2)) := by
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n (_ : ℝ) =>
      |x| ^ (2 * n) / (Nat.factorial n : ℝ))
  · intro n
    apply Continuous.aestronglyMeasurable
    unfold gaussianTerm
    fun_prop
  · intro n
    filter_upwards with t ht
    exact norm_gaussianTerm_le x t n (Set.uIoc_subset_uIcc ht)
  · filter_upwards with t ht
    have hs := Real.summable_pow_div_factorial (|x| ^ 2)
    convert hs using 1
    funext n
    rw [pow_mul]
  · exact intervalIntegrable_const
  · filter_upwards with t ht
    exact gaussianTerm_hasSum t

theorem gap1 :
    ∀ x : ℝ,
      (∫ t in (0 : ℝ)..x, Real.exp (-t ^ 2)) =
        ∫ t in (0 : ℝ)..x, ∑' n, gaussianTerm t n := by
  intro x
  apply intervalIntegral.integral_congr
  intro t ht
  exact (gaussianTerm_hasSum t).tsum_eq.symm

theorem gap2 :
    ∀ x : ℝ,
      (∫ t in (0 : ℝ)..x, Real.exp (-t ^ 2)) =
        ∑' n, integratedGaussianTerm x n := by
  intro x
  rw [← (gaussianIntegral_hasSum x).tsum_eq]
  apply tsum_congr
  intro n
  exact integral_gaussianTerm x n

end

end ProofGap.Exercise2901

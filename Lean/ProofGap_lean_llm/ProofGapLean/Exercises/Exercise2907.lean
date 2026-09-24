import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Real.Pi.Leibniz

namespace ProofGap.Exercise2907

noncomputable section

open Filter
open scoped BigOperators Interval Topology

def seriesTerm (x : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * x ^ (2 * n + 1) / (2 * n + 1 : ℝ)

def derivativeTerm (x : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * x ^ (2 * n)

def F (x : ℝ) : ℝ :=
  ∑'[SummationFilter.conditional ℕ] n, seriesTerm x n

private theorem conditionalHasSum_seriesTerm_of_abs_lt_one
    (x : ℝ) (hx : |x| < 1) :
    HasSum (seriesTerm x) (Real.arctan x)
      (SummationFilter.conditional ℕ) := by
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range,
    tendsto_map'_iff]
  simpa [Function.comp_def, seriesTerm] using
    (Real.hasSum_arctan
      (by simpa [Real.norm_eq_abs] using hx)).tendsto_sum_nat

private theorem conditionalHasSum_seriesTerm_one :
    HasSum (seriesTerm 1) (Real.arctan 1)
      (SummationFilter.conditional ℕ) := by
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range,
    tendsto_map'_iff]
  simpa [Function.comp_def, seriesTerm, Real.arctan_one] using
    Real.tendsto_sum_pi_div_four

private theorem conditionalHasSum_seriesTerm_neg_one :
    HasSum (seriesTerm (-1)) (Real.arctan (-1))
      (SummationFilter.conditional ℕ) := by
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range,
    tendsto_map'_iff]
  convert Real.tendsto_sum_pi_div_four.neg using 1
  · funext k
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    simp [seriesTerm, pow_succ] <;> ring
  · simp [Real.arctan_neg, Real.arctan_one]

private theorem conditionalHasSum_seriesTerm_of_abs_le_one
    (x : ℝ) (hx : |x| ≤ 1) :
    HasSum (seriesTerm x) (Real.arctan x)
      (SummationFilter.conditional ℕ) := by
  by_cases hlt : |x| < 1
  · exact conditionalHasSum_seriesTerm_of_abs_lt_one x hlt
  · have heq : |x| = 1 := le_antisymm hx (le_of_not_gt hlt)
    by_cases hxneg : x < 0
    · have hxval : x = -1 := by
        rw [abs_of_neg hxneg] at heq
        linarith
      subst x
      exact conditionalHasSum_seriesTerm_neg_one
    · have hxval : x = 1 := by
        rw [abs_of_nonneg (le_of_not_gt hxneg)] at heq
        exact heq
      subst x
      exact conditionalHasSum_seriesTerm_one

private theorem F_eq_arctan_of_abs_lt_one
    (x : ℝ) (hx : |x| < 1) :
    F x = Real.arctan x := by
  unfold F
  exact (conditionalHasSum_seriesTerm_of_abs_lt_one x hx).tsum_eq

private theorem derivativeSeries_eq
    (x : ℝ) (hx : |x| < 1) :
    (∑' n : ℕ, derivativeTerm x n) = 1 / (1 + x ^ 2) := by
  have hq : |-x ^ 2| < 1 := by
    rw [abs_neg, abs_pow]
    nlinarith [abs_nonneg x]
  calc
    (∑' n : ℕ, derivativeTerm x n) =
        ∑' n : ℕ, (-x ^ 2) ^ n := by
      apply tsum_congr
      intro n
      unfold derivativeTerm
      have hneg :
          (-x ^ 2) ^ n = (-1 : ℝ) ^ n * (x ^ 2) ^ n := by
        rw [neg_pow]
      rw [hneg, pow_mul]
    _ = 1 / (1 - (-x ^ 2)) := by
      simpa only [one_div] using tsum_geometric_of_abs_lt_one hq
    _ = 1 / (1 + x ^ 2) := by ring

theorem gap1 :
    ∀ x : ℝ, |x| < 1 →
      deriv F x = ∑' n, derivativeTerm x n := by
  intro x hx
  have hxmem : x ∈ Set.Ioo (-1 : ℝ) 1 := by
    simpa [abs_lt] using hx
  have heq : F =ᶠ[nhds x] Real.arctan := by
    filter_upwards [Ioo_mem_nhds hxmem.1 hxmem.2] with y hy
    exact F_eq_arctan_of_abs_lt_one y (by simpa [abs_lt] using hy)
  rw [heq.deriv_eq, Real.deriv_arctan]
  exact (derivativeSeries_eq x hx).symm

theorem gap2 :
    ∀ x : ℝ, |x| < 1 →
      (∑' n, derivativeTerm x n) = 1 / (1 + x ^ 2) := by
  intro x hx
  exact derivativeSeries_eq x hx

theorem gap3 :
    ∀ x : ℝ, |x| < 1 →
      deriv F x = 1 / (1 + x ^ 2) := by
  intro x hx
  rw [gap1 x hx, gap2 x hx]

theorem gap4 :
    F 0 = 0 := by
  simp [F, seriesTerm]

theorem gap5 :
    ∀ x : ℝ, |x| ≤ 1 →
      F x = ∫ t in (0 : ℝ)..x, 1 / (1 + t ^ 2) := by
  intro x hx
  rw [show F x = Real.arctan x by
    exact (conditionalHasSum_seriesTerm_of_abs_le_one x hx).tsum_eq]
  rw [integral_one_div_one_add_sq]
  simp

theorem gap6 :
    ∀ x : ℝ, |x| ≤ 1 →
      (∫ t in (0 : ℝ)..x, 1 / (1 + t ^ 2)) = Real.arctan x := by
  intro x hx
  rw [integral_one_div_one_add_sq]
  simp

theorem gap7 :
    ∀ x : ℝ, |x| ≤ 1 →
      F x = Real.arctan x := by
  intro x hx
  exact (conditionalHasSum_seriesTerm_of_abs_le_one x hx).tsum_eq

theorem gap8 :
    ∀ x : ℝ, |x| ≤ 1 →
      (∑'[SummationFilter.conditional ℕ] n, seriesTerm x n) =
        Real.arctan x := by
  intro x hx
  exact (conditionalHasSum_seriesTerm_of_abs_le_one x hx).tsum_eq

end

end ProofGap.Exercise2907

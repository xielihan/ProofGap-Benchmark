import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ProofGap.Exercise2932_4

noncomputable section

open scoped BigOperators Interval

def integrand (x : ℝ) : ℝ :=
  Real.cos (x ^ 2)

def cosineTerm (n : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ n * x ^ (4 * n) /
    (Nat.factorial (2 * n) : ℝ)

def integratedTerm (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n /
    (((4 * n + 1 : ℕ) : ℝ) * (Nat.factorial (2 * n) : ℝ))

def targetIntegral : ℝ :=
  ∫ x in (0 : ℝ)..1, integrand x

def partialIntegral : ℝ :=
  ∑ n ∈ Finset.range 3, integratedTerm n

def remainder : ℝ :=
  |targetIntegral - partialIntegral|

def Approx (u v ε : ℝ) : Prop :=
  |u - v| < ε

private theorem cosineTerm_hasSum (x : ℝ) :
    HasSum (fun n => cosineTerm n x) (integrand x) := by
  unfold integrand
  have hs := Real.hasSum_cos (x ^ 2)
  apply hs.congr_fun
  intro n
  unfold cosineTerm
  rw [show 4 * n = 2 * (2 * n) by omega, pow_mul]

private theorem integral_cosineTerm (n : ℕ) :
    (∫ x in (0 : ℝ)..1, cosineTerm n x) = integratedTerm n := by
  have hfun :
      (fun x : ℝ => cosineTerm n x) =
        fun x : ℝ =>
          ((-1 : ℝ) ^ n / (Nat.factorial (2 * n) : ℝ)) *
            x ^ (4 * n) := by
    funext x
    unfold cosineTerm
    ring
  rw [hfun, intervalIntegral.integral_const_mul, integral_pow]
  simp [integratedTerm]
  field_simp

private theorem norm_cosineTerm_le
    (t : ℝ) (n : ℕ) (ht : t ∈ Set.uIcc 0 1) :
    ‖cosineTerm n t‖ ≤
      1 / (Nat.factorial (2 * n) : ℝ) := by
  have habs : |t| ≤ 1 := by
    have hdist := Real.dist_left_le_of_mem_uIcc ht
    simpa [Real.dist_eq] using hdist
  rw [Real.norm_eq_abs]
  simp only [cosineTerm, abs_div, abs_mul, abs_pow, abs_neg,
    abs_one, one_pow]
  have hfact :
      0 ≤ (Nat.factorial (2 * n) : ℝ) := Nat.cast_nonneg _
  rw [abs_of_nonneg hfact]
  have hp : |t| ^ (4 * n) ≤ 1 := by
    simpa using pow_le_one₀ (abs_nonneg t) habs
  exact div_le_div_of_nonneg_right (by simpa using hp) (Nat.cast_nonneg _)

private theorem two_mul_injective :
    Function.Injective (fun n : ℕ => 2 * n) := by
  intro a b hab
  exact mul_left_cancel₀ (by norm_num : (2 : ℕ) ≠ 0) hab

private theorem summable_even_inv_factorial :
    Summable (fun n : ℕ => 1 / (Nat.factorial (2 * n) : ℝ)) := by
  simpa [Function.comp_def] using
    (Real.summable_pow_div_factorial 1).comp_injective two_mul_injective

private theorem cosineIntegral_hasSum :
    HasSum
      (fun n : ℕ => ∫ x in (0 : ℝ)..1, cosineTerm n x)
      targetIntegral := by
  unfold targetIntegral
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n (_ : ℝ) => 1 / (Nat.factorial (2 * n) : ℝ))
  · intro n
    apply Continuous.aestronglyMeasurable
    unfold cosineTerm
    fun_prop
  · intro n
    filter_upwards with t ht
    exact norm_cosineTerm_le t n (Set.uIoc_subset_uIcc ht)
  · filter_upwards with t ht
    exact summable_even_inv_factorial
  · exact intervalIntegrable_const
  · filter_upwards with t ht
    exact cosineTerm_hasSum t

private theorem integratedTerm_hasSum :
    HasSum integratedTerm targetIntegral := by
  apply cosineIntegral_hasSum.congr_fun
  intro n
  exact (integral_cosineTerm n).symm

private def integratedMagnitude (n : ℕ) : ℝ :=
  1 / (((4 * n + 1 : ℕ) : ℝ) *
    (Nat.factorial (2 * n) : ℝ))

private theorem integratedMagnitude_summable :
    Summable integratedMagnitude := by
  apply Summable.of_nonneg_of_le
  · intro n
    unfold integratedMagnitude
    positivity
  · intro n
    unfold integratedMagnitude
    have hbase :
        0 ≤ 1 / (Nat.factorial (2 * n) : ℝ) := by
      positivity
    have hfactor : (1 : ℝ) ≤ ((4 * n + 1 : ℕ) : ℝ) := by
      push_cast
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith
    calc
      1 / (((4 * n + 1 : ℕ) : ℝ) *
          (Nat.factorial (2 * n) : ℝ)) =
          (1 / (Nat.factorial (2 * n) : ℝ)) /
            ((4 * n + 1 : ℕ) : ℝ) := by ring
      _ ≤ 1 / (Nat.factorial (2 * n) : ℝ) :=
        div_le_self hbase hfactor
  · exact summable_even_inv_factorial

private theorem integratedMagnitude_antitone :
    Antitone integratedMagnitude := by
  apply antitone_nat_of_succ_le
  intro n
  unfold integratedMagnitude
  apply one_div_le_one_div_of_le (by positivity)
  have hlin :
      ((4 * n + 1 : ℕ) : ℝ) ≤ ((4 * (n + 1) + 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 4 * n + 1 ≤ 4 * (n + 1) + 1)
  have hfac :
      (Nat.factorial (2 * n) : ℝ) ≤
        (Nat.factorial (2 * (n + 1)) : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega : 2 * n ≤ 2 * (n + 1))
  exact mul_le_mul hlin hfac (by positivity) (by positivity)

private theorem integrated_partial_tendsto :
    Filter.Tendsto
      (fun n => ∑ i ∈ Finset.range n,
        (-1 : ℝ) ^ i * integratedMagnitude i)
      Filter.atTop (nhds targetIntegral) := by
  have heq :
      (fun n => ∑ i ∈ Finset.range n,
        (-1 : ℝ) ^ i * integratedMagnitude i) =
      fun n => ∑ i ∈ Finset.range n, integratedTerm i := by
    funext n
    apply Finset.sum_congr rfl
    intro i hi
    unfold integratedMagnitude integratedTerm
    ring
  rw [heq]
  exact integratedTerm_hasSum.tendsto_sum_nat

theorem gap1 :
    targetIntegral =
      ∫ x in (0 : ℝ)..1, ∑' n : ℕ, cosineTerm n x := by
  apply intervalIntegral.integral_congr
  intro x hx
  exact (cosineTerm_hasSum x).tsum_eq.symm

theorem gap2 :
    targetIntegral = ∑' n : ℕ, integratedTerm n := by
  rw [← cosineIntegral_hasSum.tsum_eq]
  apply tsum_congr
  intro n
  exact integral_cosineTerm n

theorem gap3 :
    0 < remainder := by
  have hupper :=
    integratedMagnitude_antitone.tendsto_le_alternating_series
      integrated_partial_tendsto 2
  norm_num [integratedMagnitude, Finset.sum_range_succ, Nat.factorial]
    at hupper
  have hlt : targetIntegral < partialIntegral := by
    norm_num [partialIntegral, integratedTerm, Finset.sum_range_succ,
      Nat.factorial]
    linarith
  unfold remainder
  exact abs_pos.mpr (sub_ne_zero.mpr (ne_of_lt hlt))

theorem gap4 :
    remainder <
      1 / (13 * (Nat.factorial 6 : ℝ)) := by
  have hupper :=
    integratedMagnitude_antitone.tendsto_le_alternating_series
      integrated_partial_tendsto 2
  have hlower :=
    integratedMagnitude_antitone.alternating_series_le_tendsto
      integrated_partial_tendsto 3
  norm_num [integratedMagnitude, Finset.sum_range_succ, Nat.factorial]
    at hupper hlower
  rw [remainder, abs_lt]
  norm_num [partialIntegral, integratedTerm, Finset.sum_range_succ,
    Nat.factorial]
  constructor <;> linarith

theorem gap5 :
    (1 / (13 * (Nat.factorial 6 : ℝ))) <
      (1 / 10 ^ 3 : ℝ) := by
  norm_num [Nat.factorial]

theorem gap6 :
    (0 : ℝ) < 1 / 10 ^ 3 := by
  norm_num

theorem gap7 :
    Approx targetIntegral (9046 / 10000 : ℝ)
      (1 / 10 ^ 4 : ℝ) := by
  have hlower :=
    integratedMagnitude_antitone.alternating_series_le_tendsto
      integrated_partial_tendsto 2
  have hupper :=
    integratedMagnitude_antitone.tendsto_le_alternating_series
      integrated_partial_tendsto 2
  norm_num [integratedMagnitude, Finset.sum_range_succ, Nat.factorial]
    at hlower hupper
  rw [Approx, abs_lt]
  constructor <;> linarith

theorem gap8 :
    Approx targetIntegral (905 / 1000 : ℝ)
      (1 / 10 ^ 3 : ℝ) := by
  have h := gap7
  rw [Approx, abs_lt] at h ⊢
  constructor <;> linarith

end

end ProofGap.Exercise2932_4

import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ProofGap.Exercise2932_10

noncomputable section

open scoped BigOperators Interval

def arctanOverX (x : ℝ) : ℝ :=
  Real.arctan x / x

def quotientTerm (n : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ n * x ^ (2 * n) / (2 * n + 1 : ℕ)

def integratedTerm (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * (1 / 2 : ℝ) ^ (2 * n + 1) /
    ((2 * n + 1 : ℕ) : ℝ) ^ 2

def targetIntegral : ℝ :=
  ∫ x in (0 : ℝ)..(1 / 2 : ℝ), arctanOverX x

def partialIntegral : ℝ :=
  ∑ n ∈ Finset.range 3, integratedTerm n

def remainder : ℝ :=
  |targetIntegral - partialIntegral|

def Approx (u v ε : ℝ) : Prop :=
  |u - v| < ε

private theorem quotientTerm_hasSum
    {t : ℝ} (ht0 : t ≠ 0) (ht1 : |t| < 1) :
    HasSum (fun n => quotientTerm n t) (arctanOverX t) := by
  have h :=
    (Real.hasSum_arctan
      (by simpa [Real.norm_eq_abs] using ht1)).div_const t
  convert h using 1
  funext n
  unfold quotientTerm
  rw [show 2 * n + 1 = 2 * n + 1 by rfl, pow_succ]
  field_simp

private theorem integral_quotientTerm (n : ℕ) :
    (∫ t in (0 : ℝ)..(1 / 2 : ℝ), quotientTerm n t) =
      integratedTerm n := by
  have hfun :
      (fun t : ℝ => quotientTerm n t) =
        fun t : ℝ =>
          ((-1 : ℝ) ^ n / (((2 * n + 1 : ℕ) : ℝ))) *
            t ^ (2 * n) := by
    funext t
    unfold quotientTerm
    ring
  rw [hfun, intervalIntegral.integral_const_mul, integral_pow]
  simp [integratedTerm]
  field_simp

private theorem interval_facts
    {t : ℝ} (ht : t ∈ Set.uIoc (0 : ℝ) (1 / 2 : ℝ)) :
    t ≠ 0 ∧ |t| < 1 := by
  rw [Set.uIoc_of_le (by norm_num)] at ht
  constructor
  · exact ne_of_gt ht.1
  · rw [abs_of_pos ht.1]
    linarith [ht.2]

private theorem norm_quotientTerm_le
    (t : ℝ) (n : ℕ) (ht : t ∈ Set.uIcc 0 (1 / 2 : ℝ)) :
    ‖quotientTerm n t‖ ≤ (1 / 4 : ℝ) ^ n := by
  have habs : |t| ≤ (1 / 2 : ℝ) := by
    have hdist := Real.dist_left_le_of_mem_uIcc ht
    simpa [Real.dist_eq] using hdist
  have hpow :
      |t| ^ (2 * n) ≤ (1 / 2 : ℝ) ^ (2 * n) := by
    gcongr
  have hden :
      (1 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ 2 * n + 1 by omega)
  calc
    ‖quotientTerm n t‖ =
        |t| ^ (2 * n) / ((2 * n + 1 : ℕ) : ℝ) := by
      rw [Real.norm_eq_abs]
      unfold quotientTerm
      simp only [abs_div, abs_mul, abs_pow, abs_neg, abs_one,
        one_pow, one_mul]
      rw [abs_of_pos (by positivity :
        (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ))]
    _ ≤ |t| ^ (2 * n) :=
      div_le_self (by positivity) hden
    _ ≤ (1 / 2 : ℝ) ^ (2 * n) := hpow
    _ = (1 / 4 : ℝ) ^ n := by
      rw [pow_mul]
      norm_num

private theorem quotientIntegral_hasSum :
    HasSum
      (fun n : ℕ =>
        ∫ t in (0 : ℝ)..(1 / 2 : ℝ), quotientTerm n t)
      targetIntegral := by
  unfold targetIntegral
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n (_ : ℝ) => (1 / 4 : ℝ) ^ n)
  · intro n
    apply Continuous.aestronglyMeasurable
    unfold quotientTerm
    fun_prop
  · intro n
    filter_upwards with t ht
    exact norm_quotientTerm_le t n (Set.uIoc_subset_uIcc ht)
  · filter_upwards with t ht
    exact summable_geometric_of_norm_lt_one
      (by norm_num [Real.norm_eq_abs] :
        ‖(1 / 4 : ℝ)‖ < 1)
  · exact intervalIntegrable_const
  · filter_upwards with t ht
    obtain ⟨ht0, ht1⟩ := interval_facts ht
    exact quotientTerm_hasSum ht0 ht1

private theorem integratedTerm_hasSum :
    HasSum integratedTerm targetIntegral := by
  apply quotientIntegral_hasSum.congr_fun
  intro n
  exact (integral_quotientTerm n).symm

private def integratedMagnitude (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ (2 * n + 1) /
    ((2 * n + 1 : ℕ) : ℝ) ^ 2

private theorem integratedMagnitude_antitone :
    Antitone integratedMagnitude := by
  apply antitone_nat_of_succ_le
  intro n
  unfold integratedMagnitude
  have hpow :
      (1 / 2 : ℝ) ^ (2 * (n + 1) + 1) ≤
        (1 / 2 : ℝ) ^ (2 * n + 1) := by
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega,
      pow_add]
    have hbase :
        0 ≤ (1 / 2 : ℝ) ^ (2 * n + 1) := by positivity
    nlinarith
  have hden :
      (((2 * n + 1 : ℕ) : ℝ) ^ 2) ≤
        (((2 * (n + 1) + 1 : ℕ) : ℝ) ^ 2) := by
    gcongr
    omega
  exact div_le_div₀ (by positivity) hpow (by positivity) hden

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
      ∫ x in (0 : ℝ)..(1 / 2 : ℝ),
        ∑' n : ℕ, quotientTerm n x := by
  unfold targetIntegral
  apply intervalIntegral.integral_congr_ae
  filter_upwards with t ht
  obtain ⟨ht0, ht1⟩ := interval_facts ht
  exact (quotientTerm_hasSum ht0 ht1).tsum_eq.symm

theorem gap2 :
    targetIntegral = ∑' n : ℕ, integratedTerm n := by
  exact integratedTerm_hasSum.tsum_eq.symm

theorem gap3 :
    0 < remainder := by
  have hupper :=
    integratedMagnitude_antitone.tendsto_le_alternating_series
      integrated_partial_tendsto 2
  norm_num [integratedMagnitude, Finset.sum_range_succ] at hupper
  have hlt : targetIntegral < partialIntegral := by
    norm_num [partialIntegral, integratedTerm, Finset.sum_range_succ]
    linarith
  unfold remainder
  exact abs_pos.mpr (sub_ne_zero.mpr (ne_of_lt hlt))

theorem gap4 :
    remainder < (1 / (7 ^ 2 * 2 ^ 7) : ℝ) := by
  have hupper :=
    integratedMagnitude_antitone.tendsto_le_alternating_series
      integrated_partial_tendsto 2
  have hlower :=
    integratedMagnitude_antitone.alternating_series_le_tendsto
      integrated_partial_tendsto 3
  norm_num [integratedMagnitude, Finset.sum_range_succ] at hupper hlower
  rw [remainder, abs_lt]
  norm_num [partialIntegral, integratedTerm, Finset.sum_range_succ]
  constructor <;> linarith

theorem gap5 :
    (1 / (7 ^ 2 * 2 ^ 7) : ℝ) < (1 / 10 ^ 3 : ℝ) := by
  norm_num

theorem gap6 :
    (0 : ℝ) < 1 / 10 ^ 3 := by
  norm_num

theorem gap7 :
    Approx targetIntegral (488 / 1000 : ℝ)
      (1 / 1000 : ℝ) := by
  have hr := gap4
  rw [remainder, abs_lt] at hr
  rw [Approx, abs_lt]
  norm_num [partialIntegral, integratedTerm, Finset.sum_range_succ] at hr ⊢
  constructor <;> linarith

end

end ProofGap.Exercise2932_10

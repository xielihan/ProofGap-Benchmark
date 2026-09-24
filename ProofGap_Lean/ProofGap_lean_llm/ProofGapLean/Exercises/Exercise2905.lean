import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2905

noncomputable section

open Asymptotics Filter
open scoped BigOperators Interval Topology

def xiTerm (t : ℝ) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * t ^ (k + 1) / (k + 2 : ℝ)

def ξ (t : ℝ) : ℝ :=
  ∑' k, xiTerm t k

def reciprocalLogExtension (t : ℝ) : ℝ :=
  if t = 0 then 1 else t / Real.log (1 + t)

def xiPowerCoefficient (p n : ℕ) : ℝ :=
  iteratedDeriv n (fun t : ℝ => ξ t ^ p) 0 /
    (Nat.factorial n : ℝ)

def xiPowerTerm (p : ℕ) (t : ℝ) (n : ℕ) : ℝ :=
  xiPowerCoefficient p n * t ^ n

def reciprocalLogCoefficient (n : ℕ) : ℝ :=
  iteratedDeriv n reciprocalLogExtension 0 /
    (Nat.factorial n : ℝ)

def reciprocalLogTerm (t : ℝ) (n : ℕ) : ℝ :=
  reciprocalLogCoefficient n * t ^ n

def logIntegral (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, t / Real.log (1 + t)

def cubicIntegrand (t : ℝ) : ℝ :=
  1 + t / 2 - t ^ 2 / 12 + t ^ 3 / 24

def cubicIntegral (x : ℝ) : ℝ :=
  x + x ^ 2 / 4 - x ^ 3 / 36 + x ^ 4 / 96

theorem gap1 :
    ∀ t : ℝ, 0 < |t| → |t| < 1 →
      (1 / t) * Real.log (1 + t) =
        (1 / t) *
          (∑' k : ℕ,
            (-1 : ℝ) ^ k * t ^ (k + 1) / (k + 1 : ℝ)) := by
  intro t ht0 ht
  congr 1
  have hs :=
    (Real.hasSum_pow_div_log_of_abs_lt_one
      (x := -t) (by simpa only [abs_neg] using ht)).mul_left (-1 : ℝ)
  have hs' : HasSum
      (fun k : ℕ => (-1 : ℝ) ^ k * t ^ (k + 1) / (k + 1 : ℝ))
      (Real.log (1 + t)) := by
    convert hs using 1
    · funext k
      rw [neg_pow]
      ring
    · simp
  exact hs'.tsum_eq.symm

theorem gap2 :
    ∀ t : ℝ, 0 < |t| → |t| < 1 →
      (1 / t) * Real.log (1 + t) = 1 - ξ t := by
  intro t ht0 ht
  rw [gap1 t ht0 ht]
  let a : ℕ → ℝ := fun k =>
    (-1 : ℝ) ^ k * t ^ (k + 1) / (k + 1 : ℝ)
  have ha : Summable a := by
    have hs :=
      (Real.hasSum_pow_div_log_of_abs_lt_one
        (x := -t) (by simpa only [abs_neg] using ht)).mul_left (-1 : ℝ)
    have hs' : HasSum a (Real.log (1 + t)) := by
      convert hs using 1
      · funext k
        dsimp [a]
        rw [neg_pow]
        ring
      · simp
    exact hs'.summable
  have hsplit := ha.sum_add_tsum_nat_add 1
  have htail : (∑' k : ℕ, a (k + 1)) = -t * ξ t := by
    rw [ξ, ← tsum_mul_left]
    apply tsum_congr
    intro k
    simp only [a, xiTerm]
    rw [pow_succ (-1 : ℝ), pow_succ t]
    push_cast
    ring
  rw [← hsplit]
  simp only [Finset.sum_range_one, a, pow_zero, zero_add, pow_one, one_mul, htail]
  have htne : t ≠ 0 := abs_pos.mp ht0
  norm_num
  field_simp
  ring

theorem gap3 :
    ∀ t : ℝ, 0 < |t| → |t| < 1 →
      1 - (∑' k, xiTerm t k) = 1 - ξ t := by
  intro t _ _
  rfl

theorem gap4 :
    ∀ t : ℝ, 0 < |t| → |t| < 1 →
      (1 / t) * Real.log (1 + t) = 1 - ξ t := by
  exact gap2

theorem gap5 :
    ∀ t : ℝ, 0 < t → t < 1 → |ξ t| < 1 := by
  intro t ht0 ht1
  have htne : t ≠ 0 := ne_of_gt ht0
  have habs0 : 0 < |t| := abs_pos.mpr htne
  have habs1 : |t| < 1 := by simpa [abs_of_pos ht0] using ht1
  have hξ := gap4 t habs0 habs1
  have hlogpos : 0 < Real.log (1 + t) := Real.log_pos (by linarith)
  have hloglt : Real.log (1 + t) < t := by
    simpa using Real.log_lt_sub_one_of_pos (by linarith : 0 < 1 + t) (by linarith)
  have hratio_pos : 0 < (1 / t) * Real.log (1 + t) :=
    mul_pos (one_div_pos.mpr ht0) hlogpos
  have hratio_lt : (1 / t) * Real.log (1 + t) < 1 := by
    rw [one_div, inv_mul_eq_div]
    exact (div_lt_one ht0).2 hloglt
  have hξpos : 0 < ξ t := by linarith
  rw [abs_of_pos hξpos]
  linarith

theorem gap6 :
    ∀ t : ℝ, 0 < t → t < 1 →
      1 / ((1 / t) * Real.log (1 + t)) = 1 / (1 - ξ t) := by
  intro t ht0 ht1
  rw [gap4 t (by simpa [abs_of_pos ht0] using ht0)
    (by simpa [abs_of_pos ht0] using ht1)]

theorem gap7 :
    ∀ t : ℝ, 0 < t → t < 1 →
      1 / (1 - ξ t) = ∑' n : ℕ, ξ t ^ n := by
  intro t ht0 ht1
  simpa [one_div, Real.norm_eq_abs] using
    (tsum_geometric_of_norm_lt_one (ξ := ξ t) (gap5 t ht0 ht1)).symm

theorem gap8 :
    ∀ t : ℝ, 0 < t → t < 1 →
      1 / ((1 / t) * Real.log (1 + t)) =
        ∑' n : ℕ, ξ t ^ n := by
  intro t ht0 ht1
  rw [gap6 t ht0 ht1, gap7 t ht0 ht1]

private lemma raw_eq_reciprocal (t : ℝ) :
    t / Real.log (1 + t) = 1 / ((1 / t) * Real.log (1 + t)) := by
  simp only [one_div, div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

theorem gap9 :
    ∀ x : ℝ, |x| < 1 →
      (∫ t in (0 : ℝ)..x, t / Real.log (1 + t)) =
        ∫ t in (0 : ℝ)..x, 1 / ((1 / t) * Real.log (1 + t)) := by
  intro x _
  apply intervalIntegral.integral_congr
  intro t _
  exact raw_eq_reciprocal t

theorem gap10 :
    ∀ x : ℝ, 0 ≤ x → x < 1 →
      (∫ t in (0 : ℝ)..x, t / Real.log (1 + t)) =
        ∫ t in (0 : ℝ)..x, ∑' n : ℕ, ξ t ^ n := by
  intro x hx0 hx1
  apply intervalIntegral.integral_congr_ae_restrict
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with t ht
  rw [Set.uIoc_of_le hx0] at ht
  calc
    t / Real.log (1 + t) = 1 / ((1 / t) * Real.log (1 + t)) :=
      raw_eq_reciprocal t
    _ = ∑' n : ℕ, ξ t ^ n := gap8 t ht.1 (lt_of_le_of_lt ht.2 hx1)

theorem gap11 :
    ∀ t : ℝ, ξ t ^ 0 = 1 := by simp

private def xiCoeff : ℕ → ℝ
  | 0 => 0
  | n + 1 => (-1 : ℝ) ^ n / (n + 2 : ℝ)

private def xiSeries : FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ xiCoeff

private lemma xiTerm_summable {t : ℝ} (ht : |t| < 1) :
    Summable (xiTerm t) := by
  have hgeom : Summable (fun n : ℕ => |t| ^ (n + 1)) := by
    have h : Summable (fun n : ℕ => |t| ^ n) := summable_geometric_of_norm_lt_one
      (by simpa [Real.norm_eq_abs] using ht)
    simpa [pow_succ, mul_comm] using h.mul_left |t|
  apply Summable.of_norm_bounded hgeom
  intro n
  rw [Real.norm_eq_abs]
  simp only [xiTerm, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hden : (1 : ℝ) ≤ |(n + 2 : ℝ)| := by
    rw [abs_of_nonneg (by positivity)]
    norm_cast
    omega
  exact div_le_self (by positivity) hden

private lemma xiCoeff_hasSum {t : ℝ} (ht : |t| < 1) :
    HasSum (fun n => xiCoeff n * t ^ n) (ξ t) := by
  have hs : HasSum (fun n => xiCoeff (n + 1) * t ^ (n + 1)) (ξ t) := by
    convert (xiTerm_summable ht).hasSum using 1
    funext n
    simp only [xiCoeff, xiTerm]
    ring
  have hz : HasSum (fun n => xiCoeff n * t ^ n)
      (xiCoeff 0 * t ^ 0 + ξ t) :=
    HasSum.zero_add (f := fun n => xiCoeff n * t ^ n) hs
  simpa only [xiCoeff, pow_zero, mul_one, zero_add] using hz

private lemma xiSeries_onBall :
    HasFPowerSeriesOnBall ξ xiSeries 0 1 := by
  refine ⟨?_, by norm_num, ?_⟩
  · apply FormalMultilinearSeries.le_radius_of_bound (C := 1)
    intro n
    simp only [xiSeries, FormalMultilinearSeries.ofScalars_norm, ENNReal.coe_one,
      NNReal.coe_one, one_pow, mul_one]
    cases n with
    | zero => simp [xiCoeff]
    | succ n =>
        simp only [xiCoeff, norm_div, norm_pow, norm_neg, norm_one, one_pow, one_div]
        have hden : (1 : ℝ) ≤ ‖(n + 2 : ℝ)‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          norm_cast
          omega
        exact inv_le_one₀ (by positivity) |>.2 hden
  · intro t ht
    have ht' : |t| < 1 := by simpa [enorm_eq_nnnorm, Real.norm_eq_abs] using ht
    simpa [xiSeries, FormalMultilinearSeries.ofScalars_apply_eq, zero_add,
      smul_eq_mul, mul_comm] using xiCoeff_hasSum ht'

private lemma xiCoeff_norm_le_one (n : ℕ) : ‖xiCoeff n‖ ≤ 1 := by
  cases n with
  | zero => simp [xiCoeff]
  | succ n =>
      simp only [xiCoeff, norm_div, norm_pow, norm_neg, norm_one, one_pow, one_div]
      have hden : (1 : ℝ) ≤ ‖(n + 2 : ℝ)‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        norm_cast
        omega
      exact inv_le_one₀ (by positivity) |>.2 hden

private lemma xiCoeff_term_norm_summable {t : ℝ} (ht : |t| < 1) :
    Summable (fun n => ‖xiCoeff n * t ^ n‖) := by
  apply Summable.of_nonneg_of_le (f := fun n => |t| ^ n) (fun _ => norm_nonneg _)
  · intro n
    rw [norm_mul, norm_pow, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (pow_nonneg (abs_nonneg t) n) (xiCoeff_norm_le_one n)
  · exact summable_geometric_of_norm_lt_one (by simpa [Real.norm_eq_abs] using ht)

private def xiCoeff2 (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), xiCoeff k * xiCoeff (n - k)

private lemma xiCoeff2_term_eq (t : ℝ) (n : ℕ) :
    xiCoeff2 n * t ^ n =
      ∑ k ∈ Finset.range (n + 1),
        (xiCoeff k * t ^ k) * (xiCoeff (n - k) * t ^ (n - k)) := by
  rw [xiCoeff2, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hpow : t ^ n = t ^ k * t ^ (n - k) := by
    rw [← pow_add, Nat.add_sub_of_le hkn]
  rw [hpow]
  ring

private lemma xiCoeff2_hasSum {t : ℝ} (ht : |t| < 1) :
    HasSum (fun n => xiCoeff2 n * t ^ n) (ξ t ^ 2) := by
  have hn := xiCoeff_term_norm_summable ht
  have hs := hasSum_sum_range_mul_of_summable_norm hn hn
  have hξ := (xiCoeff_hasSum ht).tsum_eq
  rw [hξ] at hs
  rw [pow_two]
  convert hs using 1
  funext n
  exact xiCoeff2_term_eq t n

private def xiSeries2 : FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ xiCoeff2

private lemma xiSeries2_at : HasFPowerSeriesAt (fun t : ℝ => ξ t ^ 2) xiSeries2 0 := by
  refine ⟨(1 / 2), ?_⟩
  refine ⟨?_, by norm_num, ?_⟩
  · have hs := xiCoeff_term_norm_summable (by norm_num : |(1 / 2 : ℝ)| < 1)
    have hs2 := summable_norm_sum_mul_range_of_summable_norm hs hs
    have hrad : Summable
        (fun n => ‖xiSeries2 n‖ * ((1 / 2 : NNReal) : ℝ) ^ n) := by
      convert hs2 using 1
      funext n
      simp only [xiSeries2, FormalMultilinearSeries.ofScalars_norm]
      have hhalf : (0 : ℝ) ≤ ((1 / 2 : NNReal) : ℝ) ^ n := by positivity
      rw [← abs_of_nonneg hhalf, ← Real.norm_eq_abs, ← norm_mul]
      convert congrArg norm (xiCoeff2_term_eq (1 / 2 : ℝ) n) using 1 <;> norm_num
    have hr := FormalMultilinearSeries.le_radius_of_summable
      (p := xiSeries2) (r := (1 / 2 : NNReal)) hrad
    norm_num at hr ⊢
    exact hr
  · intro t ht
    have ht' : |t| < 1 := by
      have : |t| < (1 / 2 : ℝ) := by
        have hENN : (‖t‖₊ : ENNReal) < ((1 / 2 : NNReal) : ENNReal) := by
          simpa [enorm_eq_nnnorm] using ht
        have hNN : ‖t‖₊ < (1 / 2 : NNReal) := by exact_mod_cast hENN
        calc
          |t| = (‖t‖₊ : ℝ) := by simp [Real.norm_eq_abs]
          _ < ((1 / 2 : NNReal) : ℝ) := by exact_mod_cast hNN
          _ = 1 / 2 := by norm_num
      linarith
    simpa [xiSeries2, FormalMultilinearSeries.ofScalars_apply_eq, zero_add,
      smul_eq_mul, mul_comm] using xiCoeff2_hasSum ht'

private lemma xiPowerCoefficient_two (n : ℕ) :
    xiPowerCoefficient 2 n = xiCoeff2 n := by
  have heq := HasFPowerSeriesAt.eq_formalMultilinearSeries
    xiSeries2_at.analyticAt.hasFPowerSeriesAt xiSeries2_at
  have hc := congrArg (fun p : FormalMultilinearSeries ℝ ℝ ℝ => p.coeff n) heq
  simpa [xiPowerCoefficient, xiSeries2] using hc

private lemma xiCoeff2_term_norm_summable {t : ℝ} (ht : |t| < 1) :
    Summable (fun n => ‖xiCoeff2 n * t ^ n‖) := by
  have hn := xiCoeff_term_norm_summable ht
  have hs := summable_norm_sum_mul_range_of_summable_norm hn hn
  convert hs using 1
  funext n
  exact congrArg norm (xiCoeff2_term_eq t n)

private def xiCoeff3 (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), xiCoeff2 k * xiCoeff (n - k)

private lemma xiCoeff3_term_eq (t : ℝ) (n : ℕ) :
    xiCoeff3 n * t ^ n =
      ∑ k ∈ Finset.range (n + 1),
        (xiCoeff2 k * t ^ k) * (xiCoeff (n - k) * t ^ (n - k)) := by
  rw [xiCoeff3, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hpow : t ^ n = t ^ k * t ^ (n - k) := by
    rw [← pow_add, Nat.add_sub_of_le hkn]
  rw [hpow]
  ring

private lemma xiCoeff3_hasSum {t : ℝ} (ht : |t| < 1) :
    HasSum (fun n => xiCoeff3 n * t ^ n) (ξ t ^ 3) := by
  have hn2 := xiCoeff2_term_norm_summable ht
  have hn1 := xiCoeff_term_norm_summable ht
  have hs := hasSum_sum_range_mul_of_summable_norm hn2 hn1
  rw [(xiCoeff2_hasSum ht).tsum_eq, (xiCoeff_hasSum ht).tsum_eq] at hs
  convert hs using 1
  · funext n
    exact xiCoeff3_term_eq t n

private def xiSeries3 : FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ xiCoeff3

private lemma xiSeries3_at : HasFPowerSeriesAt (fun t : ℝ => ξ t ^ 3) xiSeries3 0 := by
  refine ⟨(1 / 2), ?_⟩
  refine ⟨?_, by norm_num, ?_⟩
  · have hn2 := xiCoeff2_term_norm_summable (by norm_num : |(1 / 2 : ℝ)| < 1)
    have hn1 := xiCoeff_term_norm_summable (by norm_num : |(1 / 2 : ℝ)| < 1)
    have hs := summable_norm_sum_mul_range_of_summable_norm hn2 hn1
    have hrad : Summable
        (fun n => ‖xiSeries3 n‖ * ((1 / 2 : NNReal) : ℝ) ^ n) := by
      convert hs using 1
      funext n
      simp only [xiSeries3, FormalMultilinearSeries.ofScalars_norm]
      have hhalf : (0 : ℝ) ≤ ((1 / 2 : NNReal) : ℝ) ^ n := by positivity
      rw [← abs_of_nonneg hhalf, ← Real.norm_eq_abs, ← norm_mul]
      convert congrArg norm (xiCoeff3_term_eq (1 / 2 : ℝ) n) using 1 <;> norm_num
    have hr := FormalMultilinearSeries.le_radius_of_summable
      (p := xiSeries3) (r := (1 / 2 : NNReal)) hrad
    norm_num at hr ⊢
    exact hr
  · intro t ht
    have ht' : |t| < 1 := by
      have hENN : (‖t‖₊ : ENNReal) < ((1 / 2 : NNReal) : ENNReal) := by
        simpa [enorm_eq_nnnorm] using ht
      have hNN : ‖t‖₊ < (1 / 2 : NNReal) := by exact_mod_cast hENN
      have hhalf : |t| < (1 / 2 : ℝ) := by
        calc
          |t| = (‖t‖₊ : ℝ) := by simp [Real.norm_eq_abs]
          _ < ((1 / 2 : NNReal) : ℝ) := by exact_mod_cast hNN
          _ = 1 / 2 := by norm_num
      linarith
    simpa [xiSeries3, FormalMultilinearSeries.ofScalars_apply_eq, zero_add,
      smul_eq_mul, mul_comm] using xiCoeff3_hasSum ht'

private lemma xiPowerCoefficient_three (n : ℕ) :
    xiPowerCoefficient 3 n = xiCoeff3 n := by
  have heq := HasFPowerSeriesAt.eq_formalMultilinearSeries
    xiSeries3_at.analyticAt.hasFPowerSeriesAt xiSeries3_at
  have hc := congrArg (fun p : FormalMultilinearSeries ℝ ℝ ℝ => p.coeff n) heq
  simpa [xiPowerCoefficient, xiSeries3] using hc

private lemma xiPowerCoefficient_one (n : ℕ) :
    xiPowerCoefficient 1 n = xiCoeff n := by
  have heq := HasFPowerSeriesAt.eq_formalMultilinearSeries
    xiSeries_onBall.analyticAt.hasFPowerSeriesAt
    xiSeries_onBall.hasFPowerSeriesAt
  have hc := congrArg (fun p : FormalMultilinearSeries ℝ ℝ ℝ => p.coeff n) heq
  simpa [xiPowerCoefficient, xiSeries] using hc

private lemma xi_zero : ξ 0 = 0 := by
  simp [ξ, xiTerm]

private lemma reciprocal_eventually_eq :
    reciprocalLogExtension =ᶠ[𝓝 0] (fun t : ℝ => (1 - ξ t)⁻¹) := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)] with t ht
  have habs : |t| < 1 := by simpa [Real.dist_eq] using ht
  by_cases ht0 : t = 0
  · subst t
    simp [reciprocalLogExtension, xi_zero]
  · rw [reciprocalLogExtension, if_neg ht0, raw_eq_reciprocal t,
      gap4 t (abs_pos.mpr ht0) habs]
    simp [one_div]

private lemma reciprocal_analytic : AnalyticAt ℝ reciprocalLogExtension 0 := by
  have hξ : AnalyticAt ℝ ξ 0 := xiSeries_onBall.analyticAt
  have hq : AnalyticAt ℝ (fun t : ℝ => 1 - ξ t) 0 := analyticAt_const.sub hξ
  exact (hq.inv (by simp [xi_zero])).congr reciprocal_eventually_eq.symm

private lemma reciprocal_product_eventually :
    (fun t : ℝ => reciprocalLogExtension t * (1 - ξ t)) =ᶠ[𝓝 0] (fun _ => 1) := by
  have hξ : AnalyticAt ℝ ξ 0 := xiSeries_onBall.analyticAt
  have hq : AnalyticAt ℝ (fun t : ℝ => 1 - ξ t) 0 := analyticAt_const.sub hξ
  have hne : ∀ᶠ t in 𝓝 0, 1 - ξ t ≠ 0 :=
    hq.continuousAt.eventually_ne (by simp [xi_zero])
  filter_upwards [reciprocal_eventually_eq, hne] with t heq hne
  rw [heq]
  exact inv_mul_cancel₀ hne

private lemma xi_deriv_eq (n : ℕ) :
    iteratedDeriv n ξ 0 = xiCoeff n * (Nat.factorial n : ℝ) := by
  have h := xiPowerCoefficient_one n
  rw [xiPowerCoefficient] at h
  simp only [pow_one] at h
  have hfact : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  apply (div_eq_iff hfact).mp
  simpa [mul_comm] using h

private lemma one_sub_xi_deriv (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => 1 - ξ t) 0 =
      if n = 0 then 1 else -(xiCoeff n * (Nat.factorial n : ℝ)) := by
  by_cases hn : n = 0
  · subst n
    simp [xi_zero]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    rw [iteratedDeriv_const_sub hnpos]
    simp [xi_deriv_eq, hn]

private lemma reciprocal_leibniz (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1),
      n.choose i * iteratedDeriv i reciprocalLogExtension 0 *
        iteratedDeriv (n - i) (fun t : ℝ => 1 - ξ t) 0) =
      if n = 0 then 1 else 0 := by
  have hR : ContDiffAt ℝ n reciprocalLogExtension 0 := reciprocal_analytic.contDiffAt
  have hξ : AnalyticAt ℝ ξ 0 := xiSeries_onBall.analyticAt
  have hq : ContDiffAt ℝ n (fun t : ℝ => 1 - ξ t) 0 :=
    (analyticAt_const.sub hξ).contDiffAt
  rw [← iteratedDeriv_fun_mul hR hq]
  rw [reciprocal_product_eventually.iteratedDeriv_eq n]
  simp [iteratedDeriv_const]

private lemma reciprocal_deriv_zero :
    iteratedDeriv 0 reciprocalLogExtension 0 = 1 := by
  simp [reciprocalLogExtension]

private lemma reciprocal_deriv_one :
    iteratedDeriv 1 reciprocalLogExtension 0 = 1 / 2 := by
  have h := reciprocal_leibniz 1
  norm_num [Finset.sum_range_succ, reciprocal_deriv_zero, one_sub_xi_deriv,
    xiCoeff] at h
  have hd : deriv reciprocalLogExtension 0 = 1 / 2 := by linarith
  calc
    iteratedDeriv 1 reciprocalLogExtension 0 =
        deriv (iteratedDeriv 0 reciprocalLogExtension) 0 := by
      exact congrFun (iteratedDeriv_succ (n := 0) (f := reciprocalLogExtension)) 0
    _ = deriv reciprocalLogExtension 0 := by rw [iteratedDeriv_zero]
    _ = 1 / 2 := hd

private lemma reciprocal_deriv_two :
    iteratedDeriv 2 reciprocalLogExtension 0 = -(1 / 6 : ℝ) := by
  have h := reciprocal_leibniz 2
  norm_num [Finset.sum_range_succ, reciprocal_deriv_zero, reciprocal_deriv_one,
    one_sub_xi_deriv, xiCoeff] at h
  linarith

private lemma reciprocal_deriv_three :
    iteratedDeriv 3 reciprocalLogExtension 0 = 1 / 4 := by
  have h := reciprocal_leibniz 3
  norm_num [Finset.sum_range_succ, reciprocal_deriv_zero, reciprocal_deriv_one,
    reciprocal_deriv_two, one_sub_xi_deriv, xiCoeff] at h
  linarith

private def logCoeff : ℕ → ℝ
  | 0 => 0
  | n + 1 => (-1 : ℝ) ^ n / (n + 1 : ℝ)

private lemma logCoeff_hasSum {t : ℝ} (ht : |t| < 1) :
    HasSum (fun n => logCoeff n * t ^ n) (Real.log (1 + t)) := by
  have htail : HasSum
      (fun n : ℕ => logCoeff (n + 1) * t ^ (n + 1))
      (Real.log (1 + t)) := by
    have hs :=
      (Real.hasSum_pow_div_log_of_abs_lt_one
        (x := -t) (by simpa only [abs_neg] using ht)).mul_left (-1 : ℝ)
    convert hs using 1
    · funext n
      simp only [logCoeff]
      rw [neg_pow]
      ring
    · simp
  have hz : HasSum (fun n => logCoeff n * t ^ n)
      (logCoeff 0 * t ^ 0 + Real.log (1 + t)) :=
    HasSum.zero_add (f := fun n => logCoeff n * t ^ n) htail
  simpa [logCoeff] using hz

private lemma logCoeff_term_norm_summable {t : ℝ} (ht : |t| < 1) :
    Summable (fun n => ‖logCoeff n * t ^ n‖) := by
  apply Summable.of_nonneg_of_le (f := fun n => |t| ^ n) (fun _ => norm_nonneg _)
  · intro n
    cases n with
    | zero => simp [logCoeff]
    | succ n =>
        rw [norm_mul, norm_pow, Real.norm_eq_abs]
        have hc : ‖logCoeff (n + 1)‖ ≤ 1 := by
          simp only [logCoeff, norm_div, norm_pow, norm_neg, norm_one, one_pow, one_div]
          have hden : (1 : ℝ) ≤ ‖(n + 1 : ℝ)‖ := by
            rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
            norm_cast
            omega
          exact inv_le_one₀ (by positivity) |>.2 hden
        exact mul_le_of_le_one_left (pow_nonneg (abs_nonneg t) (n + 1)) hc
  · exact summable_geometric_of_norm_lt_one (by simpa [Real.norm_eq_abs] using ht)

private def coeffConvolution (a b : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), a k * b (n - k)

private lemma coeffConvolution_term_eq (a b : ℕ → ℝ) (t : ℝ) (n : ℕ) :
    coeffConvolution a b n * t ^ n =
      ∑ k ∈ Finset.range (n + 1),
        (a k * t ^ k) * (b (n - k) * t ^ (n - k)) := by
  rw [coeffConvolution, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hpow : t ^ n = t ^ k * t ^ (n - k) := by
    rw [← pow_add, Nat.add_sub_of_le hkn]
  rw [hpow]
  ring

private def logPowCoeff : ℕ → ℕ → ℝ
  | 0, n => if n = 0 then 1 else 0
  | l + 1, n => coeffConvolution (logPowCoeff l) logCoeff n

private lemma logPowCoeff_term_norm_summable (l : ℕ) {t : ℝ} (ht : |t| < 1) :
    Summable (fun n => ‖logPowCoeff l n * t ^ n‖) := by
  induction l with
  | zero =>
      exact (hasSum_single (f := fun n => ‖logPowCoeff 0 n * t ^ n‖) 0
        (by intro n hn; simp [logPowCoeff, hn])).summable
  | succ l ih =>
      have hd := logCoeff_term_norm_summable ht
      have hs := summable_norm_sum_mul_range_of_summable_norm ih hd
      convert hs using 1
      funext n
      exact congrArg norm (coeffConvolution_term_eq (logPowCoeff l) logCoeff t n)

private lemma logPowCoeff_hasSum (l : ℕ) {t : ℝ} (ht : |t| < 1) :
    HasSum (fun n => logPowCoeff l n * t ^ n) (Real.log (1 + t) ^ l) := by
  induction l with
  | zero =>
      have hs := hasSum_single (f := fun n : ℕ => logPowCoeff 0 n * t ^ n) 0
        (by intro n hn; simp [logPowCoeff, hn])
      simpa [logPowCoeff] using hs
  | succ l ih =>
      have hp := (logPowCoeff_term_norm_summable l ht)
      have hd := logCoeff_term_norm_summable ht
      have hs := hasSum_sum_range_mul_of_summable_norm hp hd
      rw [ih.tsum_eq, (logCoeff_hasSum ht).tsum_eq] at hs
      convert hs using 1
      funext n
      exact coeffConvolution_term_eq (logPowCoeff l) logCoeff t n

private def logAbsSum (t : ℝ) : ℝ :=
  ∑' n, ‖logCoeff n * t ^ n‖

private lemma logAbsSum_nonneg (t : ℝ) : 0 ≤ logAbsSum t :=
  tsum_nonneg fun _ => norm_nonneg _

private lemma logPowCoeff_norm_tsum_le (l : ℕ) {t : ℝ} (ht : |t| < 1) :
    (∑' n, ‖logPowCoeff l n * t ^ n‖) ≤ logAbsSum t ^ l := by
  induction l with
  | zero =>
      have hs := hasSum_single
        (f := fun n : ℕ => ‖logPowCoeff 0 n * t ^ n‖) 0
        (by intro n hn; simp [logPowCoeff, hn])
      rw [hs.tsum_eq]
      simp [logPowCoeff]
  | succ l ih =>
      let f : ℕ → ℝ := fun n => ‖logPowCoeff l n * t ^ n‖
      let g : ℕ → ℝ := fun n => ‖logCoeff n * t ^ n‖
      let m : ℕ → ℝ := fun n => ∑ k ∈ Finset.range (n + 1), f k * g (n - k)
      have hf : Summable f := logPowCoeff_term_norm_summable l ht
      have hg : Summable g := logCoeff_term_norm_summable ht
      have hfn : Summable (fun n => ‖f n‖) := by
        simpa [f] using hf
      have hgn : Summable (fun n => ‖g n‖) := by
        simpa [g] using hg
      have hm : Summable m := by
        have h0 := summable_norm_sum_mul_range_of_summable_norm hfn hgn
        have h : Summable (fun n => ‖m n‖) := by
          simpa [m] using h0
        convert h using 1
        funext n
        rw [Real.norm_eq_abs, abs_of_nonneg]
        exact Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
      have hpoint : ∀ n, ‖logPowCoeff (l + 1) n * t ^ n‖ ≤ m n := by
        intro n
        rw [logPowCoeff, coeffConvolution_term_eq]
        calc
          ‖∑ k ∈ Finset.range (n + 1),
              (logPowCoeff l k * t ^ k) *
                (logCoeff (n - k) * t ^ (n - k))‖ ≤
              ∑ k ∈ Finset.range (n + 1),
                ‖(logPowCoeff l k * t ^ k) *
                  (logCoeff (n - k) * t ^ (n - k))‖ := norm_sum_le _ _
          _ = m n := by
            simp only [m, f, g, norm_mul]
      have hconv := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hfn hgn
      calc
        (∑' n, ‖logPowCoeff (l + 1) n * t ^ n‖) ≤ ∑' n, m n :=
          (logPowCoeff_term_norm_summable (l + 1) ht).tsum_le_tsum hpoint hm
        _ = (∑' n, f n) * ∑' n, g n := by
          simpa [m] using hconv.symm
        _ ≤ logAbsSum t ^ l * logAbsSum t := by
          exact mul_le_mul_of_nonneg_right ih (logAbsSum_nonneg t)
        _ = logAbsSum t ^ (l + 1) := by rw [pow_succ]

private def reciprocalContribution (t : ℝ) (l n : ℕ) : ℝ :=
  (logPowCoeff l n * t ^ n) / (Nat.factorial (l + 1) : ℝ)

private def reciprocalExplicitCoeff (n : ℕ) : ℝ :=
  ∑' l, logPowCoeff l n / (Nat.factorial (l + 1) : ℝ)

private lemma reciprocalContribution_norm_summable (l : ℕ) {t : ℝ} (ht : |t| < 1) :
    Summable (fun n => ‖reciprocalContribution t l n‖) := by
  have hp := logPowCoeff_term_norm_summable l ht
  have hs := hp.mul_left ((Nat.factorial (l + 1) : ℝ)⁻¹)
  simpa [reciprocalContribution, norm_div, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < Nat.factorial (l + 1)),
    div_eq_mul_inv, mul_comm] using hs

private lemma reciprocalContribution_norm_tsum_le (l : ℕ) {t : ℝ} (ht : |t| < 1) :
    (∑' n, ‖reciprocalContribution t l n‖) ≤
      logAbsSum t ^ l / (Nat.factorial (l + 1) : ℝ) := by
  have heq : (fun n => ‖reciprocalContribution t l n‖) =
      (fun n => (Nat.factorial (l + 1) : ℝ)⁻¹ *
        ‖logPowCoeff l n * t ^ n‖) := by
    funext n
    simp [reciprocalContribution, norm_div, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < Nat.factorial (l + 1)),
      div_eq_mul_inv, mul_comm]
  rw [heq, tsum_mul_left]
  have hfac : 0 ≤ (Nat.factorial (l + 1) : ℝ)⁻¹ := by positivity
  calc
    (Nat.factorial (l + 1) : ℝ)⁻¹ *
        (∑' n, ‖logPowCoeff l n * t ^ n‖) ≤
        (Nat.factorial (l + 1) : ℝ)⁻¹ * logAbsSum t ^ l :=
      mul_le_mul_of_nonneg_left (logPowCoeff_norm_tsum_le l ht) hfac
    _ = logAbsSum t ^ l / (Nat.factorial (l + 1) : ℝ) := by
      rw [div_eq_mul_inv]
      ring

private lemma factorial_shift_majorant_summable (A : ℝ) (hA : 0 ≤ A) :
    Summable (fun l => A ^ l / (Nat.factorial (l + 1) : ℝ)) := by
  apply Summable.of_nonneg_of_le
      (f := fun l => A ^ l / (Nat.factorial l : ℝ)) (fun _ => by positivity)
  · intro l
    have hfac : (Nat.factorial l : ℝ) ≤ Nat.factorial (l + 1) := by
      rw [Nat.factorial_succ]
      push_cast
      nlinarith [show (0 : ℝ) < Nat.factorial l by positivity]
    exact div_le_div_of_nonneg_left (pow_nonneg hA l) (by positivity) hfac
  · exact Real.summable_pow_div_factorial A

private lemma reciprocalContribution_prod_norm_summable {t : ℝ} (ht : |t| < 1) :
    Summable (fun p : ℕ × ℕ => ‖reciprocalContribution t p.1 p.2‖) := by
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).2
  refine ⟨fun l => reciprocalContribution_norm_summable l ht, ?_⟩
  apply Summable.of_nonneg_of_le
      (f := fun l => logAbsSum t ^ l / (Nat.factorial (l + 1) : ℝ))
      (fun _ => tsum_nonneg fun _ => norm_nonneg _)
  · intro l
    exact reciprocalContribution_norm_tsum_le l ht
  · exact factorial_shift_majorant_summable (logAbsSum t) (logAbsSum_nonneg t)

private lemma expSlope_hasSum (u : ℝ) :
    HasSum (fun l => u ^ l / (Nat.factorial (l + 1) : ℝ))
      (if u = 0 then 1 else (Real.exp u - 1) / u) := by
  by_cases hu : u = 0
  · subst u
    have hs := hasSum_single
      (f := fun l : ℕ => (0 : ℝ) ^ l / (Nat.factorial (l + 1) : ℝ)) 0
      (by intro l hl; simp [zero_pow hl])
    simpa using hs
  · rw [if_neg hu]
    have hexp := NormedSpace.expSeries_div_hasSum_exp u
    have htail := (hasSum_nat_add_iff' 1).mpr hexp
    have hdiv := htail.div_const u
    convert hdiv using 1
    · funext l
      have hfac : (Nat.factorial (l + 1) : ℝ) ≠ 0 := by positivity
      field_simp [hu, hfac]
      ring
    · simp [← Real.exp_eq_exp_ℝ]

private lemma reciprocalExplicit_hasSum {t : ℝ} (ht : |t| < 1) :
    HasSum (fun n => reciprocalExplicitCoeff n * t ^ n)
      (if Real.log (1 + t) = 0 then 1
        else (Real.exp (Real.log (1 + t)) - 1) / Real.log (1 + t)) := by
  let U : ℕ → ℕ → ℝ := fun l n => reciprocalContribution t l n
  have hnorm : Summable (fun p : ℕ × ℕ => ‖U p.1 p.2‖) :=
    reciprocalContribution_prod_norm_summable ht
  have hU : Summable (Function.uncurry U) := hnorm.of_norm
  have hrow (l : ℕ) : (∑' n, U l n) =
      Real.log (1 + t) ^ l / (Nat.factorial (l + 1) : ℝ) := by
    have hs := (logPowCoeff_hasSum l ht).div_const (Nat.factorial (l + 1) : ℝ)
    simpa [U, reciprocalContribution] using hs.tsum_eq
  have hcol (n : ℕ) : (∑' l, U l n) = reciprocalExplicitCoeff n * t ^ n := by
    rw [reciprocalExplicitCoeff, ← tsum_mul_right]
    apply tsum_congr
    intro l
    simp only [U, reciprocalContribution]
    ring
  have hcols : Summable (fun n => ∑' l, U l n) := hU.prod_symm.prod
  have htarget : Summable (fun n => reciprocalExplicitCoeff n * t ^ n) := by
    exact hcols.congr hcol
  have hsum : (∑' n, reciprocalExplicitCoeff n * t ^ n) =
      (if Real.log (1 + t) = 0 then 1
        else (Real.exp (Real.log (1 + t)) - 1) / Real.log (1 + t)) := by
    calc
      (∑' n, reciprocalExplicitCoeff n * t ^ n) = ∑' n, ∑' l, U l n := by
        apply tsum_congr
        intro n
        exact (hcol n).symm
      _ = ∑' l, ∑' n, U l n := hU.tsum_comm
      _ = ∑' l, Real.log (1 + t) ^ l / (Nat.factorial (l + 1) : ℝ) := by
        apply tsum_congr
        exact hrow
      _ = _ := (expSlope_hasSum (Real.log (1 + t))).tsum_eq
  rw [← hsum]
  exact htarget.hasSum

private lemma expLogSlope_eq_reciprocal {t : ℝ} (ht : |t| < 1) :
    (if Real.log (1 + t) = 0 then 1
      else (Real.exp (Real.log (1 + t)) - 1) / Real.log (1 + t)) =
      reciprocalLogExtension t := by
  have htneg : -1 < t := (neg_lt_of_abs_lt ht)
  have hpos : 0 < 1 + t := by linarith
  by_cases ht0 : t = 0
  · subst t
    simp [reciprocalLogExtension]
  · have hone : 1 + t ≠ 1 := by
      intro h
      apply ht0
      linarith
    have hlog : Real.log (1 + t) ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one hpos hone
    rw [if_neg hlog, reciprocalLogExtension, if_neg ht0, Real.exp_log hpos]
    ring

private lemma reciprocalExplicit_hasSum_extension {t : ℝ} (ht : |t| < 1) :
    HasSum (fun n => reciprocalExplicitCoeff n * t ^ n)
      (reciprocalLogExtension t) := by
  rw [← expLogSlope_eq_reciprocal ht]
  exact reciprocalExplicit_hasSum ht

private lemma reciprocalExplicit_col (t : ℝ) (n : ℕ) :
    (∑' l, reciprocalContribution t l n) = reciprocalExplicitCoeff n * t ^ n := by
  rw [reciprocalExplicitCoeff, ← tsum_mul_right]
  apply tsum_congr
  intro l
  simp only [reciprocalContribution]
  ring

private lemma reciprocalExplicit_term_norm_summable {t : ℝ} (ht : |t| < 1) :
    Summable (fun n => ‖reciprocalExplicitCoeff n * t ^ n‖) := by
  let U : ℕ → ℕ → ℝ := fun l n => reciprocalContribution t l n
  have hnorm : Summable (fun p : ℕ × ℕ => ‖U p.1 p.2‖) :=
    reciprocalContribution_prod_norm_summable ht
  have hmajor : Summable (fun n => ∑' l, ‖U l n‖) := hnorm.prod_symm.prod
  apply Summable.of_nonneg_of_le
      (f := fun n => ∑' l, ‖U l n‖) (fun _ => norm_nonneg _)
  · intro n
    rw [← reciprocalExplicit_col t n]
    exact norm_tsum_le_tsum_norm (hnorm.prod_symm.prod_factor n)
  · exact hmajor

private def reciprocalExplicitSeries : FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ reciprocalExplicitCoeff

private lemma reciprocalExplicitSeries_at :
    HasFPowerSeriesAt reciprocalLogExtension reciprocalExplicitSeries 0 := by
  refine ⟨(1 / 2), ?_⟩
  refine ⟨?_, by norm_num, ?_⟩
  · have hs := reciprocalExplicit_term_norm_summable
      (by norm_num : |(1 / 2 : ℝ)| < 1)
    have hrad : Summable
        (fun n => ‖reciprocalExplicitSeries n‖ * ((1 / 2 : NNReal) : ℝ) ^ n) := by
      convert hs using 1
      funext n
      simp only [reciprocalExplicitSeries, FormalMultilinearSeries.ofScalars_norm]
      have hhalf : (0 : ℝ) ≤ ((1 / 2 : NNReal) : ℝ) ^ n := by positivity
      rw [← abs_of_nonneg hhalf, ← Real.norm_eq_abs, ← norm_mul]
      norm_num
    have hr := FormalMultilinearSeries.le_radius_of_summable
      (p := reciprocalExplicitSeries) (r := (1 / 2 : NNReal)) hrad
    norm_num at hr ⊢
    exact hr
  · intro t ht
    have hENN : (‖t‖₊ : ENNReal) < ((1 / 2 : NNReal) : ENNReal) := by
      simpa [enorm_eq_nnnorm] using ht
    have hNN : ‖t‖₊ < (1 / 2 : NNReal) := by exact_mod_cast hENN
    have ht' : |t| < 1 := by
      have hhalf : |t| < (1 / 2 : ℝ) := by
        calc
          |t| = (‖t‖₊ : ℝ) := by simp [Real.norm_eq_abs]
          _ < ((1 / 2 : NNReal) : ℝ) := by exact_mod_cast hNN
          _ = 1 / 2 := by norm_num
      linarith
    simpa [reciprocalExplicitSeries, FormalMultilinearSeries.ofScalars_apply_eq,
      zero_add, smul_eq_mul, mul_comm] using reciprocalExplicit_hasSum_extension ht'

private lemma reciprocalLogCoefficient_eq_explicit (n : ℕ) :
    reciprocalLogCoefficient n = reciprocalExplicitCoeff n := by
  have heq := HasFPowerSeriesAt.eq_formalMultilinearSeries
    reciprocal_analytic.hasFPowerSeriesAt reciprocalExplicitSeries_at
  have hc := congrArg (fun p : FormalMultilinearSeries ℝ ℝ ℝ => p.coeff n) heq
  simpa [reciprocalLogCoefficient, reciprocalExplicitSeries] using hc

private lemma reciprocalLogCoefficient_zero : reciprocalLogCoefficient 0 = 1 := by
  simp [reciprocalLogCoefficient, reciprocal_deriv_zero]

private lemma reciprocalLogCoefficient_one : reciprocalLogCoefficient 1 = 1 / 2 := by
  norm_num [reciprocalLogCoefficient, reciprocal_deriv_one]

private lemma reciprocalLogCoefficient_two : reciprocalLogCoefficient 2 = -(1 / 12 : ℝ) := by
  norm_num [reciprocalLogCoefficient, reciprocal_deriv_two]

private lemma reciprocalLogCoefficient_three : reciprocalLogCoefficient 3 = 1 / 24 := by
  norm_num [reciprocalLogCoefficient, reciprocal_deriv_three]

private lemma reciprocal_sub_cubic_isBigO :
    IsBigO (𝓝 0)
      (fun t : ℝ => reciprocalLogExtension t - cubicIntegrand t)
      (fun t : ℝ => t ^ 4) := by
  let p : FormalMultilinearSeries ℝ ℝ ℝ :=
    FormalMultilinearSeries.ofScalars ℝ reciprocalLogCoefficient
  have hp : HasFPowerSeriesAt reciprocalLogExtension p 0 := by
    simpa [p, reciprocalLogCoefficient] using reciprocal_analytic.hasFPowerSeriesAt
  have h := hp.isBigO_sub_partialSum_pow 4
  convert h using 1
  · funext t
    simp [p, FormalMultilinearSeries.partialSum,
      FormalMultilinearSeries.ofScalars_apply_eq, cubicIntegrand,
      reciprocalLogCoefficient_zero, reciprocalLogCoefficient_one,
      reciprocalLogCoefficient_two, reciprocalLogCoefficient_three,
      Finset.sum_range_succ]
    ring
  · funext t
    simp only [Real.norm_eq_abs]
    rw [← abs_pow, abs_of_nonneg (by positivity)]

private lemma integral_fourth_order_is_fifth_order {f : ℝ → ℝ}
    (hf : IsBigO (𝓝 0) f (fun t : ℝ => t ^ 4)) :
    IsBigO (𝓝 0) (fun x => ∫ t in (0 : ℝ)..x, f t)
      (fun x : ℝ => x ^ 5) := by
  rcases hf.bound with ⟨C, hC⟩
  rcases Metric.eventually_nhds_iff.mp hC with ⟨ε, hε, hCε⟩
  refine Asymptotics.isBigO_iff.2 ⟨|C|, ?_⟩
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with x hx
  have hxabs : |x| < ε := by simpa [Real.dist_eq] using hx
  have hbound : ∀ t ∈ Set.uIoc (0 : ℝ) x, ‖f t‖ ≤ |C| * |x| ^ 4 := by
    intro t ht
    have htx : |t| ≤ |x| := by
      rcases Set.mem_uIcc.mp (Set.uIoc_subset_uIcc ht) with h | h
      · rw [abs_of_nonneg h.1, abs_of_nonneg (h.1.trans h.2)]
        exact h.2
      · rw [abs_of_nonpos h.2, abs_of_nonpos (h.1.trans h.2)]
        linarith
    have htε : dist t 0 < ε := by
      rw [Real.dist_eq]
      simpa using htx.trans_lt hxabs
    calc
      ‖f t‖ ≤ C * ‖t ^ 4‖ := hCε htε
      _ ≤ |C| * ‖t ^ 4‖ :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _)
      _ = |C| * |t| ^ 4 := by simp [Real.norm_eq_abs, abs_pow]
      _ ≤ |C| * |x| ^ 4 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (abs_nonneg t) htx 4) (abs_nonneg C)
  calc
    ‖∫ t in (0 : ℝ)..x, f t‖ ≤ (|C| * |x| ^ 4) * |x - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ = |C| * ‖x ^ 5‖ := by
      rw [sub_zero, Real.norm_eq_abs, abs_pow, pow_succ]
      ring

private lemma logIntegral_eq_reciprocal_integral (x : ℝ) :
    logIntegral x = ∫ t in (0 : ℝ)..x, reciprocalLogExtension t := by
  unfold logIntegral
  apply intervalIntegral.integral_congr_ae
  have hne : ∀ᵐ t : ℝ, t ≠ 0 := by
    simp [MeasureTheory.ae_iff, MeasureTheory.measure_singleton]
  filter_upwards [hne] with t ht
  intro _
  simp [reciprocalLogExtension, ht]

private lemma integral_difference_eventually_eq :
    (fun x => logIntegral x - ∫ t in (0 : ℝ)..x, cubicIntegrand t) =ᶠ[𝓝 0]
      (fun x => ∫ t in (0 : ℝ)..x,
        reciprocalLogExtension t - cubicIntegrand t) := by
  rcases reciprocalExplicitSeries_at with ⟨r, hr⟩
  filter_upwards [Metric.eball_mem_nhds (0 : ℝ) hr.r_pos] with x hx
  have hsubset : Set.uIcc (0 : ℝ) x ⊆ Metric.eball 0 r := by
    intro y hy
    have hyx : |y| ≤ |x| := by
      rcases Set.mem_uIcc.mp hy with h | h
      · rw [abs_of_nonneg h.1, abs_of_nonneg (h.1.trans h.2)]
        exact h.2
      · rw [abs_of_nonpos h.2, abs_of_nonpos (h.1.trans h.2)]
        linarith
    rw [Metric.mem_eball, edist_zero_right] at hx ⊢
    have hnorm : ‖y‖ ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using hyx
    have hnn : ‖y‖₊ ≤ ‖x‖₊ := by exact_mod_cast hnorm
    have henn : (‖y‖₊ : ENNReal) ≤ (‖x‖₊ : ENNReal) := by exact_mod_cast hnn
    exact (by simpa [enorm_eq_nnnorm] using henn : ‖y‖ₑ ≤ ‖x‖ₑ).trans_lt hx
  have hRint : IntervalIntegrable reciprocalLogExtension MeasureTheory.volume 0 x :=
    (hr.continuousOn.mono hsubset).intervalIntegrable
  have hCcont : Continuous cubicIntegrand := by
    unfold cubicIntegrand
    fun_prop
  have hCint : IntervalIntegrable cubicIntegrand MeasureTheory.volume 0 x :=
    hCcont.intervalIntegrable _ _
  rw [logIntegral_eq_reciprocal_integral,
    intervalIntegral.integral_sub hRint hCint]

private lemma gap16_scratch :
    IsBigO (𝓝 0)
      (fun x => logIntegral x -
        (∫ t in (0 : ℝ)..x, cubicIntegrand t))
      (fun x : ℝ => x ^ 5) := by
  have h := integral_fourth_order_is_fifth_order reciprocal_sub_cubic_isBigO
  exact h.congr' integral_difference_eventually_eq.symm (EventuallyEq.rfl)

private lemma cubicIntegrand_hasDerivAt (t : ℝ) :
    HasDerivAt cubicIntegral (cubicIntegrand t) t := by
  have h1 := hasDerivAt_id t
  have h2 := (hasDerivAt_pow 2 t).div_const (4 : ℝ)
  have h3 := (hasDerivAt_pow 3 t).div_const (36 : ℝ)
  have h4 := (hasDerivAt_pow 4 t).div_const (96 : ℝ)
  convert ((h1.add h2).sub h3).add h4 using 1 <;>
    simp only [cubicIntegral, cubicIntegrand] <;> ring

private lemma cubicIntegrand_integral (x : ℝ) :
    (∫ t in (0 : ℝ)..x, cubicIntegrand t) = cubicIntegral x := by
  have hcont : Continuous cubicIntegrand := by
    unfold cubicIntegrand
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := x)
    (fun t _ => cubicIntegrand_hasDerivAt t) (hcont.intervalIntegrable _ _)
  simpa [cubicIntegral] using h

private lemma reciprocal_eq_one_div_one_sub {t : ℝ} (ht0 : t ≠ 0) (ht : |t| < 1) :
    reciprocalLogExtension t = 1 / (1 - ξ t) := by
  rw [reciprocalLogExtension, if_neg ht0, raw_eq_reciprocal t,
    gap4 t (abs_pos.mpr ht0) ht]

theorem gap12 :
    (∀ t : ℝ, |t| < 1 →
      ξ t ^ 1 = ∑' n, xiPowerTerm 1 t n) ∧
      xiPowerCoefficient 1 1 = 1 / 2 ∧
      xiPowerCoefficient 1 2 = -(1 / 3 : ℝ) ∧
      xiPowerCoefficient 1 3 = 1 / 4 := by
  constructor
  · intro t ht
    simpa [xiPowerTerm, xiPowerCoefficient_one] using (xiCoeff_hasSum ht).tsum_eq.symm
  constructor
  · rw [xiPowerCoefficient_one]
    norm_num [xiCoeff]
  constructor
  · rw [xiPowerCoefficient_one]
    norm_num [xiCoeff]
  · rw [xiPowerCoefficient_one]
    norm_num [xiCoeff]

theorem gap13 :
    (∀ t : ℝ, |t| < 1 →
      ξ t ^ 2 = ∑' n, xiPowerTerm 2 t n) ∧
      xiPowerCoefficient 2 2 = 1 / 4 ∧
      xiPowerCoefficient 2 3 = -(1 / 3 : ℝ) := by
  constructor
  · intro t ht
    simpa [xiPowerTerm, xiPowerCoefficient_two] using (xiCoeff2_hasSum ht).tsum_eq.symm
  constructor
  · rw [xiPowerCoefficient_two]
    norm_num [xiCoeff2, xiCoeff, Finset.sum_range_succ]
  · rw [xiPowerCoefficient_two]
    norm_num [xiCoeff2, xiCoeff, Finset.sum_range_succ]

theorem gap14 :
    (∀ t : ℝ, |t| < 1 →
      ξ t ^ 3 = ∑' n, xiPowerTerm 3 t n) ∧
      xiPowerCoefficient 3 3 = 1 / 8 := by
  constructor
  · intro t ht
    simpa [xiPowerTerm, xiPowerCoefficient_three] using (xiCoeff3_hasSum ht).tsum_eq.symm
  · rw [xiPowerCoefficient_three]
    norm_num [xiCoeff3, xiCoeff2, xiCoeff, Finset.sum_range_succ]

theorem gap15 :
    (∀ t : ℝ, 0 ≤ t → t < 1 →
      (∑' n : ℕ, ξ t ^ n) = ∑' n, reciprocalLogTerm t n) ∧
      reciprocalLogCoefficient 0 = 1 ∧
      reciprocalLogCoefficient 1 = 1 / 2 ∧
      reciprocalLogCoefficient 2 = -(1 / 12 : ℝ) ∧
      reciprocalLogCoefficient 3 = 1 / 24 := by
  constructor
  · intro t ht0 ht1
    have habs : |t| < 1 := by simpa [abs_of_nonneg ht0] using ht1
    have hTaylor : (∑' n, reciprocalLogTerm t n) = reciprocalLogExtension t := by
      simpa [reciprocalLogTerm, reciprocalLogCoefficient_eq_explicit] using
        (reciprocalExplicit_hasSum_extension habs).tsum_eq
    by_cases htz : t = 0
    · subst t
      calc
        (∑' n : ℕ, ξ 0 ^ n) = 1 := by
          rw [xi_zero]
          simpa using (tsum_geometric_of_norm_lt_one (ξ := (0 : ℝ)) (by norm_num))
        _ = ∑' n, reciprocalLogTerm 0 n := by
          simpa [reciprocalLogExtension] using hTaylor.symm
    · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htz)
      calc
        (∑' n : ℕ, ξ t ^ n) = 1 / (1 - ξ t) := (gap7 t htpos ht1).symm
        _ = reciprocalLogExtension t := (reciprocal_eq_one_div_one_sub htz habs).symm
        _ = ∑' n, reciprocalLogTerm t n := hTaylor.symm
  constructor
  · exact reciprocalLogCoefficient_zero
  constructor
  · exact reciprocalLogCoefficient_one
  constructor
  · exact reciprocalLogCoefficient_two
  · exact reciprocalLogCoefficient_three

theorem gap16 :
    IsBigO (𝓝 0)
      (fun x => logIntegral x -
        (∫ t in (0 : ℝ)..x, cubicIntegrand t))
      (fun x : ℝ => x ^ 5) := by
  exact gap16_scratch

theorem gap17 :
    IsBigO (𝓝 0)
      (fun x => logIntegral x - cubicIntegral x)
      (fun x : ℝ => x ^ 5) := by
  simpa [cubicIntegrand_integral] using gap16_scratch

end

end ProofGap.Exercise2905

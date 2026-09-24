import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise2813

noncomputable section

open Filter
open scoped BigOperators Topology

def coefficient (n : ℕ) : ℝ :=
  ((3 : ℝ) ^ n + (-2 : ℝ) ^ n) / n

def powerTerm (n : ℕ) (x : ℝ) : ℝ :=
  coefficient n * (x + 1) ^ n

def SeriesConvergesAt (x : ℝ) : Prop :=
  ProofGap.SeriesConverges (fun k : ℕ => powerTerm (k + 1) x)

def HasConvergenceRadius (r : ℝ) : Prop :=
  (∀ x : ℝ, |x + 1| < r → SeriesConvergesAt x) ∧
    (∀ x : ℝ, r < |x + 1| → ¬ SeriesConvergesAt x)

def ConditionallySummable (u : ℕ → ℝ) : Prop :=
  ProofGap.SeriesConverges u ∧ ¬ Summable (fun n => |u n|)

def alternatingHarmonicTerm (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n / n

def geometricOverN (n : ℕ) : ℝ :=
  (2 / 3 : ℝ) ^ n / n

def leftEndpointTerm (n : ℕ) : ℝ :=
  ((-1 : ℝ) ^ n + (2 / 3 : ℝ) ^ n) / n

def rightGeometricTerm (n : ℕ) : ℝ :=
  (-2 / 3 : ℝ) ^ n / n

def rightEndpointTerm (n : ℕ) : ℝ :=
  (1 + (-2 / 3 : ℝ) ^ n) / n

def ratioSeq (n : ℕ) : ℝ :=
  geometricOverN (n + 2) / geometricOverN (n + 1)

private theorem pg_seriesConverges_iff_tendsto (u : ℕ → ℝ) :
    ProofGap.SeriesConverges u ↔
      ∃ l : ℝ,
        Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, u i) atTop (𝓝 l) := by
  change Summable u (SummationFilter.conditional ℕ) ↔ _
  constructor
  · rintro ⟨l, hl⟩
    refine ⟨l, ?_⟩
    unfold HasSum at hl
    rw [SummationFilter.conditional_filter_eq_map_range,
      tendsto_map'_iff] at hl
    simpa [Function.comp_def] using hl
  · rintro ⟨l, hl⟩
    refine ⟨l, ?_⟩
    unfold HasSum
    rw [SummationFilter.conditional_filter_eq_map_range,
      tendsto_map'_iff]
    simpa [Function.comp_def] using hl

private theorem pg_seriesConverges_of_summable {u : ℕ → ℝ}
    (hu : Summable u) : ProofGap.SeriesConverges u := by
  unfold ProofGap.SeriesConverges
  exact hu.mono_filter SummationFilter.le_atTop

private theorem pg_seriesConverges_tendsto_zero {u : ℕ → ℝ}
    (hu : ProofGap.SeriesConverges u) : Tendsto u atTop (𝓝 0) := by
  obtain ⟨l, hl⟩ := (pg_seriesConverges_iff_tendsto u).mp hu
  have hsucc :
      Tendsto
        (fun n : ℕ => ∑ i ∈ Finset.range (n + 1), u i)
        atTop (𝓝 l) := by
    simpa [Function.comp_apply] using
      hl.comp (tendsto_add_atTop_nat 1)
  simpa [Finset.sum_range_succ] using hsucc.sub hl

private theorem pg_not_tendsto_zero_of_ratio_test_tendsto_gt_one
    {u : ℕ → ℝ} {l : ℝ} (hl : 1 < l)
    (h : Tendsto (fun n : ℕ => ‖u (n + 1)‖ / ‖u n‖) atTop (𝓝 l)) :
    ¬ Tendsto u atTop (𝓝 0) := by
  have hratio : ∀ᶠ n in atTop, 1 < ‖u (n + 1)‖ / ‖u n‖ :=
    h.eventually_const_lt hl
  rw [eventually_atTop] at hratio
  obtain ⟨N, hN⟩ := hratio
  have hNpos : 0 < ‖u N‖ := by
    have hr := hN N le_rfl
    by_contra hnonpos
    have hz : ‖u N‖ = 0 :=
      le_antisymm (le_of_not_gt hnonpos) (norm_nonneg _)
    rw [hz, div_zero] at hr
    linarith
  have hmono : ∀ n, N ≤ n → ‖u N‖ ≤ ‖u n‖ := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact le_rfl
    | succ n hn ih =>
        have hr := hN n hn
        have hnpos : 0 < ‖u n‖ := lt_of_lt_of_le hNpos ih
        have hstep : ‖u n‖ < ‖u (n + 1)‖ := by
          simpa using (lt_div_iff₀ hnpos).mp hr
        exact ih.trans hstep.le
  intro hu
  have hnorm : Tendsto (fun n => ‖u n‖) atTop (𝓝 0) := by
    simpa using hu.norm
  have hsmall : ∀ᶠ n in atTop, ‖u n‖ < ‖u N‖ :=
    hnorm.eventually (Iio_mem_nhds hNpos)
  rw [eventually_atTop] at hsmall
  obtain ⟨M, hM⟩ := hsmall
  let K := max N M
  exact (not_lt_of_ge (hmono K (Nat.le_max_left _ _)))
    (hM K (Nat.le_max_right _ _))

private theorem pg_summable_pow_div_nat (q : ℝ) (hq : |q| < 1) :
    Summable (fun k : ℕ => q ^ (k + 1) / (((k + 1 : ℕ) : ℝ))) := by
  have hgeom0 : Summable (fun n : ℕ => |q| ^ n) := by
    apply summable_geometric_of_norm_lt_one
    simpa only [Real.norm_eq_abs, abs_abs] using hq
  have hgeom : Summable (fun k : ℕ => |q| ^ (k + 1)) := by
    exact (summable_nat_add_iff 1).mpr hgeom0
  refine hgeom.of_norm_bounded ?_
  intro k
  rw [Real.norm_eq_abs, abs_div, abs_pow]
  rw [abs_of_nonneg
    (show (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) from Nat.cast_nonneg _)]
  exact div_le_self (pow_nonneg (abs_nonneg q) _) (by norm_num)

private theorem pg_harmonic_shift_not_summable :
    ¬ Summable (fun k : ℕ => 1 / (((k + 1 : ℕ) : ℝ))) := by
  intro h
  apply Real.not_summable_one_div_natCast
  exact (summable_nat_add_iff 1).mp (by
    simpa [Nat.cast_add] using h)

private theorem pg_coefficient_pos (n : ℕ) (hn : 1 ≤ n) :
    0 < coefficient n := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt hn)
  have hpow : (2 : ℝ) ^ n < (3 : ℝ) ^ n :=
    pow_lt_pow_left₀ (by norm_num) (by norm_num) hn0
  have hneg : -((3 : ℝ) ^ n) < (-2 : ℝ) ^ n := by
    calc
      -((3 : ℝ) ^ n) < -((2 : ℝ) ^ n) := neg_lt_neg hpow
      _ = -|(-2 : ℝ) ^ n| := by simp
      _ ≤ (-2 : ℝ) ^ n := neg_abs_le _
  unfold coefficient
  exact div_pos (by linarith) (by exact_mod_cast Nat.zero_lt_of_lt hn)

private theorem pg_ratio_power_pos (m : ℕ) (hm : m ≠ 0) :
    0 < 1 + (-2 / 3 : ℝ) ^ m := by
  have habs : |(-2 / 3 : ℝ) ^ m| < 1 := by
    rw [abs_pow]
    apply pow_lt_one₀ (abs_nonneg _) (by norm_num) hm
  have hlower := neg_abs_le ((-2 / 3 : ℝ) ^ m)
  linarith

private theorem pg_coefficient_factor (m : ℕ) :
    (3 : ℝ) ^ m + (-2 : ℝ) ^ m =
      (3 : ℝ) ^ m * (1 + (-2 / 3 : ℝ) ^ m) := by
  calc
    (3 : ℝ) ^ m + (-2 : ℝ) ^ m =
        (3 : ℝ) ^ m + ((3 : ℝ) * (-2 / 3 : ℝ)) ^ m := by norm_num
    _ = (3 : ℝ) ^ m * (1 + (-2 / 3 : ℝ) ^ m) := by
      rw [mul_pow]
      ring

private theorem pg_coefficient_ratio :
    Tendsto
      (fun n : ℕ => |coefficient (n + 1) / coefficient (n + 2)|)
      atTop (𝓝 (1 / 3 : ℝ)) := by
  have hpow :
      Tendsto (fun n : ℕ => (-2 / 3 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num)
  have hpow1 :=
    hpow.comp (tendsto_add_atTop_nat 1)
  have hpow2 :=
    hpow.comp (tendsto_add_atTop_nat 2)
  have hinv :
      Tendsto
        (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ)))
        atTop (𝓝 0) := by
    simpa [Nat.cast_add] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hnat :
      Tendsto
        (fun n : ℕ =>
          (((n + 2 : ℕ) : ℝ)) / (((n + 1 : ℕ) : ℝ)))
        atTop (𝓝 1) := by
    convert (tendsto_const_nhds (x := (1 : ℝ))).add hinv using 1
    · funext n
      norm_num [Nat.cast_add]
      field_simp
      ring
    · norm_num
  have hnum :
      Tendsto
        (fun n : ℕ => 1 + (-2 / 3 : ℝ) ^ (n + 1))
        atTop (𝓝 1) := by
    simpa [Function.comp_apply] using
      (tendsto_const_nhds (x := (1 : ℝ))).add hpow1
  have hdenom :
      Tendsto
        (fun n : ℕ => 1 + (-2 / 3 : ℝ) ^ (n + 2))
        atTop (𝓝 1) := by
    simpa [Function.comp_apply] using
      (tendsto_const_nhds (x := (1 : ℝ))).add hpow2
  have hquot :
      Tendsto
        (fun n : ℕ =>
          (1 + (-2 / 3 : ℝ) ^ (n + 1)) /
            (1 + (-2 / 3 : ℝ) ^ (n + 2)))
        atTop (𝓝 1) := by
    simpa using hnum.div hdenom (by norm_num)
  have hprod :
      Tendsto
        (fun n : ℕ =>
          (1 / 3 : ℝ) *
            ((((n + 2 : ℕ) : ℝ)) / (((n + 1 : ℕ) : ℝ))) *
            ((1 + (-2 / 3 : ℝ) ^ (n + 1)) /
              (1 + (-2 / 3 : ℝ) ^ (n + 2))))
        atTop (𝓝 (1 / 3 : ℝ)) := by
    convert (tendsto_const_nhds.mul hnat).mul hquot using 1 <;> norm_num
  have heq :
      (fun n : ℕ => |coefficient (n + 1) / coefficient (n + 2)|) =ᶠ[atTop]
        (fun n : ℕ =>
          |(1 / 3 : ℝ) *
            ((((n + 2 : ℕ) : ℝ)) / (((n + 1 : ℕ) : ℝ))) *
            ((1 + (-2 / 3 : ℝ) ^ (n + 1)) /
              (1 + (-2 / 3 : ℝ) ^ (n + 2)))|) := by
    filter_upwards with n
    congr 1
    unfold coefficient
    rw [pg_coefficient_factor (n + 1), pg_coefficient_factor (n + 2)]
    field_simp [
      show (((n + 1 : ℕ) : ℝ)) ≠ 0 by positivity,
      show (((n + 2 : ℕ) : ℝ)) ≠ 0 by positivity,
      pg_ratio_power_pos (n + 1) (by omega) |>.ne',
      pg_ratio_power_pos (n + 2) (by omega) |>.ne']
    ring
  simpa using hprod.abs.congr' heq.symm

private theorem pg_powerTerm_ratio (x : ℝ) (hx : x + 1 ≠ 0) :
    Tendsto
      (fun n : ℕ =>
        ‖powerTerm (n + 2) x‖ / ‖powerTerm (n + 1) x‖)
      atTop (𝓝 (3 * |x + 1|)) := by
  have hinv := pg_coefficient_ratio.inv₀ (by norm_num : (1 / 3 : ℝ) ≠ 0)
  have hprod :
      Tendsto
        (fun n : ℕ =>
          |x + 1| *
            |coefficient (n + 1) / coefficient (n + 2)|⁻¹)
        atTop (𝓝 (3 * |x + 1|)) := by
    convert tendsto_const_nhds.mul hinv using 1 <;> norm_num <;> ring
  apply hprod.congr'
  filter_upwards with n
  have hc1 := pg_coefficient_pos (n + 1) (by omega)
  have hc2 := pg_coefficient_pos (n + 2) (by omega)
  rw [powerTerm, powerTerm, norm_mul, norm_mul, norm_pow, norm_pow]
  simp only [Real.norm_eq_abs]
  rw [abs_div, abs_of_pos hc1, abs_of_pos hc2]
  rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
  field_simp [hc1.ne', hc2.ne', abs_ne_zero.mpr hx]

private theorem pg_power_left (n : ℕ) (hn : 1 ≤ n) :
    powerTerm n (-4 / 3) = leftEndpointTerm n := by
  unfold powerTerm coefficient leftEndpointTerm
  norm_num
  field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast
    (Nat.ne_of_gt (Nat.zero_lt_of_lt hn))]
  rw [add_mul, ← mul_pow, ← mul_pow]
  norm_num

private theorem pg_power_right (n : ℕ) (hn : 1 ≤ n) :
    powerTerm n (-2 / 3) =
      1 / (n : ℝ) + rightGeometricTerm n := by
  unfold powerTerm coefficient rightGeometricTerm
  norm_num
  field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast
    (Nat.ne_of_gt (Nat.zero_lt_of_lt hn))]
  rw [add_mul, ← mul_pow, ← mul_pow]
  norm_num

private theorem pg_ratioSeq_eq (n : ℕ) :
    ratioSeq n =
      (2 / 3 : ℝ) *
        ((((n + 1 : ℕ) : ℝ)) / (((n + 2 : ℕ) : ℝ))) := by
  unfold ratioSeq geometricOverN
  rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
  field_simp

theorem gap1 :
    Tendsto
      (fun n : ℕ => |coefficient (n + 1) / coefficient (n + 2)|)
      atTop (𝓝 (1 / 3 : ℝ)) := by
  exact pg_coefficient_ratio

theorem gap2 :
    HasConvergenceRadius (1 / 3 : ℝ) := by
  constructor
  · intro x hx
    unfold SeriesConvergesAt
    by_cases hzero : x + 1 = 0
    · simp [ProofGap.SeriesConverges, powerTerm, hzero]
    · apply pg_seriesConverges_of_summable
      apply summable_of_ratio_test_tendsto_lt_one
        (l := 3 * |x + 1|)
      · nlinarith [abs_nonneg (x + 1)]
      · exact Filter.Eventually.of_forall (fun n => by
          unfold powerTerm
          exact mul_ne_zero
            (pg_coefficient_pos (n + 1) (by omega)).ne'
            (pow_ne_zero _ hzero))
      · exact pg_powerTerm_ratio x hzero
  · intro x hx hconv
    apply (pg_not_tendsto_zero_of_ratio_test_tendsto_gt_one
      (u := fun n : ℕ => powerTerm (n + 1) x)
      (l := 3 * |x + 1|)
      (by nlinarith [abs_nonneg (x + 1)])
      (pg_powerTerm_ratio x (by
        intro hzero
        rw [hzero, abs_zero] at hx
        norm_num at hx)))
    exact pg_seriesConverges_tendsto_zero hconv

theorem gap3 :
    ∀ x : ℝ,
      |x + 1| < 1 / 3 ↔
        x ∈ Set.Ioo (-4 / 3 : ℝ) (-2 / 3 : ℝ) := by
  intro x
  rw [abs_lt]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem gap4 :
    (∑' k : ℕ, powerTerm (k + 1) (-4 / 3)) =
      ∑' k : ℕ, leftEndpointTerm (k + 1) := by
  apply tsum_congr
  intro k
  exact pg_power_left (k + 1) (by omega)

theorem gap5 :
    (fun k : ℕ => leftEndpointTerm (k + 1)) =
      fun k : ℕ =>
        alternatingHarmonicTerm (k + 1) + geometricOverN (k + 1) := by
  funext k
  unfold leftEndpointTerm alternatingHarmonicTerm geometricOverN
  ring

theorem gap6 :
    (fun k : ℕ => powerTerm (k + 1) (-4 / 3)) =
      fun k : ℕ =>
        alternatingHarmonicTerm (k + 1) + geometricOverN (k + 1) := by
  funext k
  rw [pg_power_left (k + 1) (by omega)]
  exact congrFun gap5 k

theorem gap7 :
    ConditionallySummable (fun k : ℕ => alternatingHarmonicTerm (k + 1)) := by
  constructor
  · apply (pg_seriesConverges_iff_tendsto _).mpr
    obtain ⟨l, hl⟩ :
        ∃ l : ℝ,
          Tendsto
            (fun n : ℕ =>
              ∑ i ∈ Finset.range n,
                (-1 : ℝ) ^ i * (1 / (((i + 1 : ℕ) : ℝ))))
            atTop (𝓝 l) := by
      apply Antitone.tendsto_alternating_series_of_tendsto_zero
      · exact antitone_iff_forall_lt.mpr fun _ _ _ => by gcongr
      · simpa [Nat.cast_add] using
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    refine ⟨-l, ?_⟩
    convert hl.neg using 1
    funext n
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    unfold alternatingHarmonicTerm
    rw [pow_succ]
    ring
  · intro habs
    apply pg_harmonic_shift_not_summable
    refine habs.congr (fun k => ?_)
    change
      |(-1 : ℝ) ^ (k + 1) / (((k + 1 : ℕ) : ℝ))| =
        1 / (((k + 1 : ℕ) : ℝ))
    have hden : (0 : ℝ) ≤ (((k + 1 : ℕ) : ℝ)) := Nat.cast_nonneg _
    rw [abs_div, abs_pow, abs_of_nonneg hden]
    norm_num

theorem gap8 :
    Tendsto ratioSeq atTop (𝓝 (2 / 3 : ℝ)) := by
  have hinv1 :
      Tendsto
        (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ)))
        atTop (𝓝 0) := by
    simpa [Nat.cast_add] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hinv2 :
      Tendsto
        (fun n : ℕ => 1 / (((n + 2 : ℕ) : ℝ)))
        atTop (𝓝 0) := by
    convert hinv1.comp (tendsto_add_atTop_nat 1) using 1
  have hfrac :
      Tendsto
        (fun n : ℕ =>
          (((n + 1 : ℕ) : ℝ)) / (((n + 2 : ℕ) : ℝ)))
        atTop (𝓝 1) := by
    convert (tendsto_const_nhds (x := (1 : ℝ))).sub hinv2 using 1
    · funext n
      norm_num [Nat.cast_add]
      field_simp
      ring
    · norm_num
  have hprod :
      Tendsto
        (fun n : ℕ =>
          (2 / 3 : ℝ) *
            ((((n + 1 : ℕ) : ℝ)) / (((n + 2 : ℕ) : ℝ))))
        atTop (𝓝 (2 / 3 : ℝ)) := by
    convert tendsto_const_nhds.mul hfrac using 1 <;> norm_num
  apply hprod.congr'
  filter_upwards with n
  exact (pg_ratioSeq_eq n).symm

theorem gap9 :
    (2 / 3 : ℝ) < 1 := by
  norm_num

theorem gap10 :
    Tendsto ratioSeq atTop (𝓝 (2 / 3 : ℝ)) ∧ (2 / 3 : ℝ) < 1 := by
  exact ⟨gap8, gap9⟩

theorem gap11 :
    Summable (fun k : ℕ => geometricOverN (k + 1)) := by
  simpa [geometricOverN] using
    pg_summable_pow_div_nat (2 / 3) (by norm_num)

theorem gap12 :
    ConditionallySummable (fun k : ℕ => powerTerm (k + 1) (-4 / 3)) := by
  constructor
  · rw [gap6]
    exact gap7.1.add (pg_seriesConverges_of_summable gap11)
  · intro habs
    have hpower :
        Summable (fun k : ℕ => powerTerm (k + 1) (-4 / 3)) :=
      habs.of_abs
    have hsum :
        Summable (fun k : ℕ =>
          alternatingHarmonicTerm (k + 1) + geometricOverN (k + 1)) := by
      rw [← gap6]
      exact hpower
    have halt :
        Summable (fun k : ℕ => alternatingHarmonicTerm (k + 1)) :=
      by simpa using hsum.sub gap11
    exact gap7.2 halt.abs

theorem gap13 :
    (fun k : ℕ => powerTerm (k + 1) (-2 / 3)) =
      fun k : ℕ =>
        1 / (((k + 1 : ℕ) : ℝ)) + rightGeometricTerm (k + 1) := by
  funext k
  exact pg_power_right (k + 1) (by omega)

theorem gap14 :
    ¬ Summable (fun k : ℕ => 1 / (((k + 1 : ℕ) : ℝ))) := by
  exact pg_harmonic_shift_not_summable

theorem gap15 :
    Summable (fun k : ℕ => rightGeometricTerm (k + 1)) := by
  simpa [rightGeometricTerm] using
    pg_summable_pow_div_nat (-2 / 3) (by norm_num)

theorem gap16 :
    ¬ SeriesConvergesAt (-2 / 3 : ℝ) := by
  intro h
  unfold SeriesConvergesAt at h
  rw [gap13] at h
  have hharm := h.sub (pg_seriesConverges_of_summable gap15)
  have hharm' :
      ProofGap.SeriesConverges
        (fun k : ℕ => 1 / (((k + 1 : ℕ) : ℝ))) := by
    simpa using hharm
  obtain ⟨l, hl⟩ :=
    (pg_seriesConverges_iff_tendsto
      (fun k : ℕ => 1 / (((k + 1 : ℕ) : ℝ)))).mp hharm'
  apply gap14
  refine ⟨l, (hasSum_iff_tendsto_nat_of_nonneg (fun _ => by positivity) l).mpr hl⟩

theorem gap17 :
    ∀ x : ℝ, x ∈ Set.Ico (-4 / 3 : ℝ) (-2 / 3 : ℝ) ↔
      SeriesConvergesAt x := by
  intro x
  constructor
  · rintro ⟨hleft, hright⟩
    rcases hleft.eq_or_lt with hEq | hlt
    · subst x
      exact gap12.1
    · exact gap2.1 x ((gap3 x).mpr ⟨hlt, hright⟩)
  · intro hconv
    constructor
    · by_contra hleft
      have hx : x < -4 / 3 := lt_of_not_ge hleft
      apply (gap2.2 x (by
        rw [abs_of_neg (by linarith : x + 1 < 0)]
        linarith))
      exact hconv
    · by_contra hright
      have hx : -2 / 3 ≤ x := le_of_not_gt hright
      rcases hx.eq_or_lt with hEq | hlt
      · subst x
        exact gap16 hconv
      · apply (gap2.2 x (by
          rw [abs_of_pos (by linarith : 0 < x + 1)]
          linarith))
        exact hconv

end

end ProofGap.Exercise2813

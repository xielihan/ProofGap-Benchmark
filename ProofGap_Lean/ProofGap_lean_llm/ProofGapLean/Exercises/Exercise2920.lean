import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace ProofGap.Exercise2920

noncomputable section

open Filter
open scoped BigOperators Topology

def center (α : ℝ) : ℂ :=
  Complex.exp (Complex.I * (α : ℂ))

def denominator (α : ℝ) : ℂ :=
  1 - center α

def coefficient (α : ℝ) (n : ℕ) : ℂ :=
  1 / ((n : ℂ) * denominator α ^ n)

def ratioSeq (α : ℝ) (n : ℕ) : ℝ :=
  ‖coefficient α n / coefficient α (n + 1)‖

def formulaSeq (α : ℝ) (n : ℕ) : ℝ :=
  ‖((((n + 1 : ℕ) : ℝ) / (n : ℝ) : ℝ) : ℂ) *
      denominator α‖

def SameLimit (u v : ℕ → ℝ) : Prop :=
  ∃ L : ℝ,
    Tendsto u atTop (𝓝 L) ∧ Tendsto v atTop (𝓝 L)

def radius (α : ℝ) : ℝ :=
  |2 * Real.sin (α / 2)|

def seriesTerm (α : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  (z - center α) ^ n /
    ((n : ℂ) * denominator α ^ n)

def SeriesConvergesAt (α : ℝ) (z : ℂ) : Prop :=
  Summable (fun k : ℕ => seriesTerm α (k + 1) z)
    (SummationFilter.conditional ℕ)

def convergenceSet (α : ℝ) : Set ℂ :=
  {z | SeriesConvergesAt α z}

def openDisk (α : ℝ) : Set ℂ :=
  {z | ‖z - center α‖ < radius α}

def coordinateOpenDisk (α : ℝ) : Set ℂ :=
  {z |
    (z.re - Real.cos α) ^ 2 + (z.im - Real.sin α) ^ 2 <
      4 * Real.sin (α / 2) ^ 2}

def correctedConvergenceSet (α : ℝ) : Set ℂ :=
  {z |
    ‖z - center α‖ ≤ radius α ∧ z ≠ 1}

def correctedCoordinateSet (α : ℝ) : Set ℂ :=
  {z |
    (z.re - Real.cos α) ^ 2 + (z.im - Real.sin α) ^ 2 ≤
        4 * Real.sin (α / 2) ^ 2 ∧
      z ≠ 1}

private theorem center_eq_cos_add_sin_mul_I (α : ℝ) :
    center α =
      (Real.cos α : ℂ) + Complex.I * (Real.sin α : ℂ) := by
  unfold center
  rw [mul_comm]
  simpa [mul_comm] using Complex.exp_ofReal_mul_I α

private theorem ratio_factor_tendsto :
    Tendsto
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / (n : ℝ))
      atTop (𝓝 1) := by
  have hbase :
      Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ))
        atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
  have heq :
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / (n : ℝ)) =ᶠ[atTop]
        fun n : ℕ => 1 + 1 / (n : ℝ) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    field_simp
    norm_num
  simpa using hbase.congr' heq.symm

private theorem formulaSeq_tendsto (α : ℝ) :
    Tendsto (formulaSeq α) atTop (𝓝 ‖denominator α‖) := by
  have hc :
      Tendsto
        (fun n : ℕ =>
          ((((n + 1 : ℕ) : ℝ) / (n : ℝ) : ℝ) : ℂ))
        atTop (𝓝 (1 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp ratio_factor_tendsto
  have hm :
      Tendsto
        (fun n : ℕ =>
          ((((n + 1 : ℕ) : ℝ) / (n : ℝ) : ℝ) : ℂ) *
            denominator α)
        atTop (𝓝 ((1 : ℂ) * denominator α)) :=
    hc.mul_const _
  convert (continuous_norm.continuousAt.tendsto.comp hm) using 1
  simp

private theorem ratioSeq_eventuallyEq_formulaSeq
    (α : ℝ) (hα : center α ≠ 1) :
    ratioSeq α =ᶠ[atTop] formulaSeq α := by
  have hd : denominator α ≠ 0 := by
    unfold denominator
    exact sub_ne_zero.mpr hα.symm
  filter_upwards [eventually_gt_atTop 0] with n hn
  unfold ratioSeq formulaSeq coefficient
  have hn0 : (n : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  have hns0 : ((n + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have hcast :
      (((((n + 1 : ℕ) : ℝ) / (n : ℝ) : ℝ) : ℂ)) =
        ((n + 1 : ℕ) : ℂ) / (n : ℂ) := by
    push_cast
    rfl
  congr 1
  rw [hcast, pow_succ]
  field_simp [hn0, hns0, hd]

private theorem norm_sub_center_sq (α : ℝ) (z : ℂ) :
    ‖z - center α‖ ^ 2 =
      (z.re - Real.cos α) ^ 2 + (z.im - Real.sin α) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply,
    center_eq_cos_add_sin_mul_I]
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, Complex.I_im, Complex.sub_im,
    Complex.add_im, Complex.ofReal_im, Complex.mul_im, zero_mul,
    one_mul, add_zero, sub_zero, zero_add]
  ring

private theorem radius_sq (α : ℝ) :
    radius α ^ 2 = 4 * Real.sin (α / 2) ^ 2 := by
  unfold radius
  rw [sq_abs]
  ring

private theorem seriesConverges_iff_tendsto_sum_range (u : ℕ → ℂ) :
    Summable u (SummationFilter.conditional ℕ) ↔
      ∃ l : ℂ,
        Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, u n) atTop (𝓝 l) := by
  unfold Summable HasSum
  rw [SummationFilter.conditional_filter_eq_map_range]
  simp only [tendsto_map'_iff]
  constructor <;> rintro ⟨l, hl⟩
  · exact ⟨l, by simpa [Function.comp_def] using hl⟩
  · exact ⟨l, by simpa [Function.comp_def] using hl⟩

private theorem seriesConverges_of_summable {u : ℕ → ℂ} (hu : Summable u) :
    Summable u (SummationFilter.conditional ℕ) := by
  exact hu.mono_filter (SummationFilter.conditional ℕ).le_atTop

private theorem seriesConverges_tendsto_zero {u : ℕ → ℂ}
    (hu : Summable u (SummationFilter.conditional ℕ)) :
    Tendsto u atTop (𝓝 0) := by
  obtain ⟨l, hl⟩ := (seriesConverges_iff_tendsto_sum_range u).1 hu
  have hshift := hl.comp (tendsto_add_atTop_nat 1)
  have hsub := hshift.sub hl
  convert hsub using 1
  · funext n
    simp [Finset.sum_range_succ]
  · ring

private theorem real_summable_of_seriesConverges_of_nonneg {u : ℕ → ℝ}
    (hu : ProofGap.SeriesConverges u) (hu0 : ∀ n, 0 ≤ u n) : Summable u := by
  unfold ProofGap.SeriesConverges Summable HasSum at hu
  rcases hu with ⟨l, hl⟩
  have hrange :
      Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, u n) atTop (𝓝 l) := by
    rw [SummationFilter.conditional_filter_eq_map_range] at hl
    simpa [Function.comp_def] using hl
  exact ⟨l, (hasSum_iff_tendsto_nat_of_nonneg hu0 l).2 hrange⟩

private theorem seriesTerm_eq_normalized (α : ℝ) (z : ℂ)
    (hα : center α ≠ 1) (n : ℕ) (hn : n ≠ 0) :
    seriesTerm α n z =
      ((z - center α) / denominator α) ^ n / (n : ℂ) := by
  have hd : denominator α ≠ 0 := by
    unfold denominator
    exact sub_ne_zero.mpr hα.symm
  unfold seriesTerm
  rw [div_pow]
  field_simp [hd, hn]

private theorem summable_normalized_of_norm_lt_one {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun k : ℕ => q ^ (k + 1) / ((k + 1 : ℕ) : ℂ)) := by
  have hg0 : Summable (fun k : ℕ => ‖q‖ ^ k) :=
    summable_geometric_of_lt_one (norm_nonneg q) hq
  have hg : Summable (fun k : ℕ => ‖q‖ ^ (k + 1)) :=
    (summable_nat_add_iff 1).mpr hg0
  refine hg.of_norm_bounded (fun k => ?_)
  rw [norm_div, norm_pow]
  have hk : (1 : ℝ) ≤ ‖(((k + 1 : ℕ) : ℂ))‖ := by
    rw [Complex.norm_natCast]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  exact div_le_self (by positivity) hk

private theorem normalized_partial_sums_bounded {q : ℂ}
    (hqnorm : ‖q‖ = 1) (hq1 : q ≠ 1) :
    ∀ n : ℕ, ‖∑ i ∈ Finset.range n, q ^ (i + 1)‖ ≤ 2 / ‖q - 1‖ := by
  intro n
  have heq :
      (∑ i ∈ Finset.range n, q ^ (i + 1)) =
        q * ((q ^ n - 1) / (q - 1)) := by
    calc
      (∑ i ∈ Finset.range n, q ^ (i + 1)) =
          ∑ i ∈ Finset.range n, q * q ^ i := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [pow_succ']
      _ = q * ∑ i ∈ Finset.range n, q ^ i := by rw [Finset.mul_sum]
      _ = q * ((q ^ n - 1) / (q - 1)) := by rw [geom_sum_eq hq1 n]
  rw [heq, norm_mul, norm_div, hqnorm, one_mul]
  have hnum : ‖q ^ n - 1‖ ≤ 2 := by
    calc
      ‖q ^ n - 1‖ ≤ ‖q ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by norm_num [norm_pow, hqnorm]
  exact div_le_div_of_nonneg_right hnum (norm_nonneg _)

private theorem seriesConverges_normalized_of_norm_eq_one {q : ℂ}
    (hqnorm : ‖q‖ = 1) (hq1 : q ≠ 1) :
    Summable (fun k : ℕ => q ^ (k + 1) / ((k + 1 : ℕ) : ℂ))
      (SummationFilter.conditional ℕ) := by
  let f : ℕ → ℝ := fun k => 1 / ((k + 1 : ℕ) : ℝ)
  let v : ℕ → ℂ := fun k => q ^ (k + 1)
  have hfanti : Antitone f := by
    intro a b hab
    dsimp [f]
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hab 1
  have hf0 : Tendsto f atTop (𝓝 0) := by
    dsimp [f]
    have hbase : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    simpa [Function.comp_def, one_div, Nat.cast_add] using
      (hbase.comp (tendsto_add_atTop_nat 1))
  have hvbound : ∀ n : ℕ, ‖∑ i ∈ Finset.range n, v i‖ ≤ 2 / ‖q - 1‖ := by
    simpa [v] using normalized_partial_sums_bounded hqnorm hq1
  have hc := hfanti.cauchySeq_series_mul_of_tendsto_zero_of_bounded hf0 hvbound
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hc
  apply (seriesConverges_iff_tendsto_sum_range _).2
  refine ⟨l, ?_⟩
  convert hl using 1
  funext n
  apply Finset.sum_congr rfl
  intro k hk
  dsimp [f, v]
  change q ^ (k + 1) / ((k + 1 : ℕ) : ℂ) =
    ((1 / ((k + 1 : ℕ) : ℝ) : ℝ) : ℂ) * q ^ (k + 1)
  push_cast
  field_simp

private theorem not_seriesConverges_of_ratio_test_tendsto_gt_one
    {u : ℕ → ℂ} {l : ℝ} (hl : 1 < l) (hu0 : ∀ n, u n ≠ 0)
    (h : Tendsto (fun n => ‖u (n + 1)‖ / ‖u n‖) atTop (𝓝 l)) :
    ¬ Summable u (SummationFilter.conditional ℕ) := by
  intro hu
  obtain ⟨r, hr1, hrl⟩ := exists_between hl
  have hge : ∀ᶠ n in atTop, r * ‖u n‖ ≤ ‖u (n + 1)‖ := by
    filter_upwards [h.eventually_const_le hrl] with n hn
    rwa [← le_div_iff₀ (norm_pos_iff.mpr (hu0 n))]
  rw [eventually_atTop] at hge
  obtain ⟨N, hN⟩ := hge
  have hgrowth : Tendsto (fun n : ℕ => ‖u (n + N)‖) atTop atTop := by
    apply tendsto_atTop_of_geom_le
      (v := fun n : ℕ => ‖u (n + N)‖) (c := r)
      (by simpa using norm_pos_iff.mpr (hu0 N)) hr1
    intro n
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      hN (n + N) (by omega)
  have hzero : Tendsto (fun n : ℕ => ‖u (n + N)‖) atTop (𝓝 0) := by
    simpa using
      ((seriesConverges_tendsto_zero hu).comp (tendsto_add_atTop_nat N)).norm
  exact not_tendsto_atTop_of_tendsto_nhds hzero hgrowth

private theorem normalized_ratio_tendsto (q : ℂ) (hq : q ≠ 0) :
    Tendsto
      (fun n : ℕ =>
        ‖q ^ (n + 2) / ((n + 2 : ℕ) : ℂ)‖ /
          ‖q ^ (n + 1) / ((n + 1 : ℕ) : ℂ)‖)
      atTop (𝓝 ‖q‖) := by
  have hfac : Tendsto
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ))
      atTop (𝓝 1) := by
    have hbase : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have hzero : Tendsto
        (fun n : ℕ => 1 / ((n + 2 : ℕ) : ℝ)) atTop (𝓝 0) := by
      simpa [Function.comp_def] using
        hbase.comp (tendsto_add_atTop_nat 2)
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hzero
    convert h using 1
    · funext n
      have hn2 : (((n + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
      push_cast
      field_simp [hn2]
      ring
    · norm_num
  have hlim : Tendsto
      (fun n : ℕ => ‖q‖ *
        (((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)))
      atTop (𝓝 ‖q‖) := by
    simpa using (tendsto_const_nhds (x := ‖q‖)).mul hfac
  refine hlim.congr' (Eventually.of_forall (fun n => ?_))
  simp only [norm_div, norm_pow]
  have hqnorm : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  have hn1 : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hn2 : (((n + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
  simp only [Complex.norm_natCast]
  rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
  field_simp [hqnorm, hn1, hn2, pow_ne_zero _ hqnorm]

private theorem not_seriesConverges_normalized_of_one_lt_norm {q : ℂ}
    (hq : 1 < ‖q‖) :
    ¬ Summable (fun k : ℕ => q ^ (k + 1) / ((k + 1 : ℕ) : ℂ))
      (SummationFilter.conditional ℕ) := by
  have hq0 : q ≠ 0 := by
    exact norm_ne_zero_iff.mp (ne_of_gt (zero_lt_one.trans hq))
  apply not_seriesConverges_of_ratio_test_tendsto_gt_one hq
  · intro n
    exact div_ne_zero (pow_ne_zero _ hq0) (by exact_mod_cast Nat.succ_ne_zero n)
  · simpa [Nat.add_assoc] using normalized_ratio_tendsto q hq0

theorem gap1 (α : ℝ) (hα : center α ≠ 1) :
    SameLimit (ratioSeq α) (formulaSeq α) := by
  refine ⟨‖denominator α‖, ?_, formulaSeq_tendsto α⟩
  exact (formulaSeq_tendsto α).congr'
    (ratioSeq_eventuallyEq_formulaSeq α hα).symm

theorem gap2 (α : ℝ) (hα : center α ≠ 1) :
    Tendsto (ratioSeq α) atTop
      (𝓝 ‖1 - ((Real.cos α : ℂ) +
        Complex.I * (Real.sin α : ℂ))‖) := by
  rw [← center_eq_cos_add_sin_mul_I]
  exact (formulaSeq_tendsto α).congr'
    (ratioSeq_eventuallyEq_formulaSeq α hα).symm

theorem gap3 (α : ℝ) :
    ‖1 - ((Real.cos α : ℂ) +
        Complex.I * (Real.sin α : ℂ))‖ =
      Real.sqrt ((1 - Real.cos α) ^ 2 + Real.sin α ^ 2) := by
  rw [Complex.norm_def]
  congr 1
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re,
    Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.sub_im, Complex.one_im, Complex.add_im,
    Complex.ofReal_im, Complex.mul_im, zero_mul, one_mul, add_zero,
    sub_zero, zero_add]
  ring

theorem gap4 (α : ℝ) :
    Real.sqrt ((1 - Real.cos α) ^ 2 + Real.sin α ^ 2) =
      radius α := by
  unfold radius
  rw [← Real.sqrt_sq_eq_abs]
  congr 1
  have hcos :
      Real.cos α = 2 * Real.cos (α / 2) ^ 2 - 1 := by
    conv_lhs => rw [show α = 2 * (α / 2) by ring]
    rw [Real.cos_two_mul]
  have hsin :
      Real.sin α =
        2 * Real.sin (α / 2) * Real.cos (α / 2) := by
    conv_lhs => rw [show α = 2 * (α / 2) by ring]
    rw [Real.sin_two_mul]
  rw [hcos, hsin]
  have hsq :
      1 - Real.cos (α / 2) ^ 2 = Real.sin (α / 2) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (α / 2)]
  calc
    (1 - (2 * Real.cos (α / 2) ^ 2 - 1)) ^ 2 +
          (2 * Real.sin (α / 2) * Real.cos (α / 2)) ^ 2 =
        4 * (1 - Real.cos (α / 2) ^ 2) ^ 2 +
          4 * Real.sin (α / 2) ^ 2 * Real.cos (α / 2) ^ 2 := by ring
    _ = 4 * Real.sin (α / 2) ^ 4 +
          4 * Real.sin (α / 2) ^ 2 * Real.cos (α / 2) ^ 2 := by
      rw [hsq]
      ring
    _ =
        4 * Real.sin (α / 2) ^ 2 *
          (Real.sin (α / 2) ^ 2 + Real.cos (α / 2) ^ 2) := by ring
    _ = 4 * Real.sin (α / 2) ^ 2 := by
      rw [Real.sin_sq_add_cos_sq]
      ring
    _ = (2 * Real.sin (α / 2)) ^ 2 := by ring

theorem gap5 (α : ℝ) (hα : center α ≠ 1) :
    Tendsto (ratioSeq α) atTop (𝓝 (radius α)) := by
  convert gap2 α hα using 1
  rw [gap3, gap4]

theorem gap6 (α : ℝ) (hα : center α ≠ 1) :
    ∃ R : ℝ, R = radius α := by
  exact ⟨radius α, rfl⟩

theorem gap7 (α : ℝ) (hα : center α ≠ 1) :
    convergenceSet α = correctedConvergenceSet α := by
  have hd : denominator α ≠ 0 := by
    unfold denominator
    exact sub_ne_zero.mpr hα.symm
  have hdNorm : ‖denominator α‖ = radius α := by
    unfold denominator
    rw [center_eq_cos_add_sin_mul_I, gap3, gap4]
  ext z
  simp only [convergenceSet, correctedConvergenceSet, Set.mem_setOf_eq]
  let q : ℂ := (z - center α) / denominator α
  have hqNorm : ‖q‖ = ‖z - center α‖ / radius α := by
    dsimp [q]
    rw [norm_div, hdNorm]
  have hnormalize :
      (fun k : ℕ => seriesTerm α (k + 1) z) =
        fun k : ℕ => q ^ (k + 1) / ((k + 1 : ℕ) : ℂ) := by
    funext k
    exact seriesTerm_eq_normalized α z hα (k + 1) (Nat.succ_ne_zero k)
  constructor
  · intro hconv
    have hnormalized :
        Summable (fun k : ℕ => q ^ (k + 1) / ((k + 1 : ℕ) : ℂ))
          (SummationFilter.conditional ℕ) := by
      rw [← hnormalize]
      exact hconv
    constructor
    · by_contra hnot
      have hr : 0 < radius α := by
        rw [← hdNorm]
        exact norm_pos_iff.mpr hd
      have hout : radius α < ‖z - center α‖ := lt_of_not_ge hnot
      have hq : 1 < ‖q‖ := by
        rw [hqNorm]
        exact (one_lt_div hr).2 hout
      exact (not_seriesConverges_normalized_of_one_lt_norm hq) hnormalized
    · intro hz
      subst z
      have hqone : q = 1 := by
        dsimp [q, denominator]
        exact div_self (sub_ne_zero.mpr hα.symm)
      rw [hqone] at hnormalized
      have hreal : ProofGap.SeriesConverges
          (fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ)) := by
        unfold ProofGap.SeriesConverges
        unfold Summable at hnormalized ⊢
        rcases hnormalized with ⟨l, hl⟩
        refine ⟨l.re, ?_⟩
        convert Complex.hasSum_re hl using 1
        funext k
        simp only [one_pow, Complex.div_natCast_re, Complex.one_re]
      have hsum : Summable (fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ)) :=
        real_summable_of_seriesConverges_of_nonneg hreal (fun k => by positivity)
      have hharm : Summable (fun n : ℕ => 1 / (n : ℝ)) := by
        apply (summable_nat_add_iff 1).mp
        simpa [Nat.cast_add] using hsum
      exact Real.not_summable_one_div_natCast hharm
  · rintro ⟨hin, hz1⟩
    have hr : 0 < radius α := by
      rw [← hdNorm]
      exact norm_pos_iff.mpr hd
    change Summable (fun k : ℕ => seriesTerm α (k + 1) z)
      (SummationFilter.conditional ℕ)
    rw [hnormalize]
    by_cases hstrict : ‖z - center α‖ < radius α
    · apply seriesConverges_of_summable
      apply summable_normalized_of_norm_lt_one
      rw [hqNorm]
      exact (div_lt_one hr).2 hstrict
    · have heq : ‖z - center α‖ = radius α :=
        le_antisymm hin (le_of_not_gt hstrict)
      have hqnorm1 : ‖q‖ = 1 := by
        rw [hqNorm, heq, div_self hr.ne']
      have hq1 : q ≠ 1 := by
        intro hq
        dsimp [q] at hq
        have hz : z - center α = denominator α :=
          (div_eq_one_iff_eq hd).mp hq
        unfold denominator at hz
        apply hz1
        linear_combination hz
      exact seriesConverges_normalized_of_norm_eq_one hqnorm1 hq1

theorem gap8 (α : ℝ) :
    openDisk α = coordinateOpenDisk α := by
  ext z
  simp only [openDisk, coordinateOpenDisk, Set.mem_setOf_eq]
  have hr : 0 ≤ radius α := by
    unfold radius
    exact abs_nonneg _
  constructor
  · intro h
    have hs :
        ‖z - center α‖ ^ 2 < radius α ^ 2 :=
      (sq_lt_sq₀ (norm_nonneg _) hr).2 h
    rw [norm_sub_center_sq, radius_sq] at hs
    exact hs
  · intro h
    have hs :
        ‖z - center α‖ ^ 2 < radius α ^ 2 := by
      rw [norm_sub_center_sq, radius_sq]
      exact h
    exact (sq_lt_sq₀ (norm_nonneg _) hr).1 hs

theorem gap9 (α : ℝ) (hα : center α ≠ 1) :
    convergenceSet α = correctedCoordinateSet α := by
  rw [gap7 α hα]
  ext z
  simp only [correctedConvergenceSet, correctedCoordinateSet, Set.mem_setOf_eq]
  have hr : 0 ≤ radius α := by
    unfold radius
    exact abs_nonneg _
  constructor
  · rintro ⟨h, hz⟩
    refine ⟨?_, hz⟩
    have hs : ‖z - center α‖ ^ 2 ≤ radius α ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hr).2 h
    rwa [norm_sub_center_sq, radius_sq] at hs
  · rintro ⟨h, hz⟩
    refine ⟨?_, hz⟩
    apply (sq_le_sq₀ (norm_nonneg _) hr).1
    rwa [norm_sub_center_sq, radius_sq]

end

end ProofGap.Exercise2920

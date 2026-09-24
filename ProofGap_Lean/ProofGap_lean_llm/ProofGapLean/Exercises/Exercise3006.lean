import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ProofGap.Exercise3006

noncomputable section

open Filter
open scoped BigOperators Interval Topology

def coefficient (n : ℕ) : ℝ := 1 / (n : ℝ)

def term (x : ℝ) (n : ℕ) : ℝ := x ^ n / (n : ℝ)

def seriesFunction (x : ℝ) : ℝ :=
  ∑'[SummationFilter.conditional ℕ] n : ℕ, term x (n + 1)

def convergenceDomain : Set ℝ :=
  {x | ProofGap.SeriesConverges (fun n : ℕ => term x (n + 1))}

def powerSeriesRadius (a : ℕ → ℝ) : ℝ :=
  sSup {r : ℝ | 0 ≤ r ∧ ∀ x : ℝ, |x| < r → Summable (fun n => a n * x ^ n)}

private theorem coefficient_summable_of_abs_lt_one {x : ℝ} (hx : |x| < 1) :
    Summable (fun n : ℕ => coefficient n * x ^ n) := by
  have hgeom : Summable (fun n : ℕ => |x| ^ n) := by
    apply summable_geometric_of_norm_lt_one
    simpa [Real.norm_eq_abs] using hx
  apply hgeom.of_norm_bounded
  intro n
  have hc : ‖coefficient n‖ ≤ 1 := by
    by_cases hn : n = 0
    · subst n
      simp [coefficient]
    · have hnPos : (0 : ℝ) < n := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      have hnOne : (1 : ℝ) ≤ n := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      rw [coefficient, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hnPos)]
      exact (div_le_one₀ hnPos).2 hnOne
  calc
    ‖coefficient n * x ^ n‖ = ‖coefficient n‖ * |x| ^ n := by
      simp only [norm_mul, norm_pow, Real.norm_eq_abs]
    _ ≤ 1 * |x| ^ n :=
      mul_le_mul_of_nonneg_right hc (pow_nonneg (abs_nonneg x) n)
    _ = |x| ^ n := one_mul _

private theorem seriesFunction_eq_neg_log {x : ℝ} (hx : |x| < 1) :
    seriesFunction x = -Real.log (1 - x) := by
  unfold seriesFunction
  have h : HasSum (fun n : ℕ => x ^ (n + 1) / (n + 1))
      (-Real.log (1 - x)) (SummationFilter.conditional ℕ) :=
    (Real.hasSum_pow_div_log_of_abs_lt_one hx).mono_left
      (SummationFilter.conditional ℕ).le_atTop
  simpa [term] using h.tsum_eq

private theorem deriv_seriesFunction_of_abs_lt_one {x : ℝ} (hx : |x| < 1) :
    deriv seriesFunction x = 1 / (1 - x) := by
  have hxlt : x < 1 := (abs_lt.mp hx).2
  have hne : 1 - x ≠ 0 := by linarith
  have hlog : HasDerivAt (fun y : ℝ => -Real.log (1 - y))
      (1 / (1 - x)) x := by
    convert ((Real.hasDerivAt_log hne).comp x
      ((hasDerivAt_const x 1).sub (hasDerivAt_id x))).neg using 1 <;>
      simp [one_div]
  have hopen : IsOpen {y : ℝ | |y| < 1} :=
    isOpen_lt continuous_abs continuous_const
  have heq : seriesFunction =ᶠ[𝓝 x]
      (fun y : ℝ => -Real.log (1 - y)) := by
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact seriesFunction_eq_neg_log hy
  exact (hlog.congr_of_eventuallyEq heq).deriv

private theorem nat_succ_ratio_tendsto :
    Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
  have hlim : Tendsto (fun n : ℕ => (1 : ℝ) + 1 / (n : ℝ)) atTop
      (𝓝 ((1 : ℝ) + 0)) :=
    tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
  convert hlim.congr' ?_ using 1 <;> norm_num
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hnCast : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp [hnCast]

private theorem seriesConverges_iff_tendsto_sum_range (u : ℕ → ℝ) :
    ProofGap.SeriesConverges u ↔
      ∃ l : ℝ,
        Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, u n) atTop (𝓝 l) := by
  unfold ProofGap.SeriesConverges Summable HasSum
  rw [SummationFilter.conditional_filter_eq_map_range]
  simp only [tendsto_map'_iff]
  constructor <;> rintro ⟨l, hl⟩
  · exact ⟨l, by simpa [Function.comp_def] using hl⟩
  · exact ⟨l, by simpa [Function.comp_def] using hl⟩

private theorem seriesHasSum_iff_tendsto_sum_range (u : ℕ → ℝ) (l : ℝ) :
    ProofGap.SeriesHasSum u l ↔
      Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, u n) atTop (𝓝 l) := by
  unfold ProofGap.SeriesHasSum HasSum
  rw [SummationFilter.conditional_filter_eq_map_range]
  simp [tendsto_map'_iff, Function.comp_def]

private theorem seriesConverges_of_summable {u : ℕ → ℝ} (hu : Summable u) :
    ProofGap.SeriesConverges u := by
  unfold ProofGap.SeriesConverges
  exact hu.mono_filter (SummationFilter.conditional ℕ).le_atTop

private theorem seriesConverges_tendsto_zero {u : ℕ → ℝ}
    (hu : ProofGap.SeriesConverges u) : Tendsto u atTop (𝓝 0) := by
  obtain ⟨l, hl⟩ := (seriesConverges_iff_tendsto_sum_range u).1 hu
  have hshift := hl.comp (tendsto_add_atTop_nat 1)
  have hsub := hshift.sub hl
  convert hsub using 1
  · funext n
    simp [Finset.sum_range_succ]
  · ring

private theorem summable_of_seriesConverges_of_nonneg {u : ℕ → ℝ}
    (hu : ProofGap.SeriesConverges u) (hu0 : ∀ n, 0 ≤ u n) : Summable u := by
  obtain ⟨l, hl⟩ := (seriesConverges_iff_tendsto_sum_range u).1 hu
  exact ⟨l, (hasSum_iff_tendsto_nat_of_nonneg hu0 l).2 hl⟩

private theorem norm_term_tendsto_atTop_of_one_lt_abs {x : ℝ}
    (hx : 1 < |x|) :
    Tendsto (fun n : ℕ => ‖term x (n + 1)‖) atTop atTop := by
  have hzero :=
    (tendsto_pow_const_div_const_pow_of_one_lt 1 hx).comp
      (tendsto_add_atTop_nat 1)
  have hzeroGT :
      Tendsto
        (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 1) / |x| ^ (n + 1))
        atTop (𝓝[>] (0 : ℝ)) := by
    rw [nhdsWithin]
    refine tendsto_inf.2 ⟨hzero, ?_⟩
    apply tendsto_principal.2
    filter_upwards with n
    change 0 < (((n + 1 : ℕ) : ℝ) ^ 1) / |x| ^ (n + 1)
    positivity
  have hinv := hzeroGT.inv_tendsto_nhdsGT_zero
  convert hinv using 1
  funext n
  simp only [term, norm_div, norm_pow, Real.norm_eq_abs,
    Nat.cast_add, Nat.cast_one, pow_one]
  rw [abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
  simp [inv_div]

private theorem term_neg_one_hasSum :
    ProofGap.SeriesHasSum (fun n : ℕ => term (-1) (n + 1))
      (-Real.log 2) := by
  let f : ℕ → ℝ := fun n => 1 / ((n + 1 : ℕ) : ℝ)
  have hfanti : Antitone f := by
    intro a b hab
    dsimp [f]
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hab 1
  have hf0 : Tendsto f atTop (𝓝 0) := by
    dsimp [f]
    have hbase : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    simpa [Function.comp_def, Nat.cast_add] using
      (hbase.comp (tendsto_add_atTop_nat 1))
  obtain ⟨l, hl⟩ := hfanti.tendsto_alternating_series_of_tendsto_zero hf0
  have hneg :
      Tendsto
        (fun N : ℕ => ∑ n ∈ Finset.range N, term (-1) (n + 1))
        atTop (𝓝 (-l)) := by
    convert hl.neg using 1
    funext N
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    dsimp [term, f]
    rw [pow_succ]
    ring
  let a : ℕ → ℝ := fun n => term (-1) (n + 1)
  have habel := Real.tendsto_tsum_powerSeries_nhdsWithin_lt
    (f := a) (l := -l) hneg
  have hrpos : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), 0 < r :=
    (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono inf_le_left
  have hinside :
      (fun r : ℝ => ∑' n : ℕ, a n * r ^ n) =ᶠ[𝓝[<] (1 : ℝ)]
        (fun r : ℝ => -Real.log (1 + r) / r) := by
    filter_upwards [self_mem_nhdsWithin, hrpos] with r hrlt hr
    have habs : |-r| < 1 := by
      rw [abs_neg, abs_of_pos hr]
      exact hrlt
    have hs :=
      (Real.hasSum_pow_div_log_of_abs_lt_one habs).mul_left (1 / r)
    have hs' : HasSum (fun n : ℕ => a n * r ^ n)
        (-Real.log (1 + r) / r) := by
      convert hs using 1
      · funext n
        dsimp [a, term]
        rw [neg_pow, pow_succ]
        field_simp [hr.ne']
        push_cast
        ring
      · rw [sub_neg_eq_add]
        field_simp [hr.ne']
    exact hs'.tsum_eq
  have hcontFull :
      Tendsto (fun r : ℝ => -Real.log (1 + r) / r) (𝓝 1)
        (𝓝 (-Real.log 2)) := by
    have hcLog : ContinuousAt (fun r : ℝ => Real.log (1 + r)) 1 :=
      (continuousAt_const.add continuousAt_id).log (by norm_num)
    have hc : ContinuousAt (fun r : ℝ => -Real.log (1 + r) / r) 1 :=
      hcLog.neg.div continuousAt_id (by norm_num)
    convert hc.tendsto using 1 <;> norm_num
  have hm : 𝓝[<] (1 : ℝ) ≤ 𝓝 1 :=
    tendsto_nhdsWithin_of_tendsto_nhds fun _ h => h
  have hcont := hcontFull.mono_left hm
  have hlvalue : -l = -Real.log 2 :=
    tendsto_nhds_unique (habel.congr' hinside) hcont
  apply (seriesHasSum_iff_tendsto_sum_range
    (fun n : ℕ => term (-1) (n + 1)) (-Real.log 2)).2
  simpa only [hlvalue] using hneg

private theorem seriesFunction_neg_one :
    seriesFunction (-1) = -Real.log 2 := by
  unfold seriesFunction
  exact term_neg_one_hasSum.tsum_eq

private theorem seriesFunction_eq_neg_log_of_mem {x : ℝ}
    (hx : x ∈ Set.Ico (-1 : ℝ) 1) :
    seriesFunction x = -Real.log (1 - x) := by
  rcases eq_or_lt_of_le hx.1 with rfl | hneg
  · rw [seriesFunction_neg_one]
    norm_num
  · exact seriesFunction_eq_neg_log (abs_lt.mpr ⟨hneg, hx.2⟩)

theorem gap1 :
    ∃ a : ℕ → ℝ,
      (∀ n, a n = coefficient n) ∧
      Tendsto (fun n : ℕ => |a n / a (n + 1)|) atTop (𝓝 1) ∧
      Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
  refine ⟨coefficient, fun n => rfl, ?_, nat_succ_ratio_tendsto⟩
  apply nat_succ_ratio_tendsto.congr'
  filter_upwards with n
  by_cases hn : n = 0
  · subst n
    simp [coefficient]
  · have hnPos : (0 : ℝ) < n := by
      exact_mod_cast Nat.pos_of_ne_zero hn
    have hsuccPos : (0 : ℝ) < n + 1 := by positivity
    have heq : coefficient n / coefficient (n + 1) =
        ((n + 1 : ℕ) : ℝ) / (n : ℝ) := by
      unfold coefficient
      field_simp
    rw [heq]
    simpa only [Nat.cast_add, Nat.cast_one] using
      (abs_of_pos (div_pos hsuccPos hnPos)).symm

theorem gap2 :
    Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
  exact nat_succ_ratio_tendsto

theorem gap3 :
    ∃ a : ℕ → ℝ,
      (∀ n, a n = coefficient n) ∧
      Tendsto (fun n : ℕ => |a n / a (n + 1)|) atTop (𝓝 1) := by
  rcases gap1 with ⟨a, ha, hratio, hnat⟩
  exact ⟨a, ha, hratio⟩

theorem gap4 : powerSeriesRadius coefficient = 1 := by
  unfold powerSeriesRadius
  have hset :
      {r : ℝ | 0 ≤ r ∧ ∀ x : ℝ, |x| < r →
        Summable (fun n => coefficient n * x ^ n)} = Set.Icc 0 1 := by
    ext r
    constructor
    · intro hr
      refine ⟨hr.1, le_of_not_gt ?_⟩
      intro hOne
      have hsum := hr.2 1 (by simpa using hOne)
      apply Real.not_summable_one_div_natCast
      simpa [coefficient] using hsum
    · intro hr
      refine ⟨hr.1, ?_⟩
      intro x hx
      exact coefficient_summable_of_abs_lt_one (hx.trans_le hr.2)
  rw [hset, csSup_Icc (by norm_num : (0 : ℝ) ≤ 1)]

theorem gap5 (x : ℝ) (hx : x = 1) :
    ¬Summable (fun n : ℕ => term x (n + 1)) := by
  subst x
  intro hsum
  have htail : Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ))) := by
    simpa [term] using hsum
  apply Real.not_summable_one_div_natCast
  exact (summable_nat_add_iff 1).1 htail

theorem gap6 (x : ℝ) (hx : x = -1) :
    ProofGap.SeriesConverges (fun n : ℕ => term x (n + 1)) := by
  subst x
  exact term_neg_one_hasSum.summable

theorem gap7 : convergenceDomain = Set.Ico (-1) 1 := by
  ext x
  simp only [convergenceDomain, Set.mem_setOf_eq, Set.mem_Ico]
  constructor
  · intro hconv
    constructor
    · by_contra hnot
      have hx : x < -1 := lt_of_not_ge hnot
      have habs : 1 < |x| := by
        rw [abs_of_neg (by linarith)]
        linarith
      have hzero := (seriesConverges_tendsto_zero hconv).norm
      exact not_tendsto_atTop_of_tendsto_nhds hzero
        (norm_term_tendsto_atTop_of_one_lt_abs habs)
    · by_contra hnot
      have hx : 1 ≤ x := le_of_not_gt hnot
      have hnonneg : ∀ n : ℕ, 0 ≤ term x (n + 1) := by
        intro n
        unfold term
        positivity
      have hsum := summable_of_seriesConverges_of_nonneg hconv hnonneg
      have hharmShift : Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ))) := by
        refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hsum
        unfold term
        have hpow : (1 : ℝ) ≤ x ^ (n + 1) := one_le_pow₀ hx
        have hden : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
        exact (div_le_div_iff_of_pos_right hden).2 hpow
      have hharm : Summable (fun n : ℕ => 1 / (n : ℝ)) := by
        apply (summable_nat_add_iff 1).mp
        simpa [Nat.cast_add] using hharmShift
      exact Real.not_summable_one_div_natCast hharm
  · rintro ⟨hxlo, hxhi⟩
    rcases hxlo.eq_or_lt with hEq | hlt
    · subst x
      exact term_neg_one_hasSum.summable
    · apply seriesConverges_of_summable
      have hfull := coefficient_summable_of_abs_lt_one
        (abs_lt.mpr ⟨hlt, hxhi⟩)
      have hshift := (summable_nat_add_iff 1).mpr hfull
      simpa [term, coefficient, div_eq_mul_inv, mul_comm] using hshift

theorem gap8 (x : ℝ) (hx : x ∈ Set.Ico (-1 : ℝ) 1) (habs : |x| < 1) :
    deriv seriesFunction x = ∑' n : ℕ, x ^ n := by
  rw [deriv_seriesFunction_of_abs_lt_one habs]
  symm
  simpa [one_div] using tsum_geometric_of_abs_lt_one habs

theorem gap9 (x : ℝ) (hx : x ∈ Set.Ico (-1 : ℝ) 1) (habs : |x| < 1) :
    (∑' n : ℕ, x ^ n) = 1 / (1 - x) := by
  simpa [one_div] using tsum_geometric_of_abs_lt_one habs

theorem gap10 (x : ℝ) (hx : x ∈ Set.Ico (-1 : ℝ) 1) (habs : |x| < 1) :
    deriv seriesFunction x = 1 / (1 - x) := by
  rw [gap8 x hx habs, gap9 x hx habs]

theorem gap11 (x : ℝ) (hx : x ∈ Set.Ico (-1 : ℝ) 1) :
    seriesFunction 0 = 0 := by
  simp [seriesFunction, term]

theorem gap12 (x : ℝ) (hx : x ∈ Set.Ico (-1 : ℝ) 1) :
    seriesFunction x = ∫ t in 0..x, deriv seriesFunction t := by
  rw [seriesFunction_eq_neg_log_of_mem hx]
  have hderivIntegral :
      (∫ t in 0..x, deriv seriesFunction t) =
        ∫ t in 0..x, 1 / (1 - t) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t htmem
    have htBounds : -1 < t ∧ t < 1 := by
      rcases Set.mem_uIoc.mp htmem with htmem | htmem
      · constructor <;> linarith [hx.1, hx.2]
      · constructor <;> linarith [hx.1, hx.2]
    exact deriv_seriesFunction_of_abs_lt_one (abs_lt.mpr htBounds)
  rw [hderivIntegral]
  rw [intervalIntegral.integral_comp_sub_left (fun y : ℝ => 1 / y) 1]
  simp only [sub_zero]
  rw [integral_one_div_of_pos
    (by linarith [hx.2] : 0 < 1 - x) (by norm_num : (0 : ℝ) < 1)]
  rw [one_div, Real.log_inv]

theorem gap13 (x : ℝ) (hx : x ∈ Set.Ico (-1 : ℝ) 1) :
    (∫ t in 0..x, deriv seriesFunction t) =
      ∫ t in 0..x, 1 / (1 - t) := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards with t
  intro ht
  have htBounds : -1 < t ∧ t < 1 := by
    rcases Set.mem_uIoc.mp ht with ht | ht
    · constructor <;> linarith [hx.1, hx.2]
    · constructor <;> linarith [hx.1, hx.2]
  have htAbs : |t| < 1 := abs_lt.mpr htBounds
  exact gap10 t ⟨htBounds.1.le, htBounds.2⟩ htAbs

theorem gap14 (x : ℝ) (hx : x ∈ Set.Ico (-1 : ℝ) 1) :
    (∫ t in 0..x, 1 / (1 - t)) = Real.log (1 / (1 - x)) := by
  rw [intervalIntegral.integral_comp_sub_left (fun y : ℝ => 1 / y) 1]
  simpa using integral_one_div_of_pos
    (by linarith [hx.2] : 0 < 1 - x) (by norm_num : (0 : ℝ) < 1)

theorem gap15 (x : ℝ) (hx : x ∈ Set.Ico (-1 : ℝ) 1) :
    seriesFunction x = Real.log (1 / (1 - x)) := by
  rw [seriesFunction_eq_neg_log_of_mem hx, one_div, Real.log_inv]

theorem gap16 (x : ℝ) (hx : x ∈ Set.Ico (-1 : ℝ) 1) :
    (∑'[SummationFilter.conditional ℕ] n : ℕ, term x (n + 1)) =
      Real.log (1 / (1 - x)) := by
  exact gap15 x hx

end

end ProofGap.Exercise3006

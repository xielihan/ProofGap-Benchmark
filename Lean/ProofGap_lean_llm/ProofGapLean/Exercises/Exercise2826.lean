import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Real.Pi.Bounds

namespace ProofGap.Exercise2826

noncomputable section

open Filter
open scoped BigOperators Topology

def magnitude (n : ℕ) : ℝ :=
  (1 / (Nat.factorial n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n

def coefficient (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * magnitude n

def powerTerm (n : ℕ) (x : ℝ) : ℝ :=
  coefficient n * x ^ n

def SeriesConvergesAt (x : ℝ) : Prop :=
  ProofGap.SeriesConverges (fun k : ℕ => powerTerm (k + 1) x)

def HasConvergenceRadiusOne : Prop :=
  (∀ x : ℝ, |x| < 1 → SeriesConvergesAt x) ∧
    (∀ x : ℝ, 1 < |x| → ¬ SeriesConvergesAt x)

def ratioFormula (n : ℕ) : ℝ :=
  Real.exp 1 / (1 + 1 / (n : ℝ)) ^ n

def stirlingModel (n : ℕ) : ℝ :=
  1 / Real.sqrt (2 * Real.pi * (n : ℝ))

def ConditionallySummable (u : ℕ → ℝ) : Prop :=
  ProofGap.SeriesConverges u ∧ ¬ Summable (fun n => |u n|)

private theorem seriesConverges_of_summable {u : ℕ → ℝ} (hu : Summable u) :
    ProofGap.SeriesConverges u := by
  change Summable u (SummationFilter.conditional ℕ)
  exact hu.mono_filter SummationFilter.le_atTop

private theorem seriesConverges_tendsto_zero {u : ℕ → ℝ}
    (hu : ProofGap.SeriesConverges u) : Tendsto u atTop (𝓝 0) := by
  change Summable u (SummationFilter.conditional ℕ) at hu
  rcases hu with ⟨s, hs⟩
  have hpartial :
      Tendsto (fun N => ∑ n ∈ Finset.range N, u n) atTop (𝓝 s) := by
    rw [HasSum, SummationFilter.conditional_filter_eq_map_range,
      tendsto_map'_iff] at hs
    simpa [Function.comp_def] using hs
  simpa [Finset.sum_range_succ] using
    (hpartial.comp (tendsto_add_atTop_nat 1)).sub hpartial

private theorem summable_of_seriesConverges_of_nonneg {u : ℕ → ℝ}
    (hnonneg : ∀ n, 0 ≤ u n) (hu : ProofGap.SeriesConverges u) : Summable u := by
  change Summable u (SummationFilter.conditional ℕ) at hu
  rcases hu with ⟨s, hs⟩
  refine ⟨s, (hasSum_iff_tendsto_nat_of_nonneg hnonneg s).2 ?_⟩
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range,
    tendsto_map'_iff] at hs
  simpa [Function.comp_def] using hs

private theorem not_seriesConverges_of_ratio_test_tendsto_gt_one
    {u : ℕ → ℝ} {l : ℝ} (hl : 1 < l)
    (h : Tendsto (fun n => ‖u (n + 1)‖ / ‖u n‖) atTop (𝓝 l)) :
    ¬ ProofGap.SeriesConverges u := by
  intro hsum
  have hzero := seriesConverges_tendsto_zero hsum
  have key : ∀ᶠ n in atTop, ‖u n‖ ≠ 0 := by
    filter_upwards [h.eventually_const_le hl] with n hn hnorm
    rw [hnorm, div_zero] at hn
    linarith
  rcases exists_between hl with ⟨r, hr, hrl⟩
  have hgrowth : ∀ᶠ n in atTop, r * ‖u n‖ ≤ ‖u (n + 1)‖ := by
    filter_upwards [h.eventually_const_le hrl, key] with n hn hne
    rwa [← le_div_iff₀ (lt_of_le_of_ne (norm_nonneg _) hne.symm)]
  rcases Filter.eventually_atTop.1 (key.and hgrowth) with ⟨N, hN⟩
  have hNpos : 0 < ‖u N‖ :=
    lt_of_le_of_ne (norm_nonneg _) (hN N le_rfl).1.symm
  have hshift : Tendsto (fun n : ℕ => N + n) atTop atTop := by
    simpa [Nat.add_comm] using tendsto_add_atTop_nat N
  have hzeroShift : Tendsto (fun n => ‖u (N + n)‖) atTop (𝓝 0) :=
    tendsto_norm_zero.comp (hzero.comp hshift)
  have hinfty : Tendsto (fun n => ‖u (N + n)‖) atTop atTop := by
    apply tendsto_atTop_of_geom_le hNpos hr
    intro n
    convert (hN (N + n) (Nat.le_add_right N n)).2 using 1
  exact not_tendsto_atTop_of_tendsto_nhds hzeroShift hinfty

private theorem magnitude_pos (n : ℕ) : 0 < magnitude n := by
  cases n with
  | zero => norm_num [magnitude]
  | succ n =>
      unfold magnitude
      positivity

private theorem coefficient_ne_zero (n : ℕ) : coefficient n ≠ 0 := by
  unfold coefficient
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (magnitude_pos n).ne'

private theorem magnitude_ratio (n : ℕ) (hn : 1 ≤ n) :
    magnitude n / magnitude (n + 1) = ratioFormula n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have he : Real.exp 1 ≠ 0 := Real.exp_ne_zero _
  unfold magnitude ratioFormula
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp [hn0, hn1, he]
  rw [← mul_pow]
  congr 1
  field_simp

private theorem coefficient_ratio (n : ℕ) (hn : 1 ≤ n) :
    |coefficient n / coefficient (n + 1)| = ratioFormula n := by
  simp only [coefficient, abs_div, abs_mul, abs_pow, abs_neg, abs_one,
    one_pow, one_mul, abs_of_pos (magnitude_pos _)]
  exact magnitude_ratio n hn

private theorem magnitude_stirling_identity (n : ℕ) (hn : n ≠ 0) :
    magnitude n / stirlingModel n =
      Real.sqrt Real.pi / Stirling.stirlingSeq n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  unfold magnitude stirlingModel Stirling.stirlingSeq
  field_simp
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (n : ℝ) * 2)]
  ring

private theorem powerTerm_ratio (x : ℝ) (n : ℕ) :
    ‖powerTerm (n + 2) x‖ / ‖powerTerm (n + 1) x‖ =
      |x| / |coefficient (n + 1) / coefficient (n + 2)| := by
  by_cases hx : x = 0
  · subst x
    simp [powerTerm]
  · have hax : |x| ≠ 0 := abs_ne_zero.mpr hx
    have hc1 : coefficient (n + 1) ≠ 0 := coefficient_ne_zero _
    have hc2 : coefficient (n + 2) ≠ 0 := coefficient_ne_zero _
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    simp only [powerTerm, abs_mul, abs_pow]
    rw [abs_div]
    field_simp [hax, hc1, hc2, pow_ne_zero _ hax]
    ring

theorem gap1 :
    (fun n : ℕ => |coefficient (n + 1) / coefficient (n + 2)|) =
      fun n : ℕ => ratioFormula (n + 1) := by
  funext n
  exact coefficient_ratio (n + 1) (by omega)

theorem gap2 :
    Tendsto ratioFormula atTop (𝓝 1) := by
  have hden :
      Tendsto (fun n : ℕ => (1 + 1 / (n : ℝ)) ^ n)
        atTop (𝓝 (Real.exp 1)) := by
    simpa using Real.tendsto_one_add_div_pow_exp 1
  unfold ratioFormula
  convert tendsto_const_nhds.div hden (Real.exp_ne_zero 1) using 1
  field_simp [Real.exp_ne_zero]

theorem gap3 :
    Tendsto
      (fun n : ℕ => |coefficient (n + 1) / coefficient (n + 2)|)
      atTop (𝓝 1) := by
  rw [gap1]
  exact gap2.comp (tendsto_add_atTop_nat 1)

private theorem powerTerm_ratio_tendsto (x : ℝ) :
    Tendsto
      (fun n : ℕ =>
        ‖powerTerm (n + 2) x‖ / ‖powerTerm (n + 1) x‖)
      atTop (𝓝 |x|) := by
  have hrel :
      (fun n : ℕ =>
        ‖powerTerm (n + 2) x‖ / ‖powerTerm (n + 1) x‖) =
        fun n : ℕ =>
          |x| / |coefficient (n + 1) / coefficient (n + 2)| := by
    funext n
    exact powerTerm_ratio x n
  rw [hrel]
  convert tendsto_const_nhds.div gap3 (by norm_num : (1 : ℝ) ≠ 0) using 1
  all_goals norm_num

theorem gap4 :
    HasConvergenceRadiusOne := by
  constructor
  · intro x hx
    by_cases hx0 : x = 0
    · subst x
      unfold SeriesConvergesAt
      apply seriesConverges_of_summable
      simp [powerTerm]
    · unfold SeriesConvergesAt
      apply seriesConverges_of_summable
      apply summable_of_ratio_test_tendsto_lt_one hx
      · exact Filter.Eventually.of_forall (fun n =>
          mul_ne_zero (coefficient_ne_zero _) (pow_ne_zero _ hx0))
      · simpa [Nat.add_assoc] using powerTerm_ratio_tendsto x
  · intro x hx
    unfold SeriesConvergesAt
    apply not_seriesConverges_of_ratio_test_tendsto_gt_one hx
    simpa [Nat.add_assoc] using powerTerm_ratio_tendsto x

theorem gap5 :
    Set.Ioo (-1 : ℝ) 1 ⊆ {x : ℝ | SeriesConvergesAt x} := by
  intro x hx
  exact gap4.1 x ((abs_lt).2 hx)

theorem gap6 :
    (fun k : ℕ => powerTerm (k + 1) (-1)) =
      fun k : ℕ => magnitude (k + 1) := by
  funext k
  unfold powerTerm coefficient
  calc
    (-1 : ℝ) ^ (k + 1) * magnitude (k + 1) * (-1) ^ (k + 1) =
        ((-1 : ℝ) ^ (k + 1)) ^ 2 * magnitude (k + 1) := by ring
    _ = magnitude (k + 1) := by
      rw [pow_two, ← mul_pow]
      norm_num

theorem gap7 :
    Tendsto
      (fun n : ℕ => magnitude (n + 1) / stirlingModel (n + 1))
      atTop (𝓝 1) := by
  have hs :
      Tendsto (fun n : ℕ => Stirling.stirlingSeq (n + 1))
        atTop (𝓝 (Real.sqrt Real.pi)) :=
    Stirling.tendsto_stirlingSeq_sqrt_pi.comp (tendsto_add_atTop_nat 1)
  have hsqrt : Real.sqrt Real.pi ≠ 0 := by positivity
  have hratio :=
    (tendsto_const_nhds (x := Real.sqrt Real.pi)).div hs hsqrt
  convert hratio using 1
  · funext n
    exact magnitude_stirling_identity (n + 1) (by omega)
  · field_simp [hsqrt]

theorem gap8 :
    ∀ n : ℕ, 1 ≤ n →
      stirlingModel n ≥ (1 / (2 * Real.pi)) * (1 / (n : ℝ)) := by
  intro n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have htwo_pi : (1 : ℝ) ≤ 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hA : (1 : ℝ) ≤ 2 * Real.pi * (n : ℝ) := by
    apply htwo_pi.trans
    calc
      2 * Real.pi = (2 * Real.pi) * 1 := by ring
      _ ≤ (2 * Real.pi) * (n : ℝ) :=
        mul_le_mul_of_nonneg_left hnR (by positivity)
  have hsqrt :
      Real.sqrt (2 * Real.pi * (n : ℝ)) ≤
        2 * Real.pi * (n : ℝ) := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · nlinarith
  unfold stirlingModel
  calc
    (1 / (2 * Real.pi)) * (1 / (n : ℝ)) =
        1 / (2 * Real.pi * (n : ℝ)) := by ring
    _ ≤ 1 / Real.sqrt (2 * Real.pi * (n : ℝ)) :=
      one_div_le_one_div_of_le (by positivity) hsqrt

theorem gap9 :
    ∀ n : ℕ, 1 ≤ n →
      (1 / (2 * Real.pi)) * (1 / (n : ℝ)) > 0 := by
  intro n hn
  positivity

theorem gap10 :
    ∀ n : ℕ, 1 ≤ n → stirlingModel n > 0 := by
  intro n hn
  unfold stirlingModel
  positivity

theorem gap11 :
    ¬ Summable (fun k : ℕ => magnitude (k + 1)) := by
  intro hs
  have hevent :
      ∀ᶠ n : ℕ in atTop,
        (1 / 2 : ℝ) ≤
          magnitude (n + 1) / stirlingModel (n + 1) :=
    gap7.eventually_const_le (by norm_num)
  rcases eventually_atTop.1 hevent with ⟨N, hN⟩
  have hsN :
      Summable (fun k : ℕ => magnitude ((N + k) + 1)) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (summable_nat_add_iff N).2 hs
  let c : ℝ := 1 / (4 * Real.pi)
  have hcpos : 0 < c := by
    dsimp [c]
    positivity
  have hg_nonneg :
      ∀ k : ℕ, 0 ≤ c * (1 / (((N + k) + 1 : ℕ) : ℝ)) := by
    intro k
    positivity
  have hg_le :
      ∀ k : ℕ,
        c * (1 / (((N + k) + 1 : ℕ) : ℝ)) ≤
          magnitude ((N + k) + 1) := by
    intro k
    have hm : 1 ≤ (N + k) + 1 := by omega
    have hratio :
        (1 / 2 : ℝ) ≤
          magnitude ((N + k) + 1) /
            stirlingModel ((N + k) + 1) :=
      hN (N + k) (Nat.le_add_right N k)
    have hmodelpos : 0 < stirlingModel ((N + k) + 1) :=
      gap10 ((N + k) + 1) hm
    have hratio_to_mag :
        (1 / 2 : ℝ) * stirlingModel ((N + k) + 1) ≤
          magnitude ((N + k) + 1) := by
      calc
        (1 / 2 : ℝ) * stirlingModel ((N + k) + 1) ≤
            (magnitude ((N + k) + 1) /
                stirlingModel ((N + k) + 1)) *
              stirlingModel ((N + k) + 1) :=
          mul_le_mul_of_nonneg_right hratio hmodelpos.le
        _ = magnitude ((N + k) + 1) := by
          field_simp [hmodelpos.ne']
    calc
      c * (1 / (((N + k) + 1 : ℕ) : ℝ)) =
          (1 / 2 : ℝ) *
            ((1 / (2 * Real.pi)) *
              (1 / (((N + k) + 1 : ℕ) : ℝ))) := by
        dsimp [c]
        ring
      _ ≤ (1 / 2 : ℝ) * stirlingModel ((N + k) + 1) :=
        mul_le_mul_of_nonneg_left
          (gap8 ((N + k) + 1) hm) (by norm_num)
      _ ≤ magnitude ((N + k) + 1) := hratio_to_mag
  have hg :
      Summable
        (fun k : ℕ =>
          c * (1 / (((N + k) + 1 : ℕ) : ℝ))) :=
    Summable.of_nonneg_of_le hg_nonneg hg_le hsN
  have hscaled := hg.mul_left (4 * Real.pi)
  have hharmonic_shift :
      Summable
        (fun k : ℕ => 1 / (((N + k) + 1 : ℕ) : ℝ)) := by
    refine hscaled.congr ?_
    intro k
    dsimp [c]
    field_simp [Real.pi_ne_zero]
  have hharmonic :
      Summable (fun k : ℕ => 1 / (k : ℝ)) := by
    apply (summable_nat_add_iff (N + 1)).1
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      hharmonic_shift
  exact Real.not_summable_one_div_natCast hharmonic

theorem gap12 :
    (fun k : ℕ => powerTerm (k + 1) 1) =
      fun k : ℕ => (-1 : ℝ) ^ (k + 1) * magnitude (k + 1) := by
  funext k
  simp [powerTerm, coefficient]

theorem gap13 :
    Tendsto
      (fun n : ℕ => magnitude (n + 1) / stirlingModel (n + 1))
      atTop (𝓝 1) := by
  exact gap7

theorem gap14 :
    Tendsto magnitude atTop (𝓝 0) := by
  have hcast :
      Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ)))
        atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hmul :
      Tendsto
        (fun n : ℕ => 2 * Real.pi * (((n + 1 : ℕ) : ℝ)))
        atTop atTop :=
    Tendsto.const_mul_atTop (by positivity) hcast
  have hsqrt :
      Tendsto
        (fun n : ℕ =>
          Real.sqrt (2 * Real.pi * (((n + 1 : ℕ) : ℝ))))
        atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hmul
  have hmodel :
      Tendsto (fun n : ℕ => stirlingModel (n + 1))
        atTop (𝓝 0) := by
    simpa [stirlingModel, one_div] using
      tendsto_inv_atTop_zero.comp hsqrt
  have hproduct := gap7.mul hmodel
  have hshift :
      Tendsto (fun n : ℕ => magnitude (n + 1))
        atTop (𝓝 0) := by
    convert hproduct using 1
    · funext n
      have hpos : 0 < stirlingModel (n + 1) :=
        gap10 (n + 1) (by omega)
      field_simp [hpos.ne']
    · norm_num
  exact (tendsto_add_atTop_iff_nat 1).1 hshift

theorem gap15 :
    ∀ n : ℕ, 1 ≤ n →
      |coefficient n / coefficient (n + 1)| = ratioFormula n := by
  exact coefficient_ratio

theorem gap16 :
    ∀ n : ℕ, 1 ≤ n → ratioFormula n > 1 := by
  intro n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hbase :
      1 + 1 / (n : ℝ) < Real.exp (1 / (n : ℝ)) := by
    simpa [add_comm] using Real.add_one_lt_exp (one_div_ne_zero hn0)
  have hpow :
      (1 + 1 / (n : ℝ)) ^ n <
        (Real.exp (1 / (n : ℝ))) ^ n := by
    gcongr
  have hexp :
      (Real.exp (1 / (n : ℝ))) ^ n = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  unfold ratioFormula
  apply (lt_div_iff₀ (pow_pos (by positivity) n)).2
  rw [hexp] at hpow
  simpa using hpow

theorem gap17 :
    ∀ n : ℕ, 1 ≤ n →
      |coefficient n / coefficient (n + 1)| > 1 := by
  intro n hn
  rw [gap15 n hn]
  exact gap16 n hn

theorem gap18 :
    ∀ n : ℕ, 1 ≤ n → |coefficient n| > |coefficient (n + 1)| := by
  intro n hn
  have hden : 0 < |coefficient (n + 1)| :=
    abs_pos.mpr (coefficient_ne_zero _)
  have hratio := gap17 n hn
  rw [abs_div] at hratio
  simpa using (lt_div_iff₀ hden).1 hratio

theorem gap19 :
    ConditionallySummable
      (fun k : ℕ => (-1 : ℝ) ^ (k + 1) * magnitude (k + 1)) := by
  have hanti : Antitone (fun n : ℕ => magnitude (n + 1)) :=
    antitone_nat_of_succ_le fun n => by
      have h := (gap18 (n + 1) (by omega)).le
      simpa [coefficient, abs_mul, abs_pow,
        abs_of_pos (magnitude_pos (n + 1)),
        abs_of_pos (magnitude_pos (n + 2)), Nat.add_assoc] using h
  have hzero : Tendsto (fun n : ℕ => magnitude (n + 1)) atTop (𝓝 0) :=
    gap14.comp (tendsto_add_atTop_nat 1)
  rcases hanti.tendsto_alternating_series_of_tendsto_zero hzero with ⟨l, hl⟩
  have hu :
      (fun k : ℕ => (-1 : ℝ) ^ (k + 1) * magnitude (k + 1)) =
        fun k : ℕ => -((-1 : ℝ) ^ k * magnitude (k + 1)) := by
    funext k
    rw [pow_succ]
    ring
  constructor
  · rw [hu]
    change Summable _ (SummationFilter.conditional ℕ)
    refine ⟨-l, ?_⟩
    rw [HasSum, SummationFilter.conditional_filter_eq_map_range,
      tendsto_map'_iff]
    simpa [Function.comp_def] using hl.neg
  · intro hs
    apply gap11
    refine hs.congr ?_
    intro k
    rw [abs_mul, abs_pow, abs_of_pos (magnitude_pos (k + 1))]
    norm_num

theorem gap20 :
    {x : ℝ | SeriesConvergesAt x} = Set.Ioc (-1 : ℝ) 1 := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_Ioc]
  constructor
  · intro hsum
    have hxlower : (-1 : ℝ) < x := by
      by_contra hx
      have hxle : x ≤ (-1 : ℝ) := le_of_not_gt hx
      rcases hxle.eq_or_lt with hxeq | hxlt
      · subst x
        apply gap11
        apply summable_of_seriesConverges_of_nonneg
          (fun k => (magnitude_pos (k + 1)).le)
        rw [← gap6]
        exact hsum
      · have habs : 1 < |x| := by
          rw [abs_of_neg (by linarith)]
          linarith
        exact (gap4.2 x habs) hsum
    have hxupper : x ≤ (1 : ℝ) := by
      by_contra hx
      have hxgt : (1 : ℝ) < x := lt_of_not_ge hx
      have habs : 1 < |x| := by
        rw [abs_of_pos (by linarith)]
        exact hxgt
      exact (gap4.2 x habs) hsum
    exact ⟨hxlower, hxupper⟩
  · intro hx
    rcases hx.2.eq_or_lt with hxeq | hxlt
    · subst x
      rw [SeriesConvergesAt, gap12]
      exact gap19.1
    · exact gap4.1 x (abs_lt.mpr ⟨hx.1, hxlt⟩)

end

end ProofGap.Exercise2826

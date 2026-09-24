import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries

namespace ProofGap.Exercise2825

noncomputable section

open Filter
open scoped BigOperators Topology

def coefficient (n : ℕ) : ℝ :=
  ((4 : ℝ) ^ n * (Nat.factorial n : ℝ) ^ 2) /
    Nat.factorial (2 * n + 1)

def powerTerm (n : ℕ) (x : ℝ) : ℝ :=
  coefficient n * x ^ n

def SeriesConvergesAt (x : ℝ) : Prop :=
  ProofGap.SeriesConverges (fun k : ℕ => powerTerm (k + 1) x)

def HasConvergenceRadiusOne : Prop :=
  (∀ x : ℝ, |x| < 1 → SeriesConvergesAt x) ∧
    (∀ x : ℝ, 1 < |x| → ¬ SeriesConvergesAt x)

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
    convert (hN (N + n) (Nat.le_add_right N n)).2 using 1 <;> omega
  exact not_tendsto_atTop_of_tendsto_nhds hzeroShift hinfty

def ratioFormula (n : ℕ) : ℝ :=
  ((2 * n + 3 : ℕ) : ℝ) / ((2 * n + 2 : ℕ) : ℝ)

private theorem coefficient_pos (n : ℕ) : 0 < coefficient n := by
  unfold coefficient
  positivity

private theorem coefficient_succ (n : ℕ) :
    coefficient (n + 1) =
      coefficient n *
        (((2 * n + 2 : ℕ) : ℝ) / ((2 * n + 3 : ℕ) : ℝ)) := by
  have hfacn :
      ((Nat.factorial (n + 1) : ℕ) : ℝ) =
        ((n + 1 : ℕ) : ℝ) * (Nat.factorial n : ℝ) := by
    rw [Nat.factorial_succ]
    norm_num
  have hfac2 :
      ((Nat.factorial (2 * (n + 1) + 1) : ℕ) : ℝ) =
        ((2 * n + 3 : ℕ) : ℝ) * ((2 * n + 2 : ℕ) : ℝ) *
          (Nat.factorial (2 * n + 1) : ℝ) := by
    rw [show 2 * (n + 1) + 1 = (2 * n + 2) + 1 by omega,
      Nat.factorial_succ,
      show 2 * n + 2 = (2 * n + 1) + 1 by omega,
      Nat.factorial_succ]
    push_cast
    ring
  unfold coefficient
  rw [hfacn, hfac2]
  have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hf : (0 : ℝ) < (Nat.factorial (2 * n + 1) : ℝ) := by
    positivity
  field_simp [hn1.ne', hf.ne']
  push_cast
  ring

private theorem coefficient_ratio (n : ℕ) :
    |coefficient n| / |coefficient (n + 1)| = ratioFormula n := by
  rw [abs_of_pos (coefficient_pos n),
    abs_of_pos (coefficient_pos (n + 1)), coefficient_succ]
  unfold ratioFormula
  have hc : coefficient n ≠ 0 := (coefficient_pos n).ne'
  have h2 : (((2 * n + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
  have h3 : (((2 * n + 3 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp [hc, h2, h3]

private theorem coefficient_lower (n : ℕ) :
    1 / (((2 * n + 1 : ℕ) : ℝ)) ≤ coefficient n := by
  induction n with
  | zero =>
      norm_num [coefficient]
  | succ n ih =>
      rw [coefficient_succ]
      calc
        1 / (((2 * (n + 1) + 1 : ℕ) : ℝ)) ≤
            (1 / (((2 * n + 1 : ℕ) : ℝ))) *
              (((2 * n + 2 : ℕ) : ℝ) / ((2 * n + 3 : ℕ) : ℝ)) := by
                have h1 : (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) := by
                  positivity
                have h3 : (0 : ℝ) < ((2 * n + 3 : ℕ) : ℝ) := by
                  positivity
                field_simp [h1.ne', h3.ne']
                push_cast
                nlinarith
        _ ≤ coefficient n *
              (((2 * n + 2 : ℕ) : ℝ) / ((2 * n + 3 : ℕ) : ℝ)) := by
          exact mul_le_mul_of_nonneg_right ih (by positivity)

private theorem coefficient_sq_le (n : ℕ) :
    coefficient n ^ 2 ≤ 1 / ((n + 1 : ℕ) : ℝ) := by
  induction n with
  | zero =>
      norm_num [coefficient]
  | succ n ih =>
      rw [coefficient_succ, mul_pow]
      calc
        coefficient n ^ 2 *
              ((((2 * n + 2 : ℕ) : ℝ) / ((2 * n + 3 : ℕ) : ℝ))) ^ 2 ≤
            (1 / ((n + 1 : ℕ) : ℝ)) *
              ((((2 * n + 2 : ℕ) : ℝ) / ((2 * n + 3 : ℕ) : ℝ))) ^ 2 := by
                exact mul_le_mul_of_nonneg_right ih (sq_nonneg _)
        _ ≤ 1 / ((n + 2 : ℕ) : ℝ) := by
          have h1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
          have h2 : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
          have h3 : (0 : ℝ) < ((2 * n + 3 : ℕ) : ℝ) := by positivity
          field_simp [h1.ne', h2.ne', h3.ne']
          push_cast
          nlinarith

private theorem powerTerm_ratio (x : ℝ) (n : ℕ) :
    ‖powerTerm (n + 2) x‖ / ‖powerTerm (n + 1) x‖ =
      |x| / |coefficient (n + 1) / coefficient (n + 2)| := by
  by_cases hx : x = 0
  · subst x
    simp [powerTerm]
  · have hax : |x| ≠ 0 := abs_ne_zero.mpr hx
    have hc1 : coefficient (n + 1) ≠ 0 := (coefficient_pos _).ne'
    have hc2 : coefficient (n + 2) ≠ 0 := (coefficient_pos _).ne'
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    simp only [powerTerm, abs_mul, abs_pow,
      abs_of_pos (coefficient_pos _)]
    rw [abs_of_pos (div_pos (coefficient_pos _) (coefficient_pos _))]
    field_simp [hax, hc1, hc2, pow_ne_zero _ hax]
    ring

theorem gap1 :
    (fun n : ℕ => |coefficient (n + 1) / coefficient (n + 2)|) =
      fun n : ℕ => ratioFormula (n + 1) := by
  funext n
  simpa [abs_div, Nat.add_assoc] using coefficient_ratio (n + 1)

theorem gap2 :
    Tendsto ratioFormula atTop (𝓝 1) := by
  have hn : Tendsto (fun n : ℕ => 2 * n + 2) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop b] with a ha
    omega
  have hc :
      Tendsto (fun n : ℕ => (((2 * n + 2 : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have hinv :
      Tendsto (fun n : ℕ => 1 / (((2 * n + 2 : ℕ) : ℝ)))
        atTop (𝓝 0) := by
    simpa [one_div] using tendsto_inv_atTop_zero.comp hc
  have heq :
      ratioFormula =
        fun n : ℕ => 1 + 1 / (((2 * n + 2 : ℕ) : ℝ)) := by
    funext n
    unfold ratioFormula
    have h : (((2 * n + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
    field_simp [h]
    push_cast
    ring
  rw [heq]
  convert tendsto_const_nhds.add hinv using 1 <;> norm_num

theorem gap3 :
    Tendsto
      (fun n : ℕ => |coefficient (n + 1) / coefficient (n + 2)|)
      atTop (𝓝 1) := by
  rw [gap1]
  exact (tendsto_add_atTop_iff_nat 1).2 gap2

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
  convert tendsto_const_nhds.div gap3 (by norm_num : (1 : ℝ) ≠ 0) using 1 <;>
    norm_num

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
          mul_ne_zero (coefficient_pos _).ne' (pow_ne_zero _ hx0))
      · simpa [Nat.add_assoc] using powerTerm_ratio_tendsto x
  · intro x hx
    unfold SeriesConvergesAt
    apply not_seriesConverges_of_ratio_test_tendsto_gt_one hx
    simpa [Nat.add_assoc] using powerTerm_ratio_tendsto x

theorem gap5 :
    ∀ x : ℝ, |x| < 1 → SeriesConvergesAt x := by
  exact gap4.1

theorem gap6 :
    ¬ Summable (fun k : ℕ => coefficient (k + 1)) := by
  intro hs
  let g : ℕ → ℝ :=
    fun k => (1 / 3 : ℝ) * (1 / ((k + 1 : ℕ) : ℝ))
  have hg_nonneg : ∀ k, 0 ≤ g k := by
    intro k
    dsimp [g]
    positivity
  have hg_le : ∀ k, g k ≤ coefficient (k + 1) := by
    intro k
    calc
      g k ≤ 1 / (((2 * (k + 1) + 1 : ℕ) : ℝ)) := by
        dsimp [g]
        have hk : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
        have hden :
            (0 : ℝ) < ((2 * (k + 1) + 1 : ℕ) : ℝ) := by
          positivity
        field_simp [hk.ne', hden.ne']
        push_cast
        nlinarith
      _ ≤ coefficient (k + 1) := coefficient_lower (k + 1)
  have hg : Summable g :=
    Summable.of_nonneg_of_le hg_nonneg hg_le hs
  have hshift :
      Summable (fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ)) := by
    have hmul := hg.mul_left (3 : ℝ)
    refine hmul.congr ?_
    intro k
    dsimp [g]
    field_simp
  have hall : Summable (fun k : ℕ => 1 / (k : ℝ)) :=
    (summable_nat_add_iff 1).1 hshift
  exact Real.not_summable_one_div_natCast hall

theorem gap7 :
    ∀ n : ℕ,
      |coefficient n| / |coefficient (n + 1)| = ratioFormula n := by
  exact coefficient_ratio

theorem gap8 :
    ∀ n : ℕ, ratioFormula n > 1 := by
  intro n
  unfold ratioFormula
  have hden : (0 : ℝ) < ((2 * n + 2 : ℕ) : ℝ) := by positivity
  apply (lt_div_iff₀ hden).2
  push_cast
  linarith

theorem gap9 :
    ∀ n : ℕ,
      |coefficient n| / |coefficient (n + 1)| > 1 := by
  intro n
  rw [gap7 n]
  exact gap8 n

theorem gap10 :
    ∀ n : ℕ, |coefficient n| > |coefficient (n + 1)| := by
  intro n
  have hden : 0 < |coefficient (n + 1)| :=
    abs_pos.mpr (coefficient_pos (n + 1)).ne'
  simpa using (lt_div_iff₀ hden).1 (gap9 n)

theorem gap11 :
    Tendsto coefficient atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => n + 1) atTop atTop :=
    (tendsto_add_atTop_iff_nat 1).2 tendsto_id
  have hc :
      Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have hinv :
      Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ))
        atTop (𝓝 0) := by
    simpa [one_div] using tendsto_inv_atTop_zero.comp hc
  have hsqrt :
      Tendsto (fun n : ℕ => Real.sqrt (1 / ((n + 1 : ℕ) : ℝ)))
        atTop (𝓝 0) := by
    convert (Real.continuous_sqrt.tendsto 0).comp hinv using 1 <;>
      simp only [Real.sqrt_zero]
  apply squeeze_zero (fun n => (coefficient_pos n).le) _ hsqrt
  intro n
  exact
    (Real.le_sqrt (coefficient_pos n).le (by positivity)).2
      (coefficient_sq_le n)

theorem gap12 :
    ProofGap.SeriesConverges
      (fun k : ℕ => (-1 : ℝ) ^ (k + 1) * coefficient (k + 1)) := by
  have hantiCoefficient : Antitone coefficient :=
    antitone_nat_of_succ_le fun n => by
      have h := (gap10 n).le
      simpa [abs_of_pos (coefficient_pos n), abs_of_pos (coefficient_pos (n + 1))] using h
  have hanti : Antitone (fun n : ℕ => coefficient (n + 1)) := by
    intro m n hmn
    exact hantiCoefficient (Nat.add_le_add_right hmn 1)
  have hzero : Tendsto (fun n : ℕ => coefficient (n + 1)) atTop (𝓝 0) :=
    gap11.comp (tendsto_add_atTop_nat 1)
  rcases hanti.tendsto_alternating_series_of_tendsto_zero hzero with ⟨l, hl⟩
  have hu :
      (fun k : ℕ => (-1 : ℝ) ^ (k + 1) * coefficient (k + 1)) =
        fun k : ℕ => -((-1 : ℝ) ^ k * coefficient (k + 1)) := by
    funext k
    rw [pow_succ]
    ring
  rw [hu]
  change Summable _ (SummationFilter.conditional ℕ)
  refine ⟨-l, ?_⟩
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range,
    tendsto_map'_iff]
  simpa [Function.comp_def] using hl.neg

theorem gap13 :
    ConditionallySummable
      (fun k : ℕ => (-1 : ℝ) ^ (k + 1) * coefficient (k + 1)) := by
  refine ⟨gap12, ?_⟩
  intro hs
  apply gap6
  refine hs.congr ?_
  intro k
  rw [abs_mul, abs_pow, abs_of_pos (coefficient_pos (k + 1))]
  norm_num

theorem gap14 :
    ∀ x : ℝ, x ∈ Set.Ico (-1 : ℝ) 1 ↔ SeriesConvergesAt x := by
  intro x
  constructor
  · intro hx
    rcases hx.1.eq_or_lt with hxeq | hxneg
    · subst x
      simpa [SeriesConvergesAt, powerTerm, mul_comm] using gap12
    · exact gap5 x (abs_lt.mpr ⟨hxneg, hx.2⟩)
  · intro hsum
    have hxlower : (-1 : ℝ) ≤ x := by
      by_contra hx
      have hxlt : x < -1 := lt_of_not_ge hx
      have habs : 1 < |x| := by
        rw [abs_of_neg (by linarith)]
        linarith
      exact (gap4.2 x habs) hsum
    have hxupper : x < (1 : ℝ) := by
      by_contra hx
      have hxge : (1 : ℝ) ≤ x := le_of_not_gt hx
      rcases hxge.eq_or_lt with hxeq | hxgt
      · subst x
        apply gap6
        apply summable_of_seriesConverges_of_nonneg
          (fun k => (coefficient_pos (k + 1)).le)
        simpa [SeriesConvergesAt, powerTerm] using hsum
      · have habs : 1 < |x| := by
          rw [abs_of_pos (by linarith)]
          exact hxgt
        exact (gap4.2 x habs) hsum
    exact ⟨hxlower, hxupper⟩

end

end ProofGap.Exercise2825

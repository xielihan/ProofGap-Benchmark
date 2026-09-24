import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries

namespace ProofGap.Exercise2686

noncomputable section

open Filter
open scoped BigOperators

def weight (n : ℕ) : ℝ :=
  1 / Real.log (n + 2)

def partialSin (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 2 N, Real.sin ((m : ℝ) * Real.pi / 12)

def sinTerm (n : ℕ) : ℝ :=
  Real.sin (((n + 2 : ℕ) : ℝ) * Real.pi / 12) /
    Real.log (n + 2)

def cosTerm (n : ℕ) : ℝ :=
  Real.cos (((n + 2 : ℕ) : ℝ) * Real.pi / 6) /
    Real.log (n + 2)

def ConditionallySummable (f : ℕ → ℝ) : Prop :=
  ProofGap.SeriesConverges f ∧
    ¬ Summable (fun n => |f n|)

private lemma log_shift_pos (n : ℕ) :
    0 < Real.log ((n : ℝ) + 2) := by
  apply Real.log_pos
  exact_mod_cast (show 1 < n + 2 by omega)

private lemma sin_pi_div_twenty_four_pos :
    0 < Real.sin (Real.pi / 24) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · nlinarith [Real.pi_pos]

private lemma sin_telescope (m : ℕ) :
    Real.sin ((m : ℝ) * Real.pi / 12) =
      (Real.cos (((m : ℝ) - 1 / 2) * Real.pi / 12) -
        Real.cos (((m : ℝ) + 1 / 2) * Real.pi / 12)) /
        (2 * Real.sin (Real.pi / 24)) := by
  have hden : 2 * Real.sin (Real.pi / 24) ≠ 0 :=
    mul_ne_zero (by norm_num) sin_pi_div_twenty_four_pos.ne'
  apply (eq_div_iff hden).2
  rw [Real.cos_sub_cos]
  have hsum :
      ((((m : ℝ) - 1 / 2) * Real.pi / 12 +
          ((m : ℝ) + 1 / 2) * Real.pi / 12) / 2) =
        (m : ℝ) * Real.pi / 12 := by ring
  have hdiff :
      ((((m : ℝ) - 1 / 2) * Real.pi / 12 -
          ((m : ℝ) + 1 / 2) * Real.pi / 12) / 2) =
        -(Real.pi / 24) := by ring
  rw [hsum, hdiff, Real.sin_neg]
  ring

private lemma sum_range_sin_eq_partialSin (n : ℕ) :
    (∑ i ∈ Finset.range n,
      Real.sin (((i + 2 : ℕ) : ℝ) * Real.pi / 12)) =
      partialSin (n + 1) := by
  induction n with
  | zero => simp [partialSin]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      unfold partialSin
      rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ n + 2)]

private lemma sin_pi_div_twelve_pos :
    0 < Real.sin (Real.pi / 12) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · nlinarith [Real.pi_pos]

private lemma cos_telescope (m : ℕ) :
    Real.cos ((m : ℝ) * Real.pi / 6) =
      (Real.sin (((m : ℝ) + 1 / 2) * Real.pi / 6) -
        Real.sin (((m : ℝ) - 1 / 2) * Real.pi / 6)) /
        (2 * Real.sin (Real.pi / 12)) := by
  have hden : 2 * Real.sin (Real.pi / 12) ≠ 0 :=
    mul_ne_zero (by norm_num) sin_pi_div_twelve_pos.ne'
  apply (eq_div_iff hden).2
  rw [Real.sin_sub_sin]
  have hdiff :
      ((((m : ℝ) + 1 / 2) * Real.pi / 6 -
          ((m : ℝ) - 1 / 2) * Real.pi / 6) / 2) =
        Real.pi / 12 := by ring
  have hsum :
      ((((m : ℝ) + 1 / 2) * Real.pi / 6 +
          ((m : ℝ) - 1 / 2) * Real.pi / 6) / 2) =
        (m : ℝ) * Real.pi / 6 := by ring
  rw [hdiff, hsum]
  ring

private lemma sum_range_cos_eq (n : ℕ) :
    (∑ i ∈ Finset.range n,
      Real.cos (((i + 2 : ℕ) : ℝ) * Real.pi / 6)) =
      (Real.sin (((n : ℝ) + 3 / 2) * Real.pi / 6) -
        Real.sin ((3 / 2 : ℝ) * Real.pi / 6)) /
        (2 * Real.sin (Real.pi / 12)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, cos_telescope (n + 2)]
      have hden : 2 * Real.sin (Real.pi / 12) ≠ 0 :=
        mul_ne_zero (by norm_num) sin_pi_div_twelve_pos.ne'
      field_simp [hden]
      push_cast
      ring

private lemma seriesConverges_of_cauchySeq_range {f : ℕ → ℝ}
    (hf : CauchySeq fun n => ∑ i ∈ Finset.range n, f i) :
    ProofGap.SeriesConverges f := by
  rcases cauchySeq_tendsto_of_complete hf with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  change Tendsto (fun s : Finset ℕ => ∑ i ∈ s, f i)
    (SummationFilter.conditional ℕ).filter (nhds a)
  simpa only [SummationFilter.conditional_filter_eq_map_range,
    tendsto_map'_iff, Function.comp_apply] using ha

private lemma seriesConverges_of_summable {f : ℕ → ℝ}
    (hf : Summable f) : ProofGap.SeriesConverges f := by
  exact seriesConverges_of_cauchySeq_range hf.hasSum.tendsto_sum_nat.cauchySeq

private lemma summable_of_seriesConverges_of_nonneg {f : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) (h : ProofGap.SeriesConverges f) : Summable f := by
  rcases h with ⟨a, ha⟩
  refine ⟨a, (hasSum_iff_tendsto_nat_of_nonneg hf a).2 ?_⟩
  change Tendsto (fun s : Finset ℕ => ∑ i ∈ s, f i)
    (SummationFilter.conditional ℕ).filter (nhds a) at ha
  simpa only [SummationFilter.conditional_filter_eq_map_range,
    tendsto_map'_iff, Function.comp_apply] using ha

theorem gap1 :
    Tendsto weight atTop (nhds 0) := by
  have harg : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  change Tendsto (fun n : ℕ => 1 / Real.log ((n : ℝ) + 2)) atTop (nhds 0)
  simpa only [one_div, Function.comp_apply] using
    tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp harg)

theorem gap2 :
    Antitone weight := by
  intro a b hab
  unfold weight
  apply one_div_le_one_div_of_le (log_shift_pos a)
  exact Real.strictMonoOn_log.monotoneOn
    (Set.mem_Ioi.mpr (by positivity))
    (Set.mem_Ioi.mpr (by positivity))
    (by exact_mod_cast Nat.add_le_add_right hab 2)

theorem gap3 :
    ∀ N : ℕ, 2 ≤ N →
      partialSin N =
        (Real.cos (Real.pi / 8) -
          Real.cos (((N : ℝ) + 1 / 2) * Real.pi / 12)) /
          (2 * Real.sin (Real.pi / 24)) := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base =>
      rw [partialSin, show Finset.Icc 2 2 = {2} by ext x; simp]
      simp only [Finset.sum_singleton]
      convert sin_telescope 2 using 1 <;> ring
  | succ N hN ih =>
      unfold partialSin at ih ⊢
      rw [Finset.sum_Icc_succ_top (by omega), ih, sin_telescope (N + 1)]
      have hden : 2 * Real.sin (Real.pi / 24) ≠ 0 :=
        mul_ne_zero (by norm_num) sin_pi_div_twenty_four_pos.ne'
      field_simp [hden]
      push_cast
      ring

theorem gap4 :
    ∀ N : ℕ,
      |(Real.cos (Real.pi / 8) -
          Real.cos (((N : ℝ) + 1 / 2) * Real.pi / 12)) /
          (2 * Real.sin (Real.pi / 24))| ≤
        1 / Real.sin (Real.pi / 24) := by
  intro N
  have hs := sin_pi_div_twenty_four_pos
  have hnum :
      |Real.cos (Real.pi / 8) -
        Real.cos (((N : ℝ) + 1 / 2) * Real.pi / 12)| ≤ 2 := by
    calc
      |Real.cos (Real.pi / 8) -
          Real.cos (((N : ℝ) + 1 / 2) * Real.pi / 12)|
          ≤ |Real.cos (Real.pi / 8)| +
              |Real.cos (((N : ℝ) + 1 / 2) * Real.pi / 12)| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add (Real.abs_cos_le_one _) (Real.abs_cos_le_one _)
      _ = 2 := by norm_num
  rw [abs_div, abs_of_pos (mul_pos (by norm_num) hs)]
  apply (div_le_div_iff₀ (mul_pos (by norm_num) hs) hs).2
  nlinarith

theorem gap5 :
    ∀ N : ℕ, 2 ≤ N →
      |partialSin N| ≤ 1 / Real.sin (Real.pi / 24) := by
  intro N hN
  rw [gap3 N hN]
  exact gap4 N

theorem gap6 :
    ∃ C : ℝ, ∀ N : ℕ, |partialSin N| ≤ C := by
  refine ⟨1 / Real.sin (Real.pi / 24), fun N => ?_⟩
  by_cases hN : 2 ≤ N
  · exact gap5 N hN
  · have hsmall : N = 0 ∨ N = 1 := by omega
    rcases hsmall with rfl | rfl <;>
      simp [partialSin, le_of_lt sin_pi_div_twenty_four_pos]

theorem gap7 :
    ProofGap.SeriesConverges sinTerm := by
  obtain ⟨C, hC⟩ := gap6
  have hbound : ∀ n,
      ‖∑ i ∈ Finset.range n,
        Real.sin (((i + 2 : ℕ) : ℝ) * Real.pi / 12)‖ ≤ C := by
    intro n
    rw [Real.norm_eq_abs, sum_range_sin_eq_partialSin]
    exact hC (n + 1)
  have hcauchy := gap2.cauchySeq_series_mul_of_tendsto_zero_of_bounded
    gap1 hbound
  apply seriesConverges_of_cauchySeq_range
  convert hcauchy using 1
  funext n
  apply Finset.sum_congr rfl
  intro i hi
  simp only [sinTerm, weight, one_div, smul_eq_mul]
  ring

theorem gap8 :
    ∀ n : ℕ,
      |sinTerm n| ≥
        Real.sin (((n + 2 : ℕ) : ℝ) * Real.pi / 12) ^ 2 /
          Real.log (n + 2) := by
  intro n
  have hlog := log_shift_pos n
  unfold sinTerm
  rw [abs_div, abs_of_pos hlog]
  apply (div_le_div_iff_of_pos_right hlog).2
  have habs := Real.abs_sin_le_one (((n + 2 : ℕ) : ℝ) * Real.pi / 12)
  have hnonneg := abs_nonneg (Real.sin (((n + 2 : ℕ) : ℝ) * Real.pi / 12))
  rw [← sq_abs]
  nlinarith

theorem gap9 :
    ∀ n : ℕ,
      Real.sin (((n + 2 : ℕ) : ℝ) * Real.pi / 12) ^ 2 /
          Real.log (n + 2) =
        (1 - Real.cos (((n + 2 : ℕ) : ℝ) * Real.pi / 6)) /
          (2 * Real.log (n + 2)) := by
  intro n
  have hlog := log_shift_pos n
  let x : ℝ := ((n + 2 : ℕ) : ℝ) * Real.pi / 12
  have harg : (((n + 2 : ℕ) : ℝ) * Real.pi / 6) = 2 * x := by
    dsimp [x]
    ring
  rw [harg, Real.cos_two_mul]
  have htrig := Real.sin_sq_add_cos_sq x
  change Real.sin x ^ 2 / Real.log (n + 2) =
    (1 - (2 * Real.cos x ^ 2 - 1)) / (2 * Real.log (n + 2))
  field_simp [hlog.ne']
  nlinarith

theorem gap10 :
    ∀ n : ℕ,
      (1 - Real.cos (((n + 2 : ℕ) : ℝ) * Real.pi / 6)) /
          (2 * Real.log (n + 2)) =
        1 / (2 * Real.log (n + 2)) -
          Real.cos (((n + 2 : ℕ) : ℝ) * Real.pi / 6) /
            (2 * Real.log (n + 2)) := by
  intro n
  have hlog := log_shift_pos n
  field_simp [hlog.ne']

theorem gap11 :
    ∀ n : ℕ,
      |sinTerm n| ≥
        1 / (2 * Real.log (n + 2)) -
          Real.cos (((n + 2 : ℕ) : ℝ) * Real.pi / 6) /
            (2 * Real.log (n + 2)) := by
  intro n
  calc
    |sinTerm n| ≥
        Real.sin (((n + 2 : ℕ) : ℝ) * Real.pi / 12) ^ 2 /
          Real.log (n + 2) := gap8 n
    _ = (1 - Real.cos (((n + 2 : ℕ) : ℝ) * Real.pi / 6)) /
          (2 * Real.log (n + 2)) := gap9 n
    _ = 1 / (2 * Real.log (n + 2)) -
          Real.cos (((n + 2 : ℕ) : ℝ) * Real.pi / 6) /
            (2 * Real.log (n + 2)) := gap10 n

theorem gap12 :
    ¬ Summable weight := by
  intro hw'
  have hharm : ¬ Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ))) := by
    intro h
    apply Real.not_summable_one_div_natCast
    exact (summable_nat_add_iff 1).1 (by simpa using h)
  apply hharm
  apply hw'.of_nonneg_of_le (fun _ => by positivity)
  intro n
  unfold weight
  apply one_div_le_one_div_of_le (log_shift_pos n)
  have h := Real.log_le_sub_one_of_pos (show 0 < (((n + 2 : ℕ) : ℝ)) by positivity)
  norm_num [Nat.cast_add, Nat.cast_one] at h ⊢
  linarith

theorem gap13 :
    ProofGap.SeriesConverges cosTerm := by
  have hbound : ∀ n,
      ‖∑ i ∈ Finset.range n,
        Real.cos (((i + 2 : ℕ) : ℝ) * Real.pi / 6)‖ ≤
        1 / Real.sin (Real.pi / 12) := by
    intro n
    rw [Real.norm_eq_abs, sum_range_cos_eq, abs_div,
      abs_of_pos (mul_pos (by norm_num) sin_pi_div_twelve_pos)]
    have hnum :
        |Real.sin (((n : ℝ) + 3 / 2) * Real.pi / 6) -
          Real.sin ((3 / 2 : ℝ) * Real.pi / 6)| ≤ 2 := by
      calc
        |Real.sin (((n : ℝ) + 3 / 2) * Real.pi / 6) -
            Real.sin ((3 / 2 : ℝ) * Real.pi / 6)|
            ≤ |Real.sin (((n : ℝ) + 3 / 2) * Real.pi / 6)| +
                |Real.sin ((3 / 2 : ℝ) * Real.pi / 6)| := abs_sub _ _
        _ ≤ 1 + 1 := add_le_add (Real.abs_sin_le_one _) (Real.abs_sin_le_one _)
        _ = 2 := by norm_num
    apply (div_le_div_iff₀
      (mul_pos (by norm_num) sin_pi_div_twelve_pos)
      sin_pi_div_twelve_pos).2
    have hmul := mul_le_mul_of_nonneg_right hnum sin_pi_div_twelve_pos.le
    nlinarith
  have hcauchy := gap2.cauchySeq_series_mul_of_tendsto_zero_of_bounded
    gap1 hbound
  apply seriesConverges_of_cauchySeq_range
  convert hcauchy using 1
  funext n
  apply Finset.sum_congr rfl
  intro i hi
  simp only [cosTerm, weight, one_div, smul_eq_mul]
  ring

theorem gap14 :
    ¬ Summable (fun n : ℕ => |sinTerm n|) := by
  intro habs'
  let lower : ℕ → ℝ := fun n =>
    1 / (2 * Real.log (n + 2)) -
      Real.cos (((n + 2 : ℕ) : ℝ) * Real.pi / 6) /
        (2 * Real.log (n + 2))
  have hlower_nonneg : ∀ n, 0 ≤ lower n := by
    intro n
    dsimp [lower]
    rw [← gap10 n, ← gap9 n]
    exact div_nonneg (sq_nonneg _) (log_shift_pos n).le
  have hlower_le : ∀ n, lower n ≤ |sinTerm n| := by
    intro n
    exact gap11 n
  have hlower_sum : Summable lower :=
    habs'.of_nonneg_of_le hlower_nonneg hlower_le
  have hlower_series : ProofGap.SeriesConverges lower :=
    seriesConverges_of_summable hlower_sum
  have hweight : ProofGap.SeriesConverges weight := by
    have h := (hlower_series.mul_left 2).add gap13
    change Summable weight (SummationFilter.conditional ℕ)
    apply h.congr
    intro n
    dsimp [lower, weight, cosTerm]
    have hlog := log_shift_pos n
    field_simp [hlog.ne']
    ring
  apply gap12
  exact summable_of_seriesConverges_of_nonneg
    (fun n => one_div_nonneg.mpr (log_shift_pos n).le) hweight

theorem gap15 :
    ConditionallySummable sinTerm := by
  exact ⟨gap7, gap14⟩

end

end ProofGap.Exercise2686

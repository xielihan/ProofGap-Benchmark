import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2668

noncomputable section

open Filter
open scoped BigOperators

def originalTerm (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * Real.sin n ^ 2 / n

def alternatingTerm (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n / (2 * n : ℝ)

def oscillatoryTerm (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) * Real.cos (2 * n) / (2 * n : ℝ)

def positiveCosTerm (n : ℕ) : ℝ :=
  Real.cos (2 * n) / (2 * n : ℝ)

def evenCorrection (n : ℕ) : ℝ :=
  Real.cos (4 * n) / (2 * n : ℝ)

def partialOscillatory (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, oscillatoryTerm n

def partialPositive (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, positiveCosTerm n

def partialEven (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 (N / 2), evenCorrection n

def S1 (N : ℕ) : ℝ := partialPositive N
def S2 (N : ℕ) : ℝ := partialEven N

private theorem seriesConverges_of_tendsto {f : ℕ → ℝ} {s : ℝ}
    (h : Tendsto (fun N => ∑ n ∈ Finset.range N, f n) atTop (nhds s)) :
    ProofGap.SeriesConverges f := by
  unfold ProofGap.SeriesConverges Summable
  refine ⟨s, ?_⟩
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range,
    Filter.tendsto_map'_iff]
  simpa [Function.comp_def] using h

private theorem seriesConverges_iff_tendsto {f : ℕ → ℝ} :
    ProofGap.SeriesConverges f ↔
      ∃ s, Tendsto (fun N => ∑ n ∈ Finset.range N, f n) atTop (nhds s) := by
  constructor
  · intro h
    unfold ProofGap.SeriesConverges Summable at h
    rcases h with ⟨s, hs⟩
    refine ⟨s, ?_⟩
    rw [HasSum, SummationFilter.conditional_filter_eq_map_range,
      Filter.tendsto_map'_iff] at hs
    simpa [Function.comp_def] using hs
  · rintro ⟨s, hs⟩
    exact seriesConverges_of_tendsto hs

private theorem sum_shift_eq_Icc (f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, f (n + 1)) = ∑ n ∈ Finset.Icc 1 N, f n := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]

private theorem alternating_not_unconditionally_summable :
    ¬ Summable (fun n : ℕ => alternatingTerm (n + 1)) := by
  intro h
  have hnorm : Summable (fun n : ℕ => ‖alternatingTerm (n + 1)‖) := h.norm
  have hhalf : Summable (fun n : ℕ => 1 / (2 * ((n : ℝ) + 1))) := by
    convert hnorm using 1
    funext n
    simp [alternatingTerm, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n + 1)]
  have hshift : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1)) :=
    (hhalf.mul_left (2 : ℝ)).congr fun n => by
      simp only [one_div, mul_inv_rev]
      ring_nf
  apply Real.not_summable_one_div_natCast
  apply (summable_nat_add_iff 1).1
  simpa [Nat.cast_add] using hshift

private def unitStep (a : ℝ) : ℂ := Complex.exp (a * Complex.I)

private theorem unitStep_norm (a : ℝ) : ‖unitStep a‖ = 1 := by
  simp [unitStep, Complex.exp_ofReal_mul_I]

private theorem unitStep_ne_one {a : ℝ} (ha0 : 0 < a) (ha2pi : a < 2 * Real.pi) :
    unitStep a ≠ 1 := by
  intro h
  have hre := congrArg Complex.re h
  have hcos : Real.cos a = 1 := by
    simpa [unitStep, Complex.exp_ofReal_mul_I] using hre
  have ha : a = 0 :=
    (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [Real.pi_pos]) ha2pi).1 hcos
  linarith

private theorem unitStep_pow_re (a : ℝ) (n : ℕ) :
    (unitStep a ^ n).re = Real.cos ((n : ℝ) * a) := by
  rw [unitStep, ← Complex.exp_nat_mul]
  have harg :
      (n : ℂ) * ((a : ℂ) * Complex.I) =
        (((n : ℝ) * a : ℝ) : ℂ) * Complex.I := by
    rw [← mul_assoc]
    norm_num
  rw [harg, Complex.exp_ofReal_mul_I_re]

private theorem cos_partial_sum_bounded {a : ℝ} (ha0 : 0 < a) (ha2pi : a < 2 * Real.pi) :
    ∃ b : ℝ, ∀ N : ℕ,
      ‖∑ n ∈ Finset.range N, Real.cos (a * (n + 1))‖ ≤ b := by
  let q := unitStep a
  have hqnorm : ‖q‖ = 1 := unitStep_norm a
  have hqne : q ≠ 1 := unitStep_ne_one ha0 ha2pi
  have hden : 0 < ‖q - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hqne)
  refine ⟨2 / ‖q - 1‖, ?_⟩
  intro N
  have hgeom :
      (∑ n ∈ Finset.range N, q ^ n) * (q - 1) = q ^ N - 1 :=
    geom_sum_mul q N
  have hright : ‖q ^ N - 1‖ ≤ 2 := by
    calc
      ‖q ^ N - 1‖ ≤ ‖q ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hqnorm, one_pow, norm_one]; norm_num
  have hsum : ‖∑ n ∈ Finset.range N, q ^ n‖ ≤ 2 / ‖q - 1‖ := by
    rw [le_div_iff₀ hden]
    rw [← norm_mul, hgeom]
    exact hright
  calc
    ‖∑ n ∈ Finset.range N, Real.cos (a * (n + 1))‖ =
        |∑ n ∈ Finset.range N, Real.cos (a * (n + 1))| := Real.norm_eq_abs _
    _ = |(∑ n ∈ Finset.range N, q ^ (n + 1)).re| := by
      congr 1
      rw [Complex.re_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [unitStep_pow_re]
      rw [show (((n + 1 : ℕ) : ℝ) * a) = a * (n + 1) by
        norm_num; ring]
    _ ≤ ‖∑ n ∈ Finset.range N, q ^ (n + 1)‖ := Complex.abs_re_le_norm _
    _ = ‖q * ∑ n ∈ Finset.range N, q ^ n‖ := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [pow_succ']
    _ = ‖∑ n ∈ Finset.range N, q ^ n‖ := by rw [norm_mul, hqnorm, one_mul]
    _ ≤ 2 / ‖q - 1‖ := hsum

private theorem cos_div_seriesConverges {a : ℝ} (ha0 : 0 < a)
    (ha2pi : a < 2 * Real.pi) :
    ProofGap.SeriesConverges
      (fun n : ℕ => Real.cos (a * (n + 1)) / (2 * (n + 1) : ℝ)) := by
  let f : ℕ → ℝ := fun n => 1 / (2 * ((n : ℝ) + 1))
  have hfanti : Antitone f := by
    intro m n hmn
    dsimp [f]
    gcongr
  have hfzero : Tendsto f atTop (nhds 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 2 : ℝ)
    simpa [f, div_eq_mul_inv, mul_comm] using h
  rcases cos_partial_sum_bounded ha0 ha2pi with ⟨b, hb⟩
  have hcauchy : CauchySeq
      (fun N => ∑ n ∈ Finset.range N,
        f n • Real.cos (a * (n + 1))) :=
    hfanti.cauchySeq_series_mul_of_tendsto_zero_of_bounded hfzero hb
  rcases cauchySeq_tendsto_of_complete hcauchy with ⟨s, hs⟩
  apply seriesConverges_of_tendsto (s := s)
  convert hs using 1
  funext N
  apply Finset.sum_congr rfl
  intro n hn
  dsimp [f]
  ring

theorem gap1 :
    ∀ n : ℕ, 1 ≤ n →
      originalTerm n = alternatingTerm n + oscillatoryTerm n := by
  intro n hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  rw [originalTerm, alternatingTerm, oscillatoryTerm, Real.sin_sq_eq_half_sub,
    pow_succ]
  field_simp [hn0]
  ring

theorem gap2 :
    ProofGap.SeriesConverges (fun n : ℕ => alternatingTerm (n + 1)) := by
  let f : ℕ → ℝ := fun n => 1 / (2 * ((n : ℝ) + 1))
  have hfanti : Antitone f := by
    intro m n hmn
    dsimp [f]
    gcongr
  have hfzero : Tendsto f atTop (nhds 0) := by
    have h :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 2 : ℝ)
    simpa [f, div_eq_mul_inv, mul_comm] using h
  rcases hfanti.tendsto_alternating_series_of_tendsto_zero hfzero with ⟨s, hs⟩
  apply seriesConverges_of_tendsto (s := -s)
  convert hs.neg using 1
  funext N
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  dsimp [f]
  rw [alternatingTerm, pow_succ]
  have hn0 : ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp [hn0]
  norm_num [Nat.cast_add]

theorem gap3 :
    ∀ N : ℕ,
      partialOscillatory N =
        ∑ n ∈ Finset.Icc 1 N, oscillatoryTerm n := by
  intro N
  rfl

theorem gap4 :
    ∀ N : ℕ,
      partialOscillatory N = partialPositive N - partialEven N := by
  intro N
  induction N with
  | zero => simp [partialOscillatory, partialPositive, partialEven]
  | succ N ih =>
      have hosc :
          partialOscillatory (N + 1) =
            partialOscillatory N + oscillatoryTerm (N + 1) := by
        unfold partialOscillatory
        rw [Finset.sum_Icc_succ_top (by omega)]
      have hpos :
          partialPositive (N + 1) =
            partialPositive N + positiveCosTerm (N + 1) := by
        unfold partialPositive
        rw [Finset.sum_Icc_succ_top (by omega)]
      rw [hosc, hpos, ih]
      rcases Nat.even_or_odd' N with ⟨k, hk | hk⟩
      · subst N
        have heven : partialEven (2 * k + 1) = partialEven (2 * k) := by
          have hdiv1 : (2 * k + 1) / 2 = k := by omega
          have hdiv0 : (2 * k) / 2 = k := by omega
          simp only [partialEven, hdiv1, hdiv0]
        have hterm :
            oscillatoryTerm (2 * k + 1) = positiveCosTerm (2 * k + 1) := by
          rw [oscillatoryTerm, positiveCosTerm]
          norm_num [pow_add, pow_mul]
        rw [heven, hterm]
        ring
      · subst N
        have heven :
            partialEven (2 * k + 1 + 1) =
              partialEven (2 * k + 1) + evenCorrection (k + 1) := by
          have hdiv1 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
          have hdiv0 : (2 * k + 1) / 2 = k := by omega
          unfold partialEven
          rw [hdiv1, hdiv0, Finset.sum_Icc_succ_top (by omega)]
        have hterm :
            oscillatoryTerm (2 * k + 1 + 1) =
              positiveCosTerm (2 * k + 1 + 1) - evenCorrection (k + 1) := by
          rw [oscillatoryTerm, positiveCosTerm, evenCorrection]
          norm_num [pow_add, pow_mul]
          have hk0 : ((k : ℝ) + 1) ≠ 0 := by positivity
          field_simp [hk0]
          ring
        rw [heven, hterm]
        ring

theorem gap5 :
    ∀ N : ℕ,
      partialPositive N - partialEven N =
        S1 N - S2 N := by
  intro N
  rfl

theorem gap6 :
    ∀ N : ℕ,
      partialOscillatory N = S1 N - S2 N := by
  intro N
  rw [gap4 N, gap5 N]

theorem gap7 :
    ProofGap.SeriesConverges (fun n : ℕ => positiveCosTerm (n + 1)) := by
  have hpi : (2 : ℝ) < 2 * Real.pi := by linarith [Real.pi_gt_three]
  simpa [positiveCosTerm] using
    (cos_div_seriesConverges (a := (2 : ℝ)) (by norm_num) hpi)

theorem gap8 :
    ProofGap.SeriesConverges (fun n : ℕ => evenCorrection (n + 1)) := by
  have hpi : (4 : ℝ) < 2 * Real.pi := by linarith [Real.pi_gt_three]
  simpa [evenCorrection] using
    (cos_div_seriesConverges (a := (4 : ℝ)) (by norm_num) hpi)

theorem gap9 :
    ∃ s : ℝ, Tendsto partialOscillatory atTop (nhds s) := by
  rcases seriesConverges_iff_tendsto.mp gap7 with ⟨s1, hs1⟩
  rcases seriesConverges_iff_tendsto.mp gap8 with ⟨s2, hs2⟩
  have hp : Tendsto partialPositive atTop (nhds s1) := by
    convert hs1 using 1
    funext N
    simpa [partialPositive] using (sum_shift_eq_Icc positiveCosTerm N).symm
  have he : Tendsto partialEven atTop (nhds s2) := by
    have hs2' := hs2.comp (Nat.tendsto_div_const_atTop (by norm_num : (2 : ℕ) ≠ 0))
    convert hs2' using 1
    funext N
    simpa [partialEven] using (sum_shift_eq_Icc evenCorrection (N / 2)).symm
  refine ⟨s1 - s2, ?_⟩
  convert hp.sub he using 1
  funext N
  exact gap4 N

theorem gap10 :
    ProofGap.SeriesConverges (fun n : ℕ => oscillatoryTerm (n + 1)) := by
  rcases gap9 with ⟨s, hs⟩
  apply seriesConverges_of_tendsto (s := s)
  convert hs using 1
  funext N
  exact sum_shift_eq_Icc oscillatoryTerm N

theorem gap11 :
    ProofGap.SeriesConverges (fun n : ℕ => originalTerm (n + 1)) := by
  have hsum := gap2.add gap10
  apply hsum.congr
  intro n
  exact (gap1 (n + 1) (by omega)).symm

end

end ProofGap.Exercise2668

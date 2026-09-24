import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter

namespace ProofGap.Exercise2676

noncomputable section

open Filter

def magnitude (p : ℝ) (n : ℕ) : ℝ :=
  1 / Real.rpow n (p + 1 / n)

def baseMagnitude (p : ℝ) (n : ℕ) : ℝ :=
  1 / Real.rpow n p

def rootFactor (n : ℕ) : ℝ :=
  1 / Real.rpow n (1 / n)

def term (p : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n - 1) * magnitude p n

def baseTerm (p : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n - 1) * baseMagnitude p n

def ConditionallySummable (p : ℝ) : Prop :=
  Summable (fun n : ℕ => term p (n + 1)) ∧
    ¬ Summable (fun n : ℕ => magnitude p (n + 1))

private theorem seriesConverges_iff_tendsto_partialSums {f : ℕ → ℝ} :
    ProofGap.SeriesConverges f ↔
      ∃ l : ℝ, Tendsto (fun n => ∑ i ∈ Finset.range n, f i) atTop (nhds l) := by
  unfold ProofGap.SeriesConverges Summable HasSum
  simp only [SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff,
    Function.comp_apply]
  rfl

private theorem seriesConverges_tendsto_zero {f : ℕ → ℝ}
    (hf : ProofGap.SeriesConverges f) : Tendsto f atTop (nhds 0) := by
  rcases seriesConverges_iff_tendsto_partialSums.mp hf with ⟨l, hl⟩
  have hshift := hl.comp (tendsto_add_atTop_nat 1)
  have hdiff := hshift.sub hl
  convert hdiff using 1
  · ext n
    simp only [Function.comp_apply]
    rw [Finset.sum_range_succ]
    ring
  · ring

private theorem seriesConverges_nat_add_iff (f : ℕ → ℝ) (k : ℕ) :
    ProofGap.SeriesConverges (fun n => f (n + k)) ↔
      ProofGap.SeriesConverges f := by
  rw [seriesConverges_iff_tendsto_partialSums,
    seriesConverges_iff_tendsto_partialSums]
  let c := ∑ i ∈ Finset.range k, f i
  constructor
  · rintro ⟨l, hl⟩
    refine ⟨c + l, (tendsto_add_atTop_iff_nat k).mp ?_⟩
    apply (tendsto_const_nhds.add hl).congr'
    filter_upwards with n
    dsimp [c]
    rw [show n + k = k + n by omega, Finset.sum_range_add]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    omega
  · rintro ⟨l, hl⟩
    refine ⟨l - c, ?_⟩
    apply ((hl.comp (tendsto_add_atTop_nat k)).sub tendsto_const_nhds).congr'
    filter_upwards with n
    dsimp [c]
    rw [show n + k = k + n by omega, Finset.sum_range_add,
      add_sub_cancel_left]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    omega

private theorem baseMagnitude_eq_rpow_neg (p : ℝ) (n : ℕ) (hn : 0 < n) :
    baseMagnitude p n = (n : ℝ) ^ (-p) := by
  unfold baseMagnitude
  rw [Real.rpow_neg (by positivity)]
  simp [one_div]

private theorem magnitude_eq_mul (p : ℝ) (n : ℕ) (hn : 0 < n) :
    magnitude p n = baseMagnitude p n * rootFactor n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold magnitude baseMagnitude rootFactor
  change 1 / ((n : ℝ) ^ (p + 1 / (n : ℝ))) =
    1 / ((n : ℝ) ^ p) * (1 / ((n : ℝ) ^ (1 / (n : ℝ))))
  rw [Real.rpow_add hnR]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos hnR p),
    ne_of_gt (Real.rpow_pos_of_pos hnR (1 / (n : ℝ)))]

private theorem rootFactor_eq_exp (n : ℕ) (hn : 0 < n) :
    rootFactor n = Real.exp (-(Real.log n / n)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold rootFactor
  change 1 / ((n : ℝ) ^ (1 / (n : ℝ))) =
    Real.exp (-(Real.log n / n))
  rw [Real.rpow_def_of_pos hnR, one_div, ← Real.exp_neg]
  congr 1
  ring

private theorem abs_term_eq_magnitude (p : ℝ) (n : ℕ) (hn : 0 < n) :
    |term p n| = magnitude p n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold term magnitude
  have hden : 0 < Real.rpow n (p + 1 / (n : ℝ)) :=
    Real.rpow_pos_of_pos hnR _
  have hmag : 0 ≤ 1 / Real.rpow n (p + 1 / (n : ℝ)) := by positivity
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg hmag]

private theorem antitone_baseMagnitude (p : ℝ) (hp : 0 < p) :
    Antitone (fun n : ℕ => baseMagnitude p (n + 1)) := by
  intro n m hnm
  change baseMagnitude p (m + 1) ≤ baseMagnitude p (n + 1)
  rw [baseMagnitude_eq_rpow_neg p (m + 1) (by omega),
    baseMagnitude_eq_rpow_neg p (n + 1) (by omega)]
  apply Real.rpow_le_rpow_of_nonpos (by positivity)
  · exact_mod_cast Nat.add_le_add_right hnm 1
  · linarith

private theorem tendsto_baseMagnitude_zero (p : ℝ) (hp : 0 < p) :
    Tendsto (fun n : ℕ => baseMagnitude p (n + 1)) atTop (nhds 0) := by
  have hcast : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have h := (tendsto_rpow_neg_atTop hp).comp hcast
  apply h.congr'
  filter_upwards with n
  exact (baseMagnitude_eq_rpow_neg p (n + 1) (by omega)).symm

private theorem baseTerm_seriesConverges (p : ℝ) (hp : 0 < p) :
    ProofGap.SeriesConverges (fun n : ℕ => baseTerm p (n + 1)) := by
  rcases (antitone_baseMagnitude p hp).tendsto_alternating_series_of_tendsto_zero
      (tendsto_baseMagnitude_zero p hp) with ⟨l, hl⟩
  apply seriesConverges_iff_tendsto_partialSums.mpr
  refine ⟨l, ?_⟩
  simpa [baseTerm] using hl

private theorem summable_baseMagnitude_iff (p : ℝ) :
    Summable (fun n : ℕ => baseMagnitude p (n + 1)) ↔ 1 < p := by
  constructor
  · intro h
    apply Real.summable_one_div_nat_rpow.mp
    apply (summable_nat_add_iff 1).mp
    simpa [baseMagnitude] using h
  · intro hp
    have h := (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_rpow.mpr hp)
    simpa [baseMagnitude] using h

theorem gap1 :
    ∀ p : ℝ, ∀ n : ℕ, 1 ≤ n →
      magnitude p n / baseMagnitude p n = rootFactor n := by
  intro p n hn
  rw [magnitude_eq_mul p n (Nat.zero_lt_one.trans_le hn)]
  have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_one.trans_le hn)
  have hb0 : baseMagnitude p n ≠ 0 := by
    unfold baseMagnitude
    exact one_div_ne_zero (ne_of_gt (Real.rpow_pos_of_pos hnR p))
  field_simp [hb0]

theorem gap2 :
    Tendsto (fun n : ℕ => rootFactor (n + 1)) atTop (nhds 1) := by
  have hcast : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hpow := tendsto_rpow_div.comp hcast
  have hinv := hpow.inv₀ (by norm_num)
  simpa [rootFactor, Function.comp_apply, one_div] using hinv

theorem gap3 :
    ∀ p : ℝ,
      Tendsto
        (fun n : ℕ => magnitude p (n + 1) / baseMagnitude p (n + 1))
        atTop (nhds 1) := by
  intro p
  apply gap2.congr'
  filter_upwards with n
  exact (gap1 p (n + 1) (Nat.succ_le_succ (Nat.zero_le n))).symm

theorem gap4 :
    ∀ p : ℝ, 1 < p →
      Summable (fun n : ℕ => baseMagnitude p (n + 1)) := by
  intro p hp
  have h := Real.summable_one_div_nat_rpow.mpr hp
  rw [← summable_nat_add_iff 1] at h
  simpa [baseMagnitude] using h

theorem gap5 :
    ∀ p : ℝ, 1 < p →
      Summable (fun n : ℕ => |term p (n + 1)|) := by
  intro p hp
  have hbase := gap4 p hp
  have hroot := gap2.eventually (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))
  apply (hbase.mul_left 2).of_norm_bounded_eventually_nat
  filter_upwards [hroot] with n hn
  rw [Real.norm_eq_abs, abs_abs, abs_term_eq_magnitude p (n + 1) (by omega),
    magnitude_eq_mul p (n + 1) (by omega)]
  have hnR : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hb : 0 ≤ baseMagnitude p (n + 1) := by
    unfold baseMagnitude
    exact (one_div_pos.mpr (Real.rpow_pos_of_pos hnR p)).le
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hn.le hb

theorem gap6 :
    ∀ p : ℝ, p ≤ 0 →
      ¬ Summable (fun n : ℕ => term p (n + 1)) := by
  intro p hp hsum
  have hsmall := hsum.tendsto_atTop_zero.norm.eventually
    (Iio_mem_nhds (show ‖(0 : ℝ)‖ < (1 / 4 : ℝ) by norm_num))
  have hroot := gap2.eventually (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  rcases (hsmall.and hroot).exists with ⟨n, hsmall, hroot⟩
  have hnR : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hpowpos : 0 < Real.rpow ((n + 1 : ℕ) : ℝ) p :=
    Real.rpow_pos_of_pos hnR p
  have hpowle : Real.rpow ((n + 1 : ℕ) : ℝ) p ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) hp
  have hbase : 1 ≤ baseMagnitude p (n + 1) := by
    unfold baseMagnitude
    apply (le_div_iff₀ hpowpos).2
    simpa using hpowle
  have hroot0 : 0 ≤ rootFactor (n + 1) := by
    unfold rootFactor
    positivity
  have hmul : rootFactor (n + 1) ≤
      baseMagnitude p (n + 1) * rootFactor (n + 1) := by
    simpa using mul_le_mul_of_nonneg_right hbase hroot0
  rw [Real.norm_eq_abs, abs_term_eq_magnitude p (n + 1) (by omega),
    magnitude_eq_mul p (n + 1) (by omega)] at hsmall
  linarith

theorem gap7 :
    ∀ p : ℝ, 0 < p → p ≤ 1 → ∀ n : ℕ, 1 ≤ n →
      term p n = baseTerm p n * rootFactor n := by
  intro p hp hp1 n hn
  unfold term baseTerm
  rw [magnitude_eq_mul p n (Nat.zero_lt_one.trans_le hn)]
  ring

theorem gap8 :
    ∀ p : ℝ, 0 < p → p ≤ 1 →
      (ProofGap.SeriesConverges (fun n : ℕ => baseTerm p (n + 1)) ∧
        ¬ Summable (fun n : ℕ => baseMagnitude p (n + 1))) := by
  intro p hp hp1
  exact ⟨baseTerm_seriesConverges p hp,
    (summable_baseMagnitude_iff p).not.mpr (not_lt_of_ge hp1)⟩

theorem gap9 :
    ∃ N : ℕ, Monotone (fun n : ℕ => rootFactor (n + N)) := by
  refine ⟨3, ?_⟩
  intro n m hnm
  change rootFactor (n + 3) ≤ rootFactor (m + 3)
  rw [rootFactor_eq_exp (n + 3) (by omega), rootFactor_eq_exp (m + 3) (by omega)]
  apply Real.exp_monotone
  apply neg_le_neg
  apply Real.log_div_self_antitoneOn
  · exact Real.exp_one_lt_three.le.trans (by exact_mod_cast Nat.le_add_left 3 n)
  · exact Real.exp_one_lt_three.le.trans (by exact_mod_cast Nat.le_add_left 3 m)
  · exact_mod_cast Nat.add_le_add_right hnm 3

theorem gap10 :
    ∀ p : ℝ, 0 < p → p ≤ 1 →
      Tendsto (fun n : ℕ => rootFactor (n + 1)) atTop (nhds 1) := by
  intro p hp hp1
  exact gap2

theorem gap11 :
    ∀ p : ℝ, 0 < p → p ≤ 1 →
      ProofGap.SeriesConverges (fun n : ℕ => term p (n + 1)) := by
  intro p hp hp1
  rcases gap9 with ⟨N, hN⟩
  let a : ℕ → ℝ := fun n => baseTerm p (n + 1)
  let r : ℕ → ℝ := fun n => rootFactor (n + 1)
  have ha : ProofGap.SeriesConverges a := by
    simpa [a] using baseTerm_seriesConverges p hp
  have haTail : ProofGap.SeriesConverges (fun n => a (n + N)) :=
    (seriesConverges_nat_add_iff a N).mpr ha
  rcases seriesConverges_iff_tendsto_partialSums.mp haTail with ⟨la, hla⟩
  obtain ⟨b, hb⟩ := isBounded_iff_forall_norm_le.mp hla.cauchySeq.isBounded_range
  have hb' : ∀ n, ‖∑ i ∈ Finset.range n, a (i + N)‖ ≤ b := by
    intro n
    exact hb _ ⟨n, rfl⟩
  have hrMonotone : Monotone (fun n => r (n + N) - 1) := by
    intro n m hnm
    apply sub_le_sub_right
    have h := hN (Nat.add_le_add_right hnm 1)
    simpa [r, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  have hrTail : Tendsto (fun n => r (n + N)) atTop (nhds 1) := by
    simpa [r, Function.comp_apply, Nat.add_assoc] using
      gap2.comp (tendsto_add_atTop_nat N)
  have hrZero : Tendsto (fun n => r (n + N) - 1) atTop (nhds 0) := by
    convert hrTail.sub tendsto_const_nhds using 1 <;> norm_num
  have hcorrectionCauchy :
      CauchySeq (fun n => ∑ i ∈ Finset.range n,
        (r (i + N) - 1) • a (i + N)) :=
    hrMonotone.cauchySeq_series_mul_of_tendsto_zero_of_bounded hrZero hb'
  rcases cauchySeq_tendsto_of_complete hcorrectionCauchy with ⟨lc, hlc⟩
  have hcorrection : ProofGap.SeriesConverges
      (fun n => a (n + N) * (r (n + N) - 1)) := by
    apply seriesConverges_iff_tendsto_partialSums.mpr
    refine ⟨lc, ?_⟩
    simpa [smul_eq_mul, mul_comm] using hlc
  have hproduct : ProofGap.SeriesConverges
      (fun n => a (n + N) * r (n + N)) := by
    apply haTail.add hcorrection |>.congr
    intro n
    ring
  have htermTail : ProofGap.SeriesConverges
      (fun n => term p ((n + N) + 1)) := by
    apply hproduct.congr
    intro n
    dsimp [a, r]
    exact (gap7 p hp hp1 ((n + N) + 1) (by omega)).symm
  apply (seriesConverges_nat_add_iff (fun n => term p (n + 1)) N).mp
  simpa only using htermTail

theorem gap12 :
    ∀ p : ℝ, 0 < p → p ≤ 1 →
      ¬ Summable (fun n : ℕ => magnitude p (n + 1)) := by
  intro p hp hp1 hmag
  have hratio := (gap3 p).eventually
    (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  have hbase : Summable (fun n : ℕ => baseMagnitude p (n + 1)) := by
    apply (hmag.mul_left 2).of_norm_bounded_eventually_nat
    filter_upwards [hratio] with n hn
    have hnR : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hbpos : 0 < baseMagnitude p (n + 1) := by
      unfold baseMagnitude
      exact one_div_pos.mpr (Real.rpow_pos_of_pos hnR p)
    have hmnonneg : 0 ≤ magnitude p (n + 1) := by
      unfold magnitude
      exact (one_div_pos.mpr (Real.rpow_pos_of_pos hnR _)).le
    rw [Real.norm_eq_abs, abs_of_pos hbpos]
    have hn' := (lt_div_iff₀ hbpos).mp hn
    nlinarith
  exact (not_lt_of_ge hp1) ((summable_baseMagnitude_iff p).mp hbase)

theorem gap13 :
    ∀ p : ℝ, 0 < p → p ≤ 1 →
      ProofGap.SeriesConverges (fun n : ℕ => term p (n + 1)) ∧
        ¬ Summable (fun n : ℕ => magnitude p (n + 1)) := by
  intro p hp hp1
  exact ⟨gap11 p hp hp1, gap12 p hp hp1⟩

end

end ProofGap.Exercise2676

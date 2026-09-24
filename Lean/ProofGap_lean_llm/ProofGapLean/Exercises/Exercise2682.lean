import ProofGapLean.Prelude.Analysis
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2682

noncomputable section

open Filter

def sineValue (n : ℕ) : ℝ :=
  Real.sin ((n : ℝ) * Real.pi / 4)

def term (p : ℝ) (n : ℕ) : ℝ :=
  sineValue n / (Real.rpow n p + sineValue n)

def leadingTerm (p : ℝ) (n : ℕ) : ℝ :=
  sineValue n / Real.rpow n p

def quadraticTerm (p : ℝ) (n : ℕ) : ℝ :=
  sineValue n ^ 2 / Real.rpow n (2 * p)

def remainder (p : ℝ) (n : ℕ) : ℝ :=
  term p n - (leadingTerm p n - quadraticTerm p n)

def comparison (q : ℝ) (n : ℕ) : ℝ :=
  1 / Real.rpow n q

def denominator (p : ℝ) (n : ℕ) : ℝ :=
  Real.rpow n p + sineValue n

def ConditionallySummable (p : ℝ) : Prop :=
  ProofGap.SeriesConverges (fun n : ℕ => term p (n + 1)) ∧
  ¬ Summable (fun n : ℕ => |term p (n + 1)|)

private def sinePartial (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, sineValue i

private theorem sineValue_add_eight (n : ℕ) : sineValue (n + 8) = sineValue n := by
  unfold sineValue
  have harg : ((n + 8 : ℕ) : ℝ) * Real.pi / 4 =
      (n : ℝ) * Real.pi / 4 + 2 * Real.pi := by
    push_cast
    ring
  rw [harg, Real.sin_add_two_pi]

private theorem sineValue_periodic : Function.Periodic sineValue 8 :=
  sineValue_add_eight

private theorem sine_block_sum : sinePartial 8 = 0 := by
  unfold sinePartial sineValue
  norm_num [Finset.sum_range_succ]
  rw [show (3 : ℝ) * Real.pi / 4 = Real.pi - Real.pi / 4 by ring,
    Real.sin_pi_sub, Real.sin_pi_div_four]
  rw [show (2 : ℝ) * Real.pi / 4 = Real.pi / 2 by ring, Real.sin_pi_div_two]
  rw [show (5 : ℝ) * Real.pi / 4 = Real.pi / 4 + Real.pi by ring,
    Real.sin_add_pi, Real.sin_pi_div_four]
  rw [show (6 : ℝ) * Real.pi / 4 = Real.pi / 2 + Real.pi by ring,
    Real.sin_add_pi, Real.sin_pi_div_two]
  rw [show (7 : ℝ) * Real.pi / 4 = 3 * Real.pi / 4 + Real.pi by ring,
    Real.sin_add_pi]
  rw [show (3 : ℝ) * Real.pi / 4 = Real.pi - Real.pi / 4 by ring,
    Real.sin_pi_sub, Real.sin_pi_div_four]
  ring

private theorem sinePartial_add_eight (n : ℕ) : sinePartial (n + 8) = sinePartial n := by
  rw [show n + 8 = 8 + n by omega]
  unfold sinePartial
  rw [Finset.sum_range_add]
  rw [show (∑ x ∈ Finset.range 8, sineValue x) = 0 by
    exact sine_block_sum]
  simp only [zero_add]
  apply Finset.sum_congr rfl
  intro i hi
  simpa [add_comm] using sineValue_add_eight i

private theorem sinePartial_periodic : Function.Periodic sinePartial 8 :=
  sinePartial_add_eight

private theorem norm_sineValue_le_one (n : ℕ) : ‖sineValue n‖ ≤ 1 := by
  unfold sineValue
  simpa [Real.norm_eq_abs] using Real.abs_sin_le_one ((n : ℝ) * Real.pi / 4)

private theorem sinePartial_bound (n : ℕ) : ‖sinePartial n‖ ≤ 8 := by
  have hdecomp : n % 8 + n / 8 * 8 = n := by omega
  have hperiod := sinePartial_periodic.nsmul (n / 8) (n % 8)
  have heq : sinePartial n = sinePartial (n % 8) := by
    rw [← hdecomp]
    simpa [add_comm, mul_comm] using hperiod
  rw [heq]
  unfold sinePartial
  calc
    ‖∑ i ∈ Finset.range (n % 8), sineValue i‖ ≤
        ∑ i ∈ Finset.range (n % 8), ‖sineValue i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range (n % 8), (1 : ℝ) := by
      gcongr with i hi
      exact norm_sineValue_le_one i
    _ ≤ 8 := by simp; omega

private theorem shifted_sine_partial_eq (n : ℕ) :
    (∑ i ∈ Finset.range n, sineValue (i + 1)) = sinePartial (n + 1) := by
  induction n with
  | zero => simp [sinePartial, sineValue]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [sinePartial, Finset.sum_range_succ]

private theorem shifted_sine_partial_bound (n : ℕ) :
    ‖∑ i ∈ Finset.range n, sineValue (i + 1)‖ ≤ 8 := by
  rw [shifted_sine_partial_eq]
  exact sinePartial_bound (n + 1)

private theorem seriesConverges_of_tendsto_partial {f : ℕ → ℝ} {s : ℝ}
    (h : Tendsto (fun n => ∑ i ∈ Finset.range n, f i) atTop (nhds s)) :
    ProofGap.SeriesConverges f := by
  unfold ProofGap.SeriesConverges
  refine ⟨s, ?_⟩
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range,
    Filter.tendsto_map'_iff]
  simpa only [Function.comp_apply] using h

private theorem seriesConverges_of_summable {f : ℕ → ℝ} (hf : Summable f) :
    ProofGap.SeriesConverges f :=
  seriesConverges_of_tendsto_partial hf.hasSum.tendsto_sum_nat

private theorem leading_series_converges (p : ℝ) (hp : 0 < p) :
    ProofGap.SeriesConverges (fun n : ℕ => leadingTerm p (n + 1)) := by
  let weight : ℕ → ℝ := fun n => Real.rpow (((n + 1 : ℕ) : ℝ)) (-p)
  have hanti : Antitone weight := by
    intro a b hab
    exact Real.rpow_le_rpow_of_nonpos (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hab 1) (by linarith)
  have hweight : Tendsto weight atTop (nhds 0) := by
    exact (tendsto_rpow_neg_atTop hp).comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))
  have hcauchy : CauchySeq (fun n =>
      ∑ i ∈ Finset.range n, weight i • sineValue (i + 1)) :=
    hanti.cauchySeq_series_mul_of_tendsto_zero_of_bounded hweight
      shifted_sine_partial_bound
  obtain ⟨s, hs⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hs' : Tendsto (fun n => ∑ i ∈ Finset.range n, leadingTerm p (i + 1))
      atTop (nhds s) := by
    convert hs using 1
    funext n
    apply Finset.sum_congr rfl
    intro i hi
    unfold weight leadingTerm
    simp only [smul_eq_mul]
    rw [show Real.rpow (((i + 1 : ℕ) : ℝ)) (-p) =
      (Real.rpow (((i + 1 : ℕ) : ℝ)) p)⁻¹ by
        simpa only using Real.rpow_neg
          (by positivity : 0 ≤ (((i + 1 : ℕ) : ℝ))) p]
    ring
  exact seriesConverges_of_tendsto_partial hs'

private theorem comparison_summable (q : ℝ) (hq : 1 < q) :
    Summable (fun n : ℕ => comparison q (n + 1)) := by
  have h := (Real.summable_one_div_nat_add_rpow 1 q).mpr hq
  apply h.congr
  intro n
  unfold comparison
  rw [Real.rpow_eq_pow]
  rw [Nat.cast_add, Nat.cast_one, abs_of_pos (by positivity)]

private theorem eventually_rpow_shift_ge_two (p : ℝ) (hp : 0 < p) :
    ∀ᶠ n : ℕ in atTop, 2 ≤ Real.rpow (((n + 1 : ℕ) : ℝ)) p := by
  have ht : Tendsto (fun n : ℕ => Real.rpow (((n + 1 : ℕ) : ℝ)) p) atTop atTop :=
    (tendsto_rpow_atTop hp).comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))
  exact ht.eventually (Ici_mem_atTop 2)

private theorem rpow_two_mul (p : ℝ) (n : ℕ) :
    Real.rpow n (2 * p) = Real.rpow n p ^ 2 := by
  rw [show 2 * p = p * (2 : ℕ) by norm_num; ring]
  simpa only using Real.rpow_mul_natCast (Nat.cast_nonneg n) p 2

private theorem rpow_three_mul (p : ℝ) (n : ℕ) :
    Real.rpow n (3 * p) = Real.rpow n p ^ 3 := by
  rw [show 3 * p = p * (3 : ℕ) by norm_num; ring]
  simpa only using Real.rpow_mul_natCast (Nat.cast_nonneg n) p 3

private theorem remainder_formula (p : ℝ) (n : ℕ)
    (ha : 2 ≤ Real.rpow n p) :
    remainder p n = sineValue n ^ 3 /
      (Real.rpow n p ^ 2 * (Real.rpow n p + sineValue n)) := by
  have hapos : 0 < Real.rpow n p := lt_of_lt_of_le (by norm_num) ha
  have hsabs : |sineValue n| ≤ 1 := by
    simpa [Real.norm_eq_abs] using norm_sineValue_le_one n
  have hsneg : -1 ≤ sineValue n := (abs_le.mp hsabs).1
  have hden : 0 < Real.rpow n p + sineValue n := by linarith
  unfold remainder term leadingTerm quadraticTerm
  rw [rpow_two_mul]
  field_simp [hapos.ne', hden.ne']
  ring

private theorem remainder_isBigO (p : ℝ) (hp : 0 < p) :
    Asymptotics.IsBigO atTop
      (fun n : ℕ => remainder p (n + 1))
      (fun n : ℕ => comparison (3 * p) (n + 1)) := by
  refine Asymptotics.IsBigO.of_bound 2
    ((eventually_rpow_shift_ge_two p hp).mono fun n ha => ?_)
  let a : ℝ := Real.rpow (((n + 1 : ℕ) : ℝ)) p
  let s : ℝ := sineValue (n + 1)
  have hapos : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have hsabs : |s| ≤ 1 := by
    simpa [s, Real.norm_eq_abs] using norm_sineValue_le_one (n + 1)
  have hsneg : -1 ≤ s := (abs_le.mp hsabs).1
  have hden : 0 < a + s := by linarith
  have hdenlower : a / 2 ≤ a + s := by linarith
  have hnum : |s| ^ 3 ≤ 1 := by
    have hs0 : 0 ≤ |s| := abs_nonneg s
    nlinarith [sq_nonneg |s|, mul_self_le_mul_self hs0 hsabs]
  have hleft : |s| ^ 3 * a ^ 3 ≤ a ^ 3 :=
    mul_le_of_le_one_left (pow_nonneg hapos.le 3) hnum
  have hright : a ^ 3 ≤ 2 * (a ^ 2 * (a + s)) := by
    have hmul := mul_le_mul_of_nonneg_left hdenlower (sq_nonneg a)
    nlinarith
  rw [remainder_formula p (n + 1) ha]
  unfold comparison
  rw [rpow_three_mul]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_div,
    abs_mul, abs_pow, abs_pow, abs_of_pos hapos,
    abs_of_pos hden, abs_of_pos (one_div_pos.mpr (pow_pos hapos 3))]
  change |s| ^ 3 / (a ^ 2 * (a + s)) ≤ 2 * (1 / a ^ 3)
  rw [show 2 * (1 / a ^ 3) = 2 / a ^ 3 by ring]
  rw [div_le_div_iff₀ (mul_pos (pow_pos hapos 2) hden) (pow_pos hapos 3)]
  exact hleft.trans hright

theorem gap1 :
    ∀ p : ℝ, 0 < p → ∀ n : ℕ, 1 ≤ n →
      term p n =
        leadingTerm p n *
          (1 / (1 + sineValue n / Real.rpow n p)) := by
  intro p hp n hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have ha : Real.rpow n p ≠ 0 := (Real.rpow_pos_of_pos hnpos p).ne'
  unfold term leadingTerm
  field_simp [ha]

theorem gap2 :
    ∀ p : ℝ, 0 < p →
      Asymptotics.IsBigO atTop
        (fun n : ℕ => remainder p (n + 1))
        (fun n : ℕ => comparison (3 * p) (n + 1)) := by
  intro p hp
  exact remainder_isBigO p hp

theorem gap3 :
    ∀ p : ℝ, 0 < p →
      Asymptotics.IsBigO atTop
        (fun n : ℕ =>
          term p (n + 1) -
            (leadingTerm p (n + 1) - quadraticTerm p (n + 1)))
        (fun n : ℕ => comparison (3 * p) (n + 1)) := by
  intro p hp
  simpa only [remainder] using gap2 p hp

theorem gap4 :
    ∀ p : ℝ, 1 / 2 < p →
      ProofGap.SeriesConverges (fun n : ℕ => leadingTerm p (n + 1)) := by
  intro p hp
  exact leading_series_converges p (by linarith)

theorem gap5 :
    ∀ p : ℝ, 1 / 2 < p →
      Summable (fun n : ℕ => quadraticTerm p (n + 1)) := by
  intro p hp
  have hcomp := comparison_summable (2 * p) (by linarith)
  apply hcomp.of_nonneg_of_le
  · intro n
    unfold quadraticTerm
    exact div_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (Nat.cast_nonneg (n + 1)) _)
  · intro n
    have hsabs : |sineValue (n + 1)| ≤ 1 := by
      simpa [Real.norm_eq_abs] using norm_sineValue_le_one (n + 1)
    have hsneg : -1 ≤ sineValue (n + 1) := (abs_le.mp hsabs).1
    have hspos : sineValue (n + 1) ≤ 1 := (abs_le.mp hsabs).2
    have hs2 : sineValue (n + 1) ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg (sineValue (n + 1) - 1),
        sq_nonneg (sineValue (n + 1) + 1)]
    unfold quadraticTerm comparison
    exact div_le_div_of_nonneg_right hs2
      (Real.rpow_nonneg (Nat.cast_nonneg (n + 1)) _)

theorem gap6 :
    ∀ p : ℝ, 1 / 2 < p →
      Summable (fun n : ℕ => remainder p (n + 1)) := by
  intro p hp
  exact summable_of_isBigO_nat
    (comparison_summable (3 * p) (by linarith))
    (gap2 p (by linarith))

private theorem sineValue_eight_mul_add_one (n : ℕ) :
    sineValue (8 * n + 1) = sineValue 1 := by
  have h := sineValue_periodic.nsmul n 1
  simpa [Nat.mul_comm, Nat.add_comm] using h

private theorem comparison_eight_mul_add_one_not_summable
    (q : ℝ) (hq : 0 < q) (hq_one : q ≤ 1) :
    ¬ Summable (fun n : ℕ => comparison q (8 * n + 1)) := by
  intro hsub
  have hscaled := hsub.mul_left (Real.rpow 8 q)
  have hstandard : Summable (fun n : ℕ => comparison q (n + 1)) := by
    apply hscaled.of_nonneg_of_le
    · intro n
      unfold comparison
      exact one_div_nonneg.mpr
        (Real.rpow_nonneg (Nat.cast_nonneg (n + 1)) q)
    · intro n
      have hnpos : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
      have hsubpos : 0 < (((8 * n + 1 : ℕ) : ℝ)) := by positivity
      have hbase : (((8 * n + 1 : ℕ) : ℝ)) ≤
          (8 : ℝ) * (((n + 1 : ℕ) : ℝ)) := by
        push_cast
        nlinarith
      have hpow := Real.rpow_le_rpow (by positivity) hbase hq.le
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8) hnpos.le] at hpow
      unfold comparison
      rw [show Real.rpow 8 q *
          (1 / Real.rpow (((8 * n + 1 : ℕ) : ℝ)) q) =
          Real.rpow 8 q / Real.rpow (((8 * n + 1 : ℕ) : ℝ)) q by ring]
      simp only [Real.rpow_eq_pow]
      rw [div_le_div_iff₀
        (Real.rpow_pos_of_pos hnpos q)
        (Real.rpow_pos_of_pos hsubpos q)]
      simpa [mul_assoc] using hpow
  have hpseries : Summable (fun n : ℕ => 1 / |(n : ℝ) + 1| ^ q) := by
    apply hstandard.congr
    intro n
    unfold comparison
    rw [Real.rpow_eq_pow]
    rw [Nat.cast_add, Nat.cast_one, abs_of_pos (by positivity)]
  have := (Real.summable_one_div_nat_add_rpow 1 q).mp hpseries
  linarith

private theorem leading_isBigO_term (p : ℝ) (hp : 0 < p) :
    Asymptotics.IsBigO atTop
      (fun n : ℕ => leadingTerm p (n + 1))
      (fun n : ℕ => term p (n + 1)) := by
  refine Asymptotics.IsBigO.of_bound 2
    ((eventually_rpow_shift_ge_two p hp).mono fun n ha => ?_)
  let a : ℝ := Real.rpow (((n + 1 : ℕ) : ℝ)) p
  let s : ℝ := sineValue (n + 1)
  have hapos : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have hsabs : |s| ≤ 1 := by
    simpa [s, Real.norm_eq_abs] using norm_sineValue_le_one (n + 1)
  have hsle : s ≤ 1 := le_trans (le_abs_self s) hsabs
  have hsneg : -1 ≤ s := (abs_le.mp hsabs).1
  have hden : 0 < a + s := by linarith
  have hdenupper : a + s ≤ 2 * a := by linarith
  have hmul := mul_le_mul_of_nonneg_left hdenupper (abs_nonneg s)
  unfold leadingTerm term
  change ‖s / a‖ ≤ 2 * ‖s / (a + s)‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_div,
    abs_of_pos hapos, abs_of_pos hden]
  rw [show 2 * (|s| / (a + s)) = (2 * |s|) / (a + s) by ring]
  rw [div_le_div_iff₀ hapos hden]
  nlinarith

theorem gap7 :
    ∀ p : ℝ, 1 / 2 < p →
      ProofGap.SeriesConverges (fun n : ℕ => term p (n + 1)) := by
  intro p hp
  unfold ProofGap.SeriesConverges at ⊢
  obtain ⟨s, hs⟩ := gap4 p hp
  obtain ⟨sq, hq⟩ := seriesConverges_of_summable (gap5 p hp)
  obtain ⟨sr, hr⟩ := seriesConverges_of_summable (gap6 p hp)
  refine ⟨s - sq + sr, ?_⟩
  convert (hs.sub hq).add hr using 1 <;>
    simp only [Pi.add_apply, Pi.sub_apply, remainder] <;> ring

private theorem leading_abs_not_summable (p : ℝ) (hp : 0 < p) (hp_one : p ≤ 1) :
    ¬ Summable (fun n : ℕ => |leadingTerm p (n + 1)|) := by
  intro hsumm
  apply comparison_eight_mul_add_one_not_summable p hp hp_one
  have hinj : Function.Injective (fun n : ℕ => 8 * n) := by
    intro a b hab
    exact Nat.mul_left_cancel (by norm_num) hab
  have hsub : Summable (fun n : ℕ => |leadingTerm p (8 * n + 1)|) := by
    simpa [Function.comp_def] using hsumm.comp_injective hinj
  have hc : 0 < sineValue 1 := by
    unfold sineValue
    norm_num only [Nat.cast_one, one_mul]
    rw [Real.sin_pi_div_four]
    positivity
  have hscaled := hsub.mul_left (sineValue 1)⁻¹
  apply hscaled.congr
  intro n
  have hnpos : 0 < (((8 * n + 1 : ℕ) : ℝ)) := by positivity
  have hapos : 0 < Real.rpow (((8 * n + 1 : ℕ) : ℝ)) p :=
    Real.rpow_pos_of_pos hnpos p
  rw [leadingTerm, sineValue_eight_mul_add_one, abs_div,
    abs_of_pos hc, abs_of_pos hapos]
  unfold comparison
  field_simp [hc.ne', hapos.ne']

theorem gap8 :
    ∀ p : ℝ, 1 / 2 < p → p ≤ 1 →
      ¬ Summable (fun n : ℕ => |leadingTerm p (n + 1)|) := by
  intro p hp hp_one
  exact leading_abs_not_summable p (by linarith) hp_one

theorem gap9 :
    ∀ p : ℝ, 1 / 2 < p → p ≤ 1 → ConditionallySummable p := by
  intro p hp hp_one
  refine ⟨gap7 p hp, ?_⟩
  intro habs
  have hterm : Summable (fun n : ℕ => term p (n + 1)) := by
    rw [← summable_norm_iff]
    simpa [Real.norm_eq_abs] using habs
  have hleading : Summable (fun n : ℕ => leadingTerm p (n + 1)) :=
    summable_of_isBigO_nat hterm (leading_isBigO_term p (by linarith))
  have hleading_abs : Summable (fun n : ℕ => |leadingTerm p (n + 1)|) := by
    simpa [Real.norm_eq_abs] using hleading.norm
  exact gap8 p hp hp_one hleading_abs

theorem gap10 :
    ∀ p : ℝ, 1 < p →
      Asymptotics.IsBigO atTop
        (fun n : ℕ => term p (n + 1))
        (fun n : ℕ => comparison p (n + 1)) := by
  intro p hp
  refine Asymptotics.IsBigO.of_bound 2
    ((eventually_rpow_shift_ge_two p (by linarith)).mono fun n ha => ?_)
  let a : ℝ := Real.rpow (((n + 1 : ℕ) : ℝ)) p
  let s : ℝ := sineValue (n + 1)
  have hapos : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have hsabs : |s| ≤ 1 := by
    simpa [s, Real.norm_eq_abs] using norm_sineValue_le_one (n + 1)
  have hsneg : -1 ≤ s := (abs_le.mp hsabs).1
  have hden : 0 < a + s := by linarith
  have hleft : |s| * a ≤ a := by
    exact mul_le_of_le_one_left hapos.le hsabs
  have hright : a ≤ 2 * (a + s) := by linarith
  unfold term comparison
  change ‖s / (a + s)‖ ≤ 2 * ‖1 / a‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_div,
    abs_of_pos hden, abs_of_pos hapos, abs_of_pos (by norm_num : (0 : ℝ) < 1)]
  rw [show 2 * (1 / a) = 2 / a by ring]
  rw [div_le_div_iff₀ hden hapos]
  exact hleft.trans hright

theorem gap11 :
    ∀ p : ℝ, 1 < p →
      Summable (fun n : ℕ => |term p (n + 1)|) := by
  intro p hp
  have ht : Summable (fun n : ℕ => term p (n + 1)) :=
    summable_of_isBigO_nat (comparison_summable p hp) (gap10 p hp)
  simpa [Real.norm_eq_abs] using ht.norm

theorem gap12 :
    ∀ p : ℝ, p ≤ 0 →
      ((p = 0 ∧ ∃ n : ℕ, 1 ≤ n ∧ denominator p n = 0) ∨
        (p < 0 ∧
          ¬ Tendsto (fun n : ℕ => term p (n + 1)) atTop (nhds 0))) := by
  intro p hp
  rcases hp.eq_or_lt with rfl | hpneg
  · left
    refine ⟨rfl, 6, by norm_num, ?_⟩
    unfold denominator sineValue
    norm_num only [Nat.cast_ofNat]
    rw [Real.rpow_eq_pow, Real.rpow_zero]
    rw [show (6 : ℝ) * Real.pi / 4 = Real.pi / 2 + Real.pi by ring,
      Real.sin_add_pi, Real.sin_pi_div_two]
    ring
  · right
    refine ⟨hpneg, ?_⟩
    intro hzero
    have hsub_atTop : Tendsto (fun n : ℕ => 8 * n) atTop atTop := by
      rw [tendsto_atTop]
      intro b
      filter_upwards [eventually_ge_atTop b] with n hn
      omega
    have hrpow : Tendsto (fun n : ℕ =>
        Real.rpow (((n + 1 : ℕ) : ℝ)) p)
        atTop (nhds 0) := by
      have hneg : 0 < -p := by linarith
      simpa only [neg_neg] using
        (tendsto_rpow_neg_atTop hneg).comp
          ((tendsto_natCast_atTop_atTop (R := ℝ)).comp
            (tendsto_add_atTop_nat 1))
    have hrpow_sub : Tendsto (fun n : ℕ =>
        Real.rpow (((8 * n + 1 : ℕ) : ℝ)) p)
        atTop (nhds 0) := by
      simpa [Function.comp_def] using hrpow.comp hsub_atTop
    have hc : sineValue 1 ≠ 0 := by
      unfold sineValue
      norm_num only [Nat.cast_one, one_mul]
      rw [Real.sin_pi_div_four]
      positivity
    have hone : Tendsto (fun n : ℕ => term p (8 * n + 1))
        atTop (nhds 1) := by
      have hconst : Tendsto (fun _ : ℕ => sineValue 1) atTop
          (nhds (sineValue 1)) := tendsto_const_nhds
      have hquot : Tendsto
          (fun n : ℕ => sineValue 1 /
            (Real.rpow (((8 * n + 1 : ℕ) : ℝ)) p + sineValue 1))
          atTop (nhds 1) := by
        have hquot0 :=
          hconst.div (hrpow_sub.add tendsto_const_nhds) (by simpa using hc)
        change Tendsto
          (fun n : ℕ => sineValue 1 /
            (Real.rpow (((8 * n + 1 : ℕ) : ℝ)) p + sineValue 1))
          atTop (nhds (sineValue 1 / (0 + sineValue 1))) at hquot0
        simpa only [zero_add, div_self hc] using hquot0
      convert hquot using 1
      · funext n
        rw [term, sineValue_eight_mul_add_one]
    have hzero_sub : Tendsto (fun n : ℕ => term p (8 * n + 1))
        atTop (nhds 0) := by
      simpa [Function.comp_def] using hzero.comp hsub_atTop
    have : (1 : ℝ) = 0 := tendsto_nhds_unique hone hzero_sub
    norm_num at this

theorem gap13 :
    ∀ p : ℝ, 0 < p → p ≤ 1 / 2 →
      ¬ Summable (fun n : ℕ => quadraticTerm p (n + 1)) := by
  intro p hp hp_half hsumm
  apply comparison_eight_mul_add_one_not_summable (2 * p) (by linarith) (by linarith)
  have hinj : Function.Injective (fun n : ℕ => 8 * n) := by
    intro a b hab
    exact Nat.mul_left_cancel (by norm_num) hab
  have hsub : Summable (fun n : ℕ => quadraticTerm p (8 * n + 1)) := by
    simpa [Function.comp_def] using hsumm.comp_injective hinj
  have hc : 0 < sineValue 1 := by
    unfold sineValue
    norm_num only [Nat.cast_one, one_mul]
    rw [Real.sin_pi_div_four]
    positivity
  have hscaled := hsub.mul_left (sineValue 1 ^ 2)⁻¹
  apply hscaled.congr
  intro n
  have hnpos : 0 < (((8 * n + 1 : ℕ) : ℝ)) := by positivity
  have hapos : 0 < Real.rpow (((8 * n + 1 : ℕ) : ℝ)) (2 * p) :=
    Real.rpow_pos_of_pos hnpos (2 * p)
  rw [quadraticTerm, sineValue_eight_mul_add_one]
  unfold comparison
  field_simp [hc.ne', hapos.ne']

theorem gap14 :
    ∀ p : ℝ, 0 < p → p ≤ 1 / 2 →
      ¬ Summable (fun n : ℕ => term p (n + 1)) := by
  intro p hp hp_half hterm
  have hleading : Summable (fun n : ℕ => leadingTerm p (n + 1)) :=
    summable_of_isBigO_nat hterm (leading_isBigO_term p hp)
  have habs : Summable (fun n : ℕ => |leadingTerm p (n + 1)|) := by
    simpa [Real.norm_eq_abs] using hleading.norm
  exact leading_abs_not_summable p hp (by linarith) habs

end

end ProofGap.Exercise2682

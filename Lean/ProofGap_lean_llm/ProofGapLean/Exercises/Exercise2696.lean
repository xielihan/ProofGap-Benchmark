import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ProofGap.Exercise2696

noncomputable section

open Filter
open Asymptotics
open scoped BigOperators
open scoped Topology

def groupedTerm (p q : ℝ) (k : ℕ) : ℝ :=
  1 / Real.rpow (3 * k + 1) p +
    1 / Real.rpow (3 * k + 2) p -
    2 / Real.rpow (3 * k + 3) q

def rawTerm (p q : ℝ) (n : ℕ) : ℝ :=
  match n % 3 with
  | 0 => 1 / Real.rpow (n + 1) p
  | 1 => 1 / Real.rpow (n + 1) p
  | _ => -(2 / Real.rpow (n + 1) q)

def absPartial (p q : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, |groupedTerm p q k|

def equalExponentRemainder (p : ℝ) (k : ℕ) : ℝ :=
  groupedTerm p p k - 3 * p / Real.rpow (3 * k) (p + 1)

def ConditionallySummable (f : ℕ → ℝ) : Prop :=
  ProofGap.SeriesConverges f ∧ ¬ Summable (fun n => |f n|)

private theorem one_add_rpow_sub_linear_isBigO (a : ℝ) :
    (fun x : ℝ => Real.rpow (1 + x) a - 1 - a * x) =O[𝓝 0]
      (fun x : ℝ => x ^ 2) := by
  have h :=
    (Real.one_add_rpow_hasFPowerSeriesAt_zero (a := a)).isBigO_sub_partialSum_pow 2
  convert h using 1
  · ext x
    simp [FormalMultilinearSeries.partialSum, binomialSeries, Finset.sum_range_succ,
      Ring.choose_zero_right, Ring.choose_one_right]
    ring
  · ext x
    simp [Real.norm_eq_abs, sq_abs]

private theorem shifted_rpow_remainder_isBigO (p c : ℝ) (hp : 0 < p) (hc : 0 ≤ c) :
    (fun k : ℕ =>
      1 / Real.rpow (3 * k + c) p - 1 / Real.rpow (3 * k) p +
        p * c / Real.rpow (3 * k) (p + 1)) =O[atTop]
      (fun k : ℕ => 1 / Real.rpow k (p + 2)) := by
  have ht : Tendsto (fun k : ℕ => c / (3 * (k : ℝ))) atTop (𝓝 0) := by
    convert tendsto_const_div_atTop_nhds_zero_nat (c / 3) using 1
    funext k
    by_cases hk : k = 0
    · simp [hk]
    · field_simp
  have hrem :
      (fun k : ℕ => Real.rpow (1 + c / (3 * (k : ℝ))) (-p) - 1 +
          p * (c / (3 * (k : ℝ)))) =O[atTop]
        (fun k : ℕ => (c / (3 * (k : ℝ))) ^ 2) := by
    simpa [sub_eq_add_neg] using
      (one_add_rpow_sub_linear_isBigO (-p)).comp_tendsto ht
  have hprod :
      (fun k : ℕ =>
        (1 / Real.rpow (3 * k) p) *
          (Real.rpow (1 + c / (3 * (k : ℝ))) (-p) - 1 +
            p * (c / (3 * (k : ℝ))))) =O[atTop]
        (fun k : ℕ =>
          (1 / Real.rpow (3 * k) p) * (c / (3 * (k : ℝ))) ^ 2) :=
    (isBigO_refl (fun k : ℕ => 1 / Real.rpow (3 * k) p) atTop).mul hrem
  have hscale :
      (fun k : ℕ =>
        (1 / Real.rpow (3 * k) p) * (c / (3 * (k : ℝ))) ^ 2) =O[atTop]
        (fun k : ℕ => 1 / Real.rpow k (p + 2)) := by
    refine isBigO_iff.2 ⟨c ^ 2, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (zero_lt_one.trans_le hk)
    have hxpos : (0 : ℝ) < 3 * k := mul_pos (by norm_num) hkpos
    have hexp : 0 ≤ p + 2 := by linarith
    have hkx : (k : ℝ) ≤ 3 * k := by nlinarith
    have hpow : Real.rpow k (p + 2) ≤ Real.rpow (3 * k) (p + 2) :=
      Real.rpow_le_rpow hkpos.le hkx hexp
    have hrec : 1 / Real.rpow (3 * k) (p + 2) ≤
        1 / Real.rpow k (p + 2) :=
      one_div_le_one_div_of_le (Real.rpow_pos_of_pos hkpos _) hpow
    have heq :
        (1 / Real.rpow (3 * k) p) * (c / (3 * (k : ℝ))) ^ 2 =
          c ^ 2 * (1 / Real.rpow (3 * k) (p + 2)) := by
      have hadd : Real.rpow (3 * k) (p + 2) =
          Real.rpow (3 * k) p * Real.rpow (3 * k) 2 :=
        Real.rpow_add hxpos p 2
      have htwo : Real.rpow (3 * k) 2 = (3 * (k : ℝ)) ^ 2 := Real.rpow_two _
      rw [hadd, htwo]
      field_simp [ne_of_gt (Real.rpow_pos_of_pos hxpos p)]
      <;> ring
    calc
      ‖(1 / Real.rpow (3 * k) p) * (c / (3 * (k : ℝ))) ^ 2‖ =
          c ^ 2 * (1 / Real.rpow (3 * k) (p + 2)) := by
            rw [heq]
            exact Real.norm_of_nonneg (mul_nonneg (sq_nonneg c)
              (one_div_nonneg.mpr (Real.rpow_nonneg hxpos.le _)))
      _ ≤ c ^ 2 * (1 / Real.rpow k (p + 2)) :=
        mul_le_mul_of_nonneg_left hrec (sq_nonneg c)
      _ = c ^ 2 * ‖1 / Real.rpow k (p + 2)‖ := by
        congr 1
        symm
        exact Real.norm_of_nonneg (one_div_nonneg.mpr (Real.rpow_nonneg hkpos.le _))
  refine (hprod.trans hscale).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (zero_lt_one.trans_le hk)
  have hxpos : (0 : ℝ) < 3 * k := mul_pos (by norm_num) hkpos
  have hxcpos : (0 : ℝ) < 3 * k + c := add_pos_of_pos_of_nonneg hxpos hc
  have honepos : (0 : ℝ) < 1 + c / (3 * k) := by positivity
  have hmul : 3 * (k : ℝ) + c = (3 * k) * (1 + c / (3 * k)) := by
    field_simp
  have hrpow_mul : Real.rpow (3 * k + c) p =
      Real.rpow (3 * k) p * Real.rpow (1 + c / (3 * k)) p := by
    rw [hmul]
    exact Real.mul_rpow hxpos.le honepos.le
  have hrpow_succ : Real.rpow (3 * k) (p + 1) =
      Real.rpow (3 * k) p * (3 * k) := by
    simpa using Real.rpow_add_one hxpos.ne' p
  have hrpow_neg : Real.rpow (1 + c / (3 * k)) (-p) =
      (Real.rpow (1 + c / (3 * k)) p)⁻¹ :=
    Real.rpow_neg honepos.le p
  rw [hrpow_mul, hrpow_neg, hrpow_succ]
  field_simp
  <;> ring

private theorem seriesConverges_iff_tendsto_sum_range (f : ℕ → ℝ) :
    ProofGap.SeriesConverges f ↔
      ∃ s : ℝ, Tendsto (fun N => ∑ n ∈ Finset.range N, f n) atTop (𝓝 s) := by
  simp only [ProofGap.SeriesConverges, Summable, HasSum,
    SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff, Function.comp_apply]
  constructor <;> rintro ⟨s, hs⟩ <;> refine ⟨s, ?_⟩
  · simpa [Function.comp_def] using hs
  · simpa [Function.comp_def] using hs

private theorem seriesConverges_tendsto_zero {f : ℕ → ℝ}
    (hf : ProofGap.SeriesConverges f) : Tendsto f atTop (𝓝 0) := by
  rcases (seriesConverges_iff_tendsto_sum_range f).mp hf with ⟨s, hs⟩
  have hs' := hs.comp (tendsto_add_atTop_nat 1)
  change Tendsto (fun n => ∑ i ∈ Finset.range (n + 1), f i) atTop (𝓝 s) at hs'
  have hdiff := hs'.sub hs
  convert hdiff using 1
  · ext n
    rw [Finset.sum_range_succ]
    ring
  · ring

private def rawCoeff (n : ℕ) : ℝ :=
  match n % 3 with
  | 0 => 1
  | 1 => 1
  | _ => -2

private theorem rawCoeff_sum_bound (N : ℕ) :
    ‖∑ n ∈ Finset.range N, rawCoeff n‖ ≤ 2 := by
  have hsum : ∀ M : ℕ,
      (∑ n ∈ Finset.range M, rawCoeff n) =
        if M % 3 = 0 then 0 else if M % 3 = 1 then 1 else 2 := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
        rw [Finset.sum_range_succ, ih]
        have hm : M % 3 < 3 := Nat.mod_lt _ (by omega)
        interval_cases h : M % 3 <;>
          simp [rawCoeff, h, Nat.add_mod] <;> norm_num
  rw [hsum N]
  split_ifs <;> norm_num

private theorem one_lt_of_summable_three_mul_succ {r : ℝ}
    (h : Summable (fun k : ℕ => 1 / Real.rpow (3 * k + 3) r)) : 1 < r := by
  have hshift : Summable (fun k : ℕ => 1 / Real.rpow (k + 1) r) := by
    have hm := h.mul_left (Real.rpow 3 r)
    convert hm using 1
    ext k
    have hrpow : Real.rpow (3 * ((k : ℝ) + 1)) r =
        Real.rpow 3 r * Real.rpow ((k : ℝ) + 1) r :=
      Real.mul_rpow (by norm_num) (by positivity)
    rw [show (3 : ℝ) * k + 3 = 3 * (k + 1) by ring, hrpow]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) r),
      ne_of_gt (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < k + 1) r)]
  have hbase : Summable (fun k : ℕ => 1 / Real.rpow k r) := by
    apply (summable_nat_add_iff 1).mp
    simpa [Nat.cast_add] using hshift
  exact Real.summable_one_div_nat_rpow.mp hbase

private theorem pseries_difference_not_seriesConverges
    (p q : ℝ) (hp : 0 < p) (hpq : p < q) (hp1 : p ≤ 1) :
    ¬ ProofGap.SeriesConverges
      (fun k : ℕ =>
        1 / Real.rpow (3 * k + 3) p - 1 / Real.rpow (3 * k + 3) q) := by
  let f : ℕ → ℝ := fun k =>
    1 / Real.rpow (3 * k + 3) p - 1 / Real.rpow (3 * k + 3) q
  have hf0 : ∀ k, 0 ≤ f k := by
    intro k
    have hx : (1 : ℝ) ≤ 3 * k + 3 := by
      norm_cast
      omega
    have hpow : Real.rpow (3 * k + 3) p ≤ Real.rpow (3 * k + 3) q :=
      Real.rpow_le_rpow_of_exponent_le hx hpq.le
    exact sub_nonneg.mpr
      (one_div_le_one_div_of_le
        (Real.rpow_pos_of_pos (zero_lt_one.trans_le hx) _) hpow)
  intro hconv
  rcases (seriesConverges_iff_tendsto_sum_range f).mp hconv with ⟨s, hs⟩
  rcases hs.bddAbove_range with ⟨C, hC⟩
  have hfsum : Summable f := summable_of_sum_range_le hf0 (fun N => hC ⟨N, rfl⟩)
  have hxTop : Tendsto (fun k : ℕ => 3 * (k : ℝ) + 3) atTop atTop :=
    tendsto_atTop_add_const_right atTop 3
      (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 3)
        tendsto_natCast_atTop_atTop)
  have hratio : Tendsto (fun k : ℕ => Real.rpow (3 * k + 3) (q - p)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hpq)).comp hxTop
  have hev : ∀ᶠ k : ℕ in atTop, (2 : ℝ) ≤ Real.rpow (3 * k + 3) (q - p) :=
    hratio.eventually (eventually_ge_atTop 2)
  have hdom : ∀ᶠ k : ℕ in atTop,
      1 / Real.rpow (3 * k + 3) p ≤ 2 * f k := by
    filter_upwards [hev] with k hk
    have hxpos : (0 : ℝ) < 3 * k + 3 := by positivity
    have hqsplit : Real.rpow (3 * k + 3) q =
        Real.rpow (3 * k + 3) p * Real.rpow (3 * k + 3) (q - p) := by
      calc
        Real.rpow (3 * k + 3) q = Real.rpow (3 * k + 3) (p + (q - p)) := by
          congr 1
          ring
        _ = _ := Real.rpow_add hxpos p (q - p)
    have hrel : Real.rpow (3 * k + 3) (q - p) *
          (1 / Real.rpow (3 * k + 3) q) =
        1 / Real.rpow (3 * k + 3) p := by
      rw [hqsplit]
      field_simp [ne_of_gt (Real.rpow_pos_of_pos hxpos p),
        ne_of_gt (Real.rpow_pos_of_pos hxpos (q - p))]
      apply mul_inv_cancel₀
      exact ne_of_gt (Real.rpow_pos_of_pos (by positivity) (q - p))
    have hsmall : 2 * (1 / Real.rpow (3 * k + 3) q) ≤
        1 / Real.rpow (3 * k + 3) p := by
      rw [← hrel]
      exact mul_le_mul_of_nonneg_right hk
        (one_div_nonneg.mpr (Real.rpow_nonneg hxpos.le _))
    simp only [f]
    linarith
  rcases eventually_atTop.1 hdom with ⟨K, hK⟩
  have hfshift : Summable (fun n : ℕ => f (n + K)) :=
    (summable_nat_add_iff K).mpr hfsum
  have hpshift : Summable
      (fun n : ℕ => 1 / Real.rpow (3 * (n + K) + 3) p) :=
    (hfshift.mul_left 2).of_nonneg_of_le
      (fun _ => one_div_nonneg.mpr (Real.rpow_nonneg (by positivity) _))
      (fun n => by
        simpa only [Nat.cast_add] using hK (n + K) (Nat.le_add_left K n))
  have hpseries : Summable (fun n : ℕ => 1 / Real.rpow (3 * n + 3) p) := by
    apply (summable_nat_add_iff K).mp
    simpa [Nat.cast_add] using hpshift
  exact (not_lt_of_ge hp1) (one_lt_of_summable_three_mul_succ hpseries)

private theorem raw_group_sum (p q : ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, groupedTerm p q k) =
      ∑ n ∈ Finset.range (3 * N), rawTerm p q n := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      rw [show 3 * (N + 1) = (((3 * N).succ).succ).succ by omega]
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
      have h0 : (3 * N) % 3 = 0 := by omega
      have h1 : (3 * N + 1) % 3 = 1 := by omega
      have h2 : (3 * N + 2) % 3 = 2 := by omega
      simp only [groupedTerm, rawTerm, h0, h1, h2]
      push_cast
      ring

theorem gap1 (p q : ℝ) (hp : 1 < p) (hq : 1 < q) :
    1 < min p q := by
  exact lt_min hp hq

theorem gap2 (p q : ℝ) (hp : 1 < p) (hq : 1 < q) :
    ∀ N : ℕ,
      absPartial p q N ≤
        4 * ∑ k ∈ Finset.range N,
          1 / Real.rpow (k + 1) (min p q) := by
  intro N
  have hr : 0 ≤ min p q := (le_min hp.le hq.le).trans' zero_le_one
  have hterm : ∀ k : ℕ,
      |groupedTerm p q k| ≤ 4 / Real.rpow (k + 1) (min p q) := by
    intro k
    have hbound (j : ℕ) (hj : 1 ≤ j) (hj3 : j ≤ 3) (s : ℝ)
        (hrs : min p q ≤ s) :
        1 / Real.rpow (3 * k + j) s ≤
          1 / Real.rpow (k + 1) (min p q) := by
      have hbase : (k + 1 : ℝ) ≤ 3 * (k : ℝ) + j := by
        norm_cast
        omega
      have hbase_one : (1 : ℝ) ≤ 3 * (k : ℝ) + j := by
        norm_cast
        omega
      have hpow : Real.rpow (k + 1) (min p q) ≤
          Real.rpow (3 * (k : ℝ) + j) s :=
        (Real.rpow_le_rpow (by positivity) hbase hr).trans
          (Real.rpow_le_rpow_of_exponent_le hbase_one hrs)
      exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by positivity) _) hpow
    have h1 : 1 / Real.rpow (3 * (k : ℝ) + 1) p ≤
        1 / Real.rpow (k + 1) (min p q) := by
      simpa only [Nat.cast_one] using hbound 1 (by omega) (by omega) p (min_le_left _ _)
    have h2 : 1 / Real.rpow (3 * (k : ℝ) + 2) p ≤
        1 / Real.rpow (k + 1) (min p q) := by
      simpa only [Nat.cast_ofNat] using hbound 2 (by omega) (by omega) p (min_le_left _ _)
    have h3 : 1 / Real.rpow (3 * (k : ℝ) + 3) q ≤
        1 / Real.rpow (k + 1) (min p q) := by
      simpa only [Nat.cast_ofNat] using hbound 3 (by omega) (by omega) q (min_le_right _ _)
    rw [groupedTerm]
    have ha : 0 ≤ 1 / Real.rpow (3 * k + 1) p :=
      one_div_nonneg.mpr (Real.rpow_nonneg (by positivity) _)
    have hb : 0 ≤ 1 / Real.rpow (3 * k + 2) p :=
      one_div_nonneg.mpr (Real.rpow_nonneg (by positivity) _)
    have hc : 0 ≤ 2 / Real.rpow (3 * k + 3) q :=
      div_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _)
    calc
      |1 / Real.rpow (3 * k + 1) p + 1 / Real.rpow (3 * k + 2) p -
          2 / Real.rpow (3 * k + 3) q|
          ≤ 1 / Real.rpow (3 * k + 1) p + 1 / Real.rpow (3 * k + 2) p +
              2 / Real.rpow (3 * k + 3) q := by
            rw [abs_le]
            constructor <;> linarith
      _ ≤ 4 / Real.rpow (k + 1) (min p q) := by
        have h3' : 2 / Real.rpow (3 * k + 3) q ≤
            2 * (1 / Real.rpow (k + 1) (min p q)) := by
          calc
            _ = 2 * (1 / Real.rpow (3 * k + 3) q) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by norm_num)
        calc
          _ ≤ 1 / Real.rpow (k + 1) (min p q) +
                1 / Real.rpow (k + 1) (min p q) +
                2 * (1 / Real.rpow (k + 1) (min p q)) := add_le_add (add_le_add h1 h2) h3'
          _ = 4 / Real.rpow (k + 1) (min p q) := by ring
  rw [absPartial]
  calc
    _ ≤ ∑ k ∈ Finset.range N, 4 / Real.rpow (k + 1) (min p q) :=
      Finset.sum_le_sum fun k _ => hterm k
    _ = 4 * ∑ k ∈ Finset.range N, 1 / Real.rpow (k + 1) (min p q) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring

theorem gap3 (p q : ℝ) (hp : 1 < p) (hq : 1 < q) :
    Summable (fun k : ℕ => 4 / Real.rpow (k + 1) (min p q)) := by
  have hbase : Summable (fun k : ℕ => 1 / Real.rpow k (min p q)) :=
    Real.summable_one_div_nat_rpow.mpr (gap1 p q hp hq)
  have hshift : Summable (fun k : ℕ => 1 / Real.rpow (k + 1) (min p q)) := by
    simpa [Nat.cast_add] using (summable_nat_add_iff 1).mpr hbase
  convert hshift.mul_left 4 using 1
  ext k
  ring

theorem gap4 (p q : ℝ) (hp : 1 < p) (hq : 1 < q) :
    ∃ C : ℝ, ∀ N : ℕ, absPartial p q N ≤ C := by
  let f : ℕ → ℝ := fun k => 4 / Real.rpow (k + 1) (min p q)
  have hf : Summable f := gap3 p q hp hq
  refine ⟨∑' k, f k, fun N => ?_⟩
  calc
    absPartial p q N ≤ 4 * ∑ k ∈ Finset.range N,
        1 / Real.rpow (k + 1) (min p q) := gap2 p q hp hq N
    _ = ∑ k ∈ Finset.range N, f k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [f]
      ring
    _ ≤ ∑' k, f k := hf.sum_le_tsum _ (fun k _ => by
      simp only [f]
      exact div_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _))

theorem gap5 (p q : ℝ) :
    Monotone (absPartial p q) := by
  apply monotone_nat_of_le_succ
  intro N
  rw [absPartial, absPartial, Finset.sum_range_succ]
  exact le_add_of_nonneg_right (abs_nonneg _)

theorem gap6 (p q : ℝ) (hp : 1 < p) (hq : 1 < q) :
    BddAbove (Set.range (absPartial p q)) := by
  rcases gap4 p q hp hq with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  rintro _ ⟨N, rfl⟩
  exact hC N

theorem gap7 (p q : ℝ) (hp : 1 < p) (hq : 1 < q) :
    Summable (fun k : ℕ => |groupedTerm p q k|) := by
  rcases gap4 p q hp hq with ⟨C, hC⟩
  apply summable_of_sum_range_le (fun _ => abs_nonneg _)
  intro N
  exact hC N

theorem gap8 :
    ¬ Summable (fun k : ℕ => 1 / ((k : ℝ) + 1)) := by
  intro h
  apply Real.not_summable_one_div_natCast
  apply (summable_nat_add_iff 1).mp
  simpa [Nat.cast_add] using h

theorem gap9 (p : ℝ) (hp₀ : 0 < p) (hp₁ : p ≤ 1) :
    ¬ Summable (fun n : ℕ => |rawTerm p p n|) := by
  intro hraw
  have hpoint : ∀ n : ℕ,
      1 / Real.rpow (n + 1) p ≤ |rawTerm p p n| := by
    intro n
    have hn : n % 3 < 3 := Nat.mod_lt _ (by omega)
    have hu : 0 ≤ 1 / Real.rpow (n + 1) p :=
      one_div_nonneg.mpr (Real.rpow_nonneg (by positivity) _)
    have hd : 0 ≤ Real.rpow (n + 1) p := Real.rpow_nonneg (by positivity) _
    interval_cases h : n % 3
    · simp only [rawTerm, h]
      rw [abs_of_nonneg hu]
    · simp only [rawTerm, h]
      rw [abs_of_nonneg hu]
    · simp only [rawTerm, h, abs_neg]
      have htwo : 0 ≤ 2 / Real.rpow (n + 1) p := by positivity
      rw [abs_of_nonneg htwo]
      rw [show 2 / Real.rpow (n + 1) p =
        2 * (1 / Real.rpow (n + 1) p) by ring]
      linarith
  have hshift : Summable (fun n : ℕ => 1 / Real.rpow (n + 1) p) :=
    hraw.of_nonneg_of_le
      (fun n => one_div_nonneg.mpr (Real.rpow_nonneg (by positivity) _)) hpoint
  have hbase : Summable (fun n : ℕ => 1 / Real.rpow n p) := by
    apply (summable_nat_add_iff 1).mp
    simpa [Nat.cast_add] using hshift
  have : 1 < p := Real.summable_one_div_nat_rpow.mp hbase
  linarith

theorem gap10 (p : ℝ) (hp₀ : 0 < p) :
    (∀ k : ℕ, 1 ≤ k →
      groupedTerm p p k =
        3 * p / Real.rpow (3 * k) (p + 1) +
          equalExponentRemainder p k) ∧
    Asymptotics.IsBigO atTop (equalExponentRemainder p)
      (fun k : ℕ => 1 / Real.rpow k (p + 2)) := by
  constructor
  · intro k hk
    rw [equalExponentRemainder]
    ring
  · have h1 := shifted_rpow_remainder_isBigO p 1 hp₀ (by norm_num)
    have h2 := shifted_rpow_remainder_isBigO p 2 hp₀ (by norm_num)
    have h3 := shifted_rpow_remainder_isBigO p 3 hp₀ (by norm_num)
    have h := (h1.add h2).sub (h3.const_mul_left 2)
    convert h using 1
    ext k
    simp only [equalExponentRemainder, groupedTerm]
    ring

theorem gap11 (p : ℝ) (hp₀ : 0 < p) :
    Summable (fun k : ℕ => groupedTerm p p (k + 1)) := by
  have hbase : Summable (fun k : ℕ => 1 / Real.rpow (k + 1) (p + 1)) := by
    have h : Summable (fun k : ℕ => 1 / Real.rpow k (p + 1)) :=
      Real.summable_one_div_nat_rpow.mpr (by linarith)
    simpa [Nat.cast_add] using (summable_nat_add_iff 1).mpr h
  have hlead : Summable
      (fun k : ℕ => 3 * p / Real.rpow (3 * (k + 1)) (p + 1)) := by
    have hmul := hbase.mul_left (3 * p / Real.rpow 3 (p + 1))
    convert hmul using 1
    ext k
    have hrpow : Real.rpow (3 * ((k : ℝ) + 1)) (p + 1) =
        Real.rpow 3 (p + 1) * Real.rpow ((k : ℝ) + 1) (p + 1) :=
      Real.mul_rpow (by norm_num) (by positivity)
    rw [hrpow]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) (p + 1)),
      ne_of_gt (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < k + 1) (p + 1))]
    <;> ring
  have hg : Summable (fun k : ℕ => 1 / Real.rpow k (p + 2)) :=
    Real.summable_one_div_nat_rpow.mpr (by linarith)
  have hrem : Summable (equalExponentRemainder p) := by
    apply summable_of_isBigO hg
    rw [Nat.cofinite_eq_atTop]
    exact (gap10 p hp₀).2
  have hremShift : Summable (fun k => equalExponentRemainder p (k + 1)) :=
    (summable_nat_add_iff 1).mpr hrem
  have hsum := hlead.add hremShift
  convert hsum using 1
  ext k
  simpa [Nat.cast_add] using (gap10 p hp₀).1 (k + 1) (by omega)

theorem gap12 (p : ℝ) (hp₀ : 0 < p) (hp₁ : p ≤ 1) :
    ConditionallySummable (fun n : ℕ => rawTerm p p n) := by
  constructor
  · let u : ℕ → ℝ := fun n => 1 / Real.rpow (n + 1) p
    have huanti : Antitone u := by
      intro m n hmn
      have hbase : (m + 1 : ℝ) ≤ n + 1 := by exact_mod_cast Nat.add_le_add_right hmn 1
      have hpow : Real.rpow (m + 1) p ≤ Real.rpow (n + 1) p :=
        Real.rpow_le_rpow (by positivity) hbase hp₀.le
      exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by positivity) _) hpow
    have hu0 : Tendsto u atTop (𝓝 0) := by
      have hx : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
        tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
      have h := (tendsto_rpow_atTop hp₀).comp hx
      simpa [u] using h.inv_tendsto_atTop
    have hraw : ∀ n : ℕ, rawTerm p p n = u n * rawCoeff n := by
      intro n
      have hn : n % 3 < 3 := Nat.mod_lt _ (by omega)
      interval_cases h : n % 3 <;> simp [rawTerm, rawCoeff, u, h] <;> ring
    have hcauchy : CauchySeq
        (fun N => ∑ n ∈ Finset.range N, u n • rawCoeff n) :=
      huanti.cauchySeq_series_mul_of_tendsto_zero_of_bounded hu0 rawCoeff_sum_bound
    rcases cauchySeq_tendsto_of_complete hcauchy with ⟨s, hs⟩
    apply (seriesConverges_iff_tendsto_sum_range _).mpr
    refine ⟨s, ?_⟩
    convert hs using 1
    ext N
    apply Finset.sum_congr rfl
    intro n hn
    simp only [hraw n, smul_eq_mul]
  · exact gap9 p hp₀ hp₁

theorem gap13 (p q : ℝ) (h : p ≤ 0 ∨ q ≤ 0) :
    ¬ ProofGap.SeriesConverges (fun n : ℕ => rawTerm p q n) := by
  intro hconv
  have hzero := seriesConverges_tendsto_zero hconv
  rcases h with hp | hq
  · have hsub : Tendsto (fun k : ℕ => rawTerm p q (3 * k)) atTop (𝓝 0) :=
      hzero.comp (tendsto_id.nsmul_atTop (by norm_num : (0 : ℕ) < 3))
    have hev : ∀ᶠ k in atTop, rawTerm p q (3 * k) < (1 / 2 : ℝ) :=
      hsub.eventually (Iio_mem_nhds (by norm_num))
    rcases hev.exists with ⟨k, hk⟩
    have hbase : (1 : ℝ) ≤ ((3 * k : ℕ) : ℝ) + 1 := by
      norm_cast
      omega
    have hden : Real.rpow (((3 * k : ℕ) : ℝ) + 1) p ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hbase hp
    have hdenpos : 0 < Real.rpow (((3 * k : ℕ) : ℝ) + 1) p :=
      Real.rpow_pos_of_pos (by positivity) _
    have hge : (1 : ℝ) ≤ rawTerm p q (3 * k) := by
      have hmod : (3 * k) % 3 = 0 := by omega
      simp only [rawTerm, hmod]
      exact one_le_one_div hdenpos hden
    linarith
  · have hmap : Tendsto (fun k : ℕ => 3 * k + 2) atTop atTop :=
      (tendsto_add_atTop_nat 2).comp
        (tendsto_id.nsmul_atTop (by norm_num : (0 : ℕ) < 3))
    have hsub : Tendsto (fun k : ℕ => rawTerm p q (3 * k + 2)) atTop (𝓝 0) :=
      hzero.comp hmap
    have hev : ∀ᶠ k in atTop, (-1 : ℝ) < rawTerm p q (3 * k + 2) :=
      hsub.eventually (Ioi_mem_nhds (by norm_num))
    rcases hev.exists with ⟨k, hk⟩
    have hbase : (1 : ℝ) ≤ ((3 * k + 2 : ℕ) : ℝ) + 1 := by
      norm_cast
      omega
    have hden : Real.rpow (((3 * k + 2 : ℕ) : ℝ) + 1) q ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hbase hq
    have hdenpos : 0 < Real.rpow (((3 * k + 2 : ℕ) : ℝ) + 1) q :=
      Real.rpow_pos_of_pos (by positivity) _
    have hone : (1 : ℝ) ≤ 1 / Real.rpow (((3 * k + 2 : ℕ) : ℝ) + 1) q :=
      one_le_one_div hdenpos hden
    have hle : rawTerm p q (3 * k + 2) ≤ (-2 : ℝ) := by
      have hmod : (3 * k + 2) % 3 = 2 := by omega
      simp only [rawTerm, hmod]
      rw [show 2 / Real.rpow (((3 * k + 2 : ℕ) : ℝ) + 1) q =
        2 * (1 / Real.rpow (((3 * k + 2 : ℕ) : ℝ) + 1) q) by ring]
      linarith
    linarith

theorem gap14 (p q : ℝ) :
    (Summable (fun n : ℕ => |rawTerm p q n|) ↔ 1 < p ∧ 1 < q) ∧
    (ConditionallySummable (fun n : ℕ => rawTerm p q n) ↔
      0 < p ∧ p = q ∧ p ≤ 1) ∧
    (¬ ProofGap.SeriesConverges (fun n : ℕ => rawTerm p q n) ↔
      (p ≤ 0 ∨ q ≤ 0) ∨
        (0 < p ∧ 0 < q ∧ p ≠ q ∧ (p ≤ 1 ∨ q ≤ 1))) := by
  have ordered_of_summable {f : ℕ → ℝ} (hf : Summable f) :
      ProofGap.SeriesConverges f :=
    hf.mono_filter (SummationFilter.conditional ℕ).le_atTop
  have habsIff : Summable (fun n : ℕ => |rawTerm p q n|) ↔ 1 < p ∧ 1 < q := by
    constructor
    · intro habs
      have hpSub : Summable (fun k : ℕ => 1 / Real.rpow (3 * k + 1) p) := by
        have h := habs.comp_injective (i := fun k : ℕ => 3 * k) (by
          intro a b hab
          exact Nat.mul_left_cancel (by omega : 0 < 3) hab)
        convert h using 1
        ext k
        have hmod : (3 * k) % 3 = 0 := by omega
        simp only [Function.comp_apply, rawTerm, hmod]
        have habsEq :
            |1 / Real.rpow (((3 * k : ℕ) : ℝ) + 1) p| =
              1 / Real.rpow (((3 * k : ℕ) : ℝ) + 1) p :=
          abs_of_nonneg (one_div_nonneg.mpr (Real.rpow_nonneg (by positivity) _))
        rw [habsEq]
        norm_num [Nat.cast_mul]
      have hp0 : 0 < p := by
        by_contra hnp
        have hpnon : p ≤ 0 := le_of_not_gt hnp
        have hz := hpSub.tendsto_atTop_zero
        have hev : ∀ᶠ k : ℕ in atTop,
            1 / Real.rpow (3 * k + 1) p < (1 / 2 : ℝ) :=
          hz.eventually (Iio_mem_nhds (by norm_num))
        rcases hev.exists with ⟨k, hk⟩
        have hx : (1 : ℝ) ≤ 3 * k + 1 := by
          norm_cast
          omega
        have hd : Real.rpow (3 * k + 1) p ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos hx hpnon
        have hge : (1 : ℝ) ≤ 1 / Real.rpow (3 * k + 1) p :=
          one_le_one_div (Real.rpow_pos_of_pos (by positivity) _) hd
        linarith
      have hpW : Summable (fun k : ℕ => 1 / Real.rpow (3 * k + 3) p) :=
        hpSub.of_nonneg_of_le
          (fun _ => one_div_nonneg.mpr (Real.rpow_nonneg (by positivity) _))
          (fun k => by
            have hbase : (3 * k + 1 : ℝ) ≤ 3 * k + 3 := by norm_num
            have hpow : Real.rpow (3 * k + 1) p ≤ Real.rpow (3 * k + 3) p :=
              Real.rpow_le_rpow (by positivity) hbase hp0.le
            exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by positivity) _) hpow)
      have hp1 : 1 < p := one_lt_of_summable_three_mul_succ hpW
      have hqAbs : Summable (fun k : ℕ => |rawTerm p q (3 * k + 2)|) :=
        habs.comp_injective (i := fun k : ℕ => 3 * k + 2) (by
          intro a b hab
          have hmul : 3 * a = 3 * b := Nat.add_right_cancel hab
          exact Nat.mul_left_cancel (by omega : 0 < 3) hmul)
      have hqW : Summable (fun k : ℕ => 1 / Real.rpow (3 * k + 3) q) := by
        have hm := hqAbs.mul_left (1 / 2 : ℝ)
        convert hm using 1
        ext k
        have hmod : (3 * k + 2) % 3 = 2 := by omega
        simp only [rawTerm, hmod, abs_neg]
        have hnon : 0 ≤ 2 / Real.rpow (((3 * k + 2 : ℕ) : ℝ) + 1) q :=
          div_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _)
        rw [abs_of_nonneg hnon]
        push_cast
        ring
      exact ⟨hp1, one_lt_of_summable_three_mul_succ hqW⟩
    · rintro ⟨hp, hq⟩
      have hpS : Summable (fun n : ℕ => 1 / Real.rpow (n + 1) p) := by
        have h := Real.summable_one_div_nat_rpow.mpr hp
        simpa [Nat.cast_add] using (summable_nat_add_iff 1).mpr h
      have hqS : Summable (fun n : ℕ => 2 / Real.rpow (n + 1) q) := by
        have h : Summable (fun n : ℕ => 1 / Real.rpow (n + 1) q) := by
          have h' := Real.summable_one_div_nat_rpow.mpr hq
          simpa [Nat.cast_add] using (summable_nat_add_iff 1).mpr h'
        convert h.mul_left 2 using 1
        ext n
        ring
      apply (hpS.add hqS).of_nonneg_of_le (fun _ => abs_nonneg _)
      intro n
      have hn : n % 3 < 3 := Nat.mod_lt _ (by omega)
      have hpnon : 0 ≤ 1 / Real.rpow (n + 1) p :=
        one_div_nonneg.mpr (Real.rpow_nonneg (by positivity) _)
      have hqnon : 0 ≤ 2 / Real.rpow (n + 1) q :=
        div_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _)
      interval_cases hmod : n % 3
      · simp only [rawTerm, hmod]
        rw [abs_of_nonneg hpnon]
        linarith
      · simp only [rawTerm, hmod]
        rw [abs_of_nonneg hpnon]
        linarith
      · simp only [rawTerm, hmod, abs_neg]
        rw [abs_of_nonneg hqnon]
        linarith
  have hconv_of_abs (h : 1 < p ∧ 1 < q) :
      ProofGap.SeriesConverges (fun n : ℕ => rawTerm p q n) := by
    have habs := habsIff.mpr h
    have hu : Summable (fun n : ℕ => rawTerm p q n) := by
      rw [← summable_norm_iff]
      simpa [Real.norm_eq_abs] using habs
    exact ordered_of_summable hu
  have hunequal (hp : 0 < p) (hq : 0 < q) (hpq : p ≠ q)
      (hlow : p ≤ 1 ∨ q ≤ 1) :
      ¬ ProofGap.SeriesConverges (fun n : ℕ => rawTerm p q n) := by
    intro hraw
    rcases (seriesConverges_iff_tendsto_sum_range _).mp hraw with ⟨s, hs⟩
    have hs3 := hs.comp (tendsto_id.nsmul_atTop (by norm_num : (0 : ℕ) < 3))
    have hgroup : ProofGap.SeriesConverges (groupedTerm p q) := by
      apply (seriesConverges_iff_tendsto_sum_range _).mpr
      refine ⟨s, ?_⟩
      convert hs3 using 1
      ext N
      exact raw_group_sum p q N
    have heqSum : Summable (groupedTerm p p) :=
      (summable_nat_add_iff 1).mp (gap11 p hp)
    have heqConv : ProofGap.SeriesConverges (groupedTerm p p) :=
      ordered_of_summable heqSum
    have hdiff0 := hgroup.sub heqConv
    have hdiff : ProofGap.SeriesConverges
        (fun k : ℕ =>
          1 / Real.rpow (3 * k + 3) p - 1 / Real.rpow (3 * k + 3) q) := by
      have hh := hdiff0.mul_left (1 / 2 : ℝ)
      apply hh.congr
      intro k
      simp only [groupedTerm]
      ring
    rcases lt_or_gt_of_ne hpq with hpqlt | hqplt
    · exact pseries_difference_not_seriesConverges p q hp hpqlt (by rcases hlow with h | h <;> linarith) hdiff
    · have hneg := hdiff.neg
      apply pseries_difference_not_seriesConverges q p hq hqplt
        (by rcases hlow with h | h <;> linarith)
      apply hneg.congr
      intro k
      ring
  have hconvIff : ProofGap.SeriesConverges (fun n : ℕ => rawTerm p q n) ↔
      (1 < p ∧ 1 < q) ∨ (0 < p ∧ p = q ∧ p ≤ 1) := by
    constructor
    · intro hc
      by_cases ha : 1 < p ∧ 1 < q
      · exact Or.inl ha
      · right
        have hp : 0 < p := by
          by_contra h
          exact gap13 p q (Or.inl (le_of_not_gt h)) hc
        have hq : 0 < q := by
          by_contra h
          exact gap13 p q (Or.inr (le_of_not_gt h)) hc
        have hlow : p ≤ 1 ∨ q ≤ 1 := by
          by_cases hp1 : p ≤ 1
          · exact Or.inl hp1
          · right
            by_contra hq1
            apply ha
            exact ⟨by linarith, by linarith⟩
        have hpq : p = q := by
          by_contra hne
          exact hunequal hp hq hne hlow hc
        exact ⟨hp, hpq, by rcases hlow with h | h <;> linarith⟩
    · rintro (habs | hcond)
      · exact hconv_of_abs habs
      · rcases hcond with ⟨hp, rfl, hp1⟩
        exact (gap12 p hp hp1).1
  refine ⟨habsIff, ?_, ?_⟩
  · constructor
    · rintro ⟨hc, hna⟩
      rcases hconvIff.mp hc with habs | hcond
      · exact False.elim (hna (habsIff.mpr habs))
      · exact hcond
    · rintro ⟨hp, rfl, hp1⟩
      exact gap12 p hp hp1
  · rw [hconvIff]
    constructor
    · intro hn
      by_cases hp : 0 < p
      · by_cases hq : 0 < q
        · right
          refine ⟨hp, hq, ?_, ?_⟩
          · intro hpq
            apply hn
            subst q
            by_cases hp1 : p ≤ 1
            · exact Or.inr ⟨hp, rfl, hp1⟩
            · exact Or.inl ⟨by linarith, by linarith⟩
          · by_contra hlow
            push_neg at hlow
            exact hn (Or.inl ⟨hlow.1, hlow.2⟩)
        · exact Or.inl (Or.inr (le_of_not_gt hq))
      · exact Or.inl (Or.inl (le_of_not_gt hp))
    · rintro (hnon | ⟨hp, hq, hpq, hlow⟩)
      · intro hc
        rcases hnon with hp0 | hq0
        · rcases hc with habs | hcond <;> linarith
        · rcases hc with habs | hcond
          · linarith
          · rcases hcond with ⟨_, hpq, _⟩
            subst q
            linarith
      · intro hc
        rcases hc with habs | hcond
        · rcases hlow with hp1 | hq1 <;> linarith
        · exact hpq hcond.2.1

end

end ProofGap.Exercise2696

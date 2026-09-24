import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace ProofGap.Exercise2829

noncomputable section

open Filter
open scoped BigOperators Topology

def oscillatingBase (n : ℕ) : ℝ :=
  1 + 2 * Real.cos (Real.pi * n / 4)

def coefficient (n : ℕ) : ℝ :=
  oscillatingBase n ^ n / Real.log n

def powerTerm (n : ℕ) (x : ℝ) : ℝ :=
  coefficient n * x ^ n

def SeriesConvergesAt (x : ℝ) : Prop :=
  Summable (fun k : ℕ => powerTerm (k + 2) x)

def HasConvergenceRadiusThird : Prop :=
  (∀ x : ℝ, |x| < 1 / 3 → SeriesConvergesAt x) ∧
    (∀ x : ℝ, 1 / 3 < |x| → ¬ SeriesConvergesAt x)

def nonPeakTerm (n : ℕ) (x : ℝ) : ℝ :=
  if n % 8 = 0 then 0 else powerTerm n x

private theorem oscillatingBase_mod (n : ℕ) :
    oscillatingBase n = oscillatingBase (n % 8) := by
  unfold oscillatingBase
  have hn :
      (n : ℝ) = (n % 8 : ℕ) + 8 * (n / 8 : ℕ) := by
    exact_mod_cast (Nat.mod_add_div n 8).symm
  rw [hn]
  rw [show Real.pi * ((n % 8 : ℕ) + 8 * (n / 8 : ℕ)) / 4 =
      Real.pi * (n % 8 : ℕ) / 4 +
        (n / 8 : ℕ) * (2 * Real.pi) by
    ring]
  rw [Real.cos_add_nat_mul_two_pi]

private theorem oscillatingBase_eight_mul (k : ℕ) :
    oscillatingBase (8 * k) = 3 := by
  rw [oscillatingBase_mod]
  norm_num [oscillatingBase]

private theorem cos_three_pi_div_four :
    Real.cos (3 * Real.pi / 4) = -(Real.sqrt 2 / 2) := by
  rw [show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 by ring]
  rw [Real.cos_pi_sub, Real.cos_pi_div_four]

private theorem cos_five_pi_div_four :
    Real.cos (5 * Real.pi / 4) = -(Real.sqrt 2 / 2) := by
  rw [show 5 * Real.pi / 4 = Real.pi / 4 + Real.pi by ring]
  rw [Real.cos_add_pi, Real.cos_pi_div_four]

private theorem cos_six_pi_div_four :
    Real.cos (6 * Real.pi / 4) = 0 := by
  rw [show 6 * Real.pi / 4 = Real.pi / 2 + Real.pi by ring]
  rw [Real.cos_add_pi, Real.cos_pi_div_two, neg_zero]

private theorem cos_seven_pi_div_four :
    Real.cos (7 * Real.pi / 4) = Real.sqrt 2 / 2 := by
  rw [show 7 * Real.pi / 4 = 2 * Real.pi - Real.pi / 4 by ring]
  rw [Real.cos_two_pi_sub, Real.cos_pi_div_four]

private theorem nonpeak_base_bound (n : ℕ) (hn : n % 8 ≠ 0) :
    |oscillatingBase n| ≤ 1 + Real.sqrt 2 := by
  rw [oscillatingBase_mod]
  have hrange : n % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have hm :
      n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 3 ∨ n % 8 = 4 ∨
        n % 8 = 5 ∨ n % 8 = 6 ∨ n % 8 = 7 := by
    omega
  rcases hm with h | h | h | h | h | h | h
  · rw [h]
    simp only [oscillatingBase]
    rw [show Real.pi * ((1 : ℕ) : ℝ) / 4 = Real.pi / 4 by norm_num,
      Real.cos_pi_div_four]
    have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    rw [abs_of_nonneg (by nlinarith)]
    ring_nf
    exact le_rfl
  · rw [h]
    simp only [oscillatingBase, Nat.cast_ofNat]
    rw [show Real.pi * (2 : ℝ) / 4 = Real.pi / 2 by ring,
      Real.cos_pi_div_two]
    norm_num
  · rw [h]
    simp only [oscillatingBase, Nat.cast_ofNat]
    rw [show Real.pi * (3 : ℝ) / 4 = 3 * Real.pi / 4 by ring,
      cos_three_pi_div_four]
    have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    have hs1 : 1 ≤ Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    rw [abs_of_nonpos (by nlinarith)]
    nlinarith
  · rw [h]
    simp only [oscillatingBase, Nat.cast_ofNat]
    rw [show Real.pi * (4 : ℝ) / 4 = Real.pi by ring,
      Real.cos_pi]
    norm_num
  · rw [h]
    simp only [oscillatingBase, Nat.cast_ofNat]
    rw [show Real.pi * (5 : ℝ) / 4 = 5 * Real.pi / 4 by ring,
      cos_five_pi_div_four]
    have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    have hs1 : 1 ≤ Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    rw [abs_of_nonpos (by nlinarith)]
    nlinarith
  · rw [h]
    simp only [oscillatingBase, Nat.cast_ofNat]
    rw [show Real.pi * (6 : ℝ) / 4 = 6 * Real.pi / 4 by ring,
      cos_six_pi_div_four]
    norm_num
  · rw [h]
    simp only [oscillatingBase, Nat.cast_ofNat]
    rw [show Real.pi * (7 : ℝ) / 4 = 7 * Real.pi / 4 by ring,
      cos_seven_pi_div_four]
    have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    rw [abs_of_nonneg (by nlinarith)]
    ring_nf
    exact le_rfl

private theorem oscillatingBase_abs_le_three (n : ℕ) :
    |oscillatingBase n| ≤ 3 := by
  unfold oscillatingBase
  calc
    |1 + 2 * Real.cos (Real.pi * n / 4)| ≤
        |(1 : ℝ)| + |2 * Real.cos (Real.pi * n / 4)| := abs_add_le _ _
    _ = 1 + 2 * |Real.cos (Real.pi * n / 4)| := by
      rw [abs_mul]
      norm_num
    _ ≤ 3 := by nlinarith [Real.abs_cos_le_one (Real.pi * n / 4)]

private theorem abs_powerTerm_eq_of_abs_eq
    (n : ℕ) {x y : ℝ} (hxy : |x| = |y|) :
    |powerTerm n x| = |powerTerm n y| := by
  unfold powerTerm
  simp only [abs_mul, abs_pow]
  rw [hxy]

private theorem abs_peak_term (k : ℕ) (hk : 1 ≤ k) (x : ℝ) :
    |powerTerm (8 * k) x| =
      (3 * |x|) ^ (8 * k) / Real.log (8 * k) := by
  have hn1 : 1 < (8 * k : ℕ) := by omega
  have hlog : 0 < Real.log (8 * k) :=
    Real.log_pos (by exact_mod_cast hn1)
  unfold powerTerm coefficient
  push_cast
  rw [oscillatingBase_eight_mul]
  rw [abs_mul, abs_div, abs_pow,
    show |Real.log (8 * (k : ℝ))| = Real.log (8 * (k : ℝ)) from
      abs_of_pos hlog,
    abs_pow]
  rw [mul_pow]
  ring

private theorem coefficient_abs_formula (n : ℕ)
    (hlog : 0 < Real.log (n : ℝ)) :
    |coefficient n| =
      |oscillatingBase n| ^ n / Real.log (n : ℝ) := by
  unfold coefficient
  rw [abs_div, abs_pow, abs_of_pos hlog]

private theorem coefficient_root_formula (n : ℕ) (hn : 2 ≤ n) :
    Real.rpow |coefficient n| (1 / (n : ℝ)) =
      |oscillatingBase n| /
        Real.rpow (Real.log n) (1 / (n : ℝ)) := by
  have hn0 : n ≠ 0 := by omega
  have hlog : 0 < Real.log (n : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < n by omega)
  rw [coefficient_abs_formula n hlog]
  calc
    Real.rpow
        (|oscillatingBase n| ^ n / Real.log (n : ℝ))
        (1 / (n : ℝ)) =
        Real.rpow (|oscillatingBase n| ^ n) (1 / (n : ℝ)) /
          Real.rpow (Real.log (n : ℝ)) (1 / (n : ℝ)) :=
      Real.div_rpow (pow_nonneg (abs_nonneg _) _) hlog.le _
    _ = |oscillatingBase n| /
          Real.rpow (Real.log (n : ℝ)) (1 / (n : ℝ)) := by
      congr 1
      simpa only [one_div] using
        Real.pow_rpow_inv_natCast (abs_nonneg (oscillatingBase n)) hn0

private theorem tendsto_log_rpow_inv_natCast :
    Tendsto
      (fun n : ℕ =>
        Real.rpow (Real.log n) (1 / (n : ℝ)))
      atTop (𝓝 1) := by
  have hlog_div :
      Tendsto
        (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ))
        atTop (𝓝 0) := by
    simpa only [Function.comp_apply, pow_one, one_mul, add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
        tendsto_natCast_atTop_atTop
  have hlog_log_div :
      Tendsto
        (fun n : ℕ =>
          Real.log (Real.log (n : ℝ)) / (n : ℝ))
        atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hlog_div ?_ ?_
    · filter_upwards [eventually_ge_atTop 3] with n hn
      have hlogn : 1 < Real.log (n : ℝ) := by
        have hlog3 : 1 < Real.log 3 :=
          (Real.lt_log_iff_exp_lt (by norm_num)).2 Real.exp_one_lt_three
        exact hlog3.trans_le
          (Real.log_le_log (by norm_num) (by exact_mod_cast hn))
      exact div_nonneg (Real.log_nonneg hlogn.le)
        (Nat.cast_nonneg _)
    · filter_upwards [eventually_ge_atTop 3] with n hn
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
      have hlogn : 0 ≤ Real.log (n : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
      exact div_le_div_of_nonneg_right (Real.log_le_self hlogn) hnpos.le
  have hexp :
      Tendsto
        (fun n : ℕ =>
          Real.exp (Real.log (Real.log (n : ℝ)) / (n : ℝ)))
        atTop (𝓝 1) :=
    Real.tendsto_exp_nhds_zero_nhds_one.comp hlog_log_div
  apply hexp.congr'
  filter_upwards [eventually_ge_atTop 3] with n hn
  have hlogn : 0 < Real.log (n : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < n by omega)
  calc
    Real.exp (Real.log (Real.log (n : ℝ)) / (n : ℝ)) =
        Real.exp
          (Real.log (Real.log (n : ℝ)) * (1 / (n : ℝ))) := by
      congr 1
      ring
    _ = Real.rpow (Real.log (n : ℝ)) (1 / (n : ℝ)) :=
      (Real.rpow_def_of_pos hlogn _).symm

private theorem series_summable_inside
    (x : ℝ) (hx : |x| < 1 / 3) :
    SeriesConvergesAt x := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq_nonneg : 0 ≤ 3 * |x| := mul_nonneg (by norm_num) (abs_nonneg _)
  have hq : ‖3 * |x|‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq_nonneg]
    linarith
  have hgeom : Summable (fun n : ℕ => (3 * |x|) ^ n) :=
    summable_geometric_of_norm_lt_one hq
  have hgeom_shift :
      Summable (fun k : ℕ => (3 * |x|) ^ (k + 2)) :=
    hgeom.comp_injective (i := fun k : ℕ => k + 2)
      (fun _ _ h => Nat.add_right_cancel h)
  have hmajor :
      Summable
        (fun k : ℕ => (1 / Real.log 2) * (3 * |x|) ^ (k + 2)) :=
    hgeom_shift.mul_left _
  change Summable (fun k : ℕ => powerTerm (k + 2) x)
  refine hmajor.of_norm_bounded ?_
  intro k
  have hn : 2 ≤ k + 2 := by omega
  have hlog : 0 < Real.log (k + 2 : ℕ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < k + 2 by omega)
  have hlog_le : Real.log 2 ≤ Real.log (k + 2 : ℕ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hbase := oscillatingBase_abs_le_three (k + 2)
  rw [Real.norm_eq_abs]
  unfold powerTerm coefficient
  rw [abs_mul, abs_div, abs_pow,
    show |Real.log (k + 2 : ℕ)| = Real.log (k + 2 : ℕ) from
      abs_of_pos hlog,
    abs_pow]
  calc
    |oscillatingBase (k + 2)| ^ (k + 2) /
          Real.log (k + 2 : ℕ) * |x| ^ (k + 2) ≤
        (3 ^ (k + 2) / Real.log 2) * |x| ^ (k + 2) := by
      gcongr
    _ = (1 / Real.log 2) * (3 * |x|) ^ (k + 2) := by
      rw [mul_pow]
      ring

private theorem series_not_summable_outside
    (x : ℝ) (hx : 1 / 3 < |x|) :
    ¬ SeriesConvergesAt x := by
  intro hsum
  change Summable (fun k : ℕ => powerTerm (k + 2) x) at hsum
  have hsub :
      Summable (fun k : ℕ => |powerTerm (8 * (k + 1)) x|) := by
    have hnorm := hsum.norm
    have hi : Function.Injective (fun k : ℕ => 8 * k + 6) := by
      intro a b h
      apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 8)
      exact Nat.add_right_cancel h
    have hcomp := hnorm.comp_injective hi
    simpa only [Function.comp_apply, Real.norm_eq_abs] using hcomp
  have hterms_zero :
      Tendsto (fun k : ℕ => |powerTerm (8 * (k + 1)) x|)
        atTop (𝓝 0) :=
    hsub.tendsto_atTop_zero
  let q : ℝ := 3 * |x|
  let r : ℝ := q ^ 8
  have hq : 1 < q := by
    dsimp [q]
    linarith
  have hr : 1 < r := by
    dsimp [r]
    exact one_lt_pow₀ hq (by norm_num)
  have hzero :
      Tendsto
        (fun k : ℕ =>
          ((k + 1 : ℕ) : ℝ) ^ 1 / r ^ (k + 1))
        atTop (𝓝 0) := by
    simpa only [Function.comp_apply] using
      (tendsto_pow_const_div_const_pow_of_one_lt 1 hr).comp
        (tendsto_add_atTop_nat 1)
  have hzero_gt :
      Tendsto
        (fun k : ℕ =>
          ((k + 1 : ℕ) : ℝ) ^ 1 / r ^ (k + 1))
        atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hzero, Eventually.of_forall (fun k => by
      simp only [Set.mem_Ioi]
      positivity)⟩
  have hratio :
      Tendsto
        (fun k : ℕ => r ^ (k + 1) / ((k + 1 : ℕ) : ℝ))
        atTop atTop := by
    apply hzero_gt.inv_tendsto_nhdsGT_zero.congr'
    exact Eventually.of_forall (fun k => by
      simp only [Pi.inv_apply, inv_div, pow_one])
  have hlarge :
      ∀ᶠ k : ℕ in atTop,
        8 ≤ r ^ (k + 1) / ((k + 1 : ℕ) : ℝ) :=
    hratio.eventually (eventually_ge_atTop 8)
  have hsmall :
      ∀ᶠ k : ℕ in atTop, |powerTerm (8 * (k + 1)) x| < 1 :=
    hterms_zero.eventually (Iio_mem_nhds (by norm_num))
  obtain ⟨k, hklarge, hksmall⟩ := (hlarge.and hsmall).exists
  have hkpos : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
  have hnum :
      8 * ((k + 1 : ℕ) : ℝ) ≤ r ^ (k + 1) :=
    (le_div_iff₀ hkpos).mp hklarge
  have hNpos : 0 < ((8 * (k + 1) : ℕ) : ℝ) := by positivity
  have hlogpos : 0 < Real.log (8 * (k + 1) : ℕ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < 8 * (k + 1) by omega)
  have hlog_num :
      Real.log (8 * (k + 1) : ℕ) ≤ r ^ (k + 1) := by
    calc
      Real.log (8 * (k + 1) : ℕ) ≤
          ((8 * (k + 1) : ℕ) : ℝ) :=
        Real.log_le_self hNpos.le
      _ = 8 * ((k + 1 : ℕ) : ℝ) := by
        push_cast
        rfl
      _ ≤ r ^ (k + 1) := hnum
  have hpow :
      (3 * |x|) ^ (8 * (k + 1)) = r ^ (k + 1) := by
    change q ^ (8 * (k + 1)) = r ^ (k + 1)
    dsimp [r]
    rw [pow_mul]
  have hlogpos' :
      0 < Real.log (8 * ((k + 1 : ℕ) : ℝ)) := by
    simpa [Nat.cast_mul] using hlogpos
  have hlog_num' :
      Real.log (8 * ((k + 1 : ℕ) : ℝ)) ≤ r ^ (k + 1) := by
    simpa [Nat.cast_mul] using hlog_num
  have hone : 1 ≤ |powerTerm (8 * (k + 1)) x| := by
    rw [abs_peak_term (k + 1) (by omega), hpow]
    apply (le_div_iff₀ hlogpos').mpr
    rw [one_mul]
    exact hlog_num'
  exact (not_lt_of_ge hone) hksmall

theorem gap1 :
    Tendsto
        (fun k : ℕ =>
          Real.rpow |coefficient (8 * (k + 1))|
            (1 / ((8 * (k + 1) : ℕ) : ℝ)))
        atTop (𝓝 3) ∧
      (∀ n : ℕ, 2 ≤ n →
        Real.rpow |coefficient n| (1 / (n : ℝ)) ≤
          3 / Real.rpow (Real.log n) (1 / (n : ℝ))) := by
  constructor
  · have hindex :
        Tendsto (fun k : ℕ => 8 * (k + 1)) atTop atTop := by
      refine tendsto_atTop.2 ?_
      intro b
      filter_upwards [eventually_ge_atTop b] with k hk
      omega
    have hden :
        Tendsto
          (fun k : ℕ =>
            Real.rpow
              (Real.log (((8 * (k + 1) : ℕ) : ℝ)))
              (1 / ((8 * (k + 1) : ℕ) : ℝ)))
          atTop (𝓝 1) :=
      by
        simpa only [Function.comp_apply] using
          tendsto_log_rpow_inv_natCast.comp hindex
    have hquot :
        Tendsto
          (fun k : ℕ =>
            3 / Real.rpow
              (Real.log (((8 * (k + 1) : ℕ) : ℝ)))
              (1 / ((8 * (k + 1) : ℕ) : ℝ)))
          atTop (𝓝 3) := by
      convert tendsto_const_nhds.div hden (by norm_num : (1 : ℝ) ≠ 0)
      norm_num
    apply hquot.congr'
    exact Eventually.of_forall (fun k => by
      change
        3 / Real.rpow
            (Real.log (((8 * (k + 1) : ℕ) : ℝ)))
            (1 / ((8 * (k + 1) : ℕ) : ℝ)) =
          Real.rpow |coefficient (8 * (k + 1))|
            (1 / ((8 * (k + 1) : ℕ) : ℝ))
      symm
      rw [coefficient_root_formula (8 * (k + 1)) (by omega)]
      rw [oscillatingBase_eight_mul]
      norm_num)
  · intro n hn
    rw [coefficient_root_formula n hn]
    have hlog : 0 < Real.log (n : ℝ) := by
      apply Real.log_pos
      exact_mod_cast (show 1 < n by omega)
    have hden :
        0 < Real.rpow (Real.log n) (1 / (n : ℝ)) :=
      Real.rpow_pos_of_pos hlog _
    exact div_le_div_of_nonneg_right
      (oscillatingBase_abs_le_three n) hden.le

theorem gap2 :
    HasConvergenceRadiusThird := by
  constructor
  · intro x hx
    exact series_summable_inside x hx
  · intro x hx
    exact series_not_summable_outside x hx

theorem gap3 :
    ∀ x : ℝ, |x| < 1 / 3 → SeriesConvergesAt x := by
  intro x hx
  exact series_summable_inside x hx

theorem gap4 :
    ∀ k : ℕ, 1 ≤ k →
      |powerTerm (8 * k) (1 / 3)| = 1 / Real.log (8 * k) := by
  intro k hk
  have hn : 0 < (8 * k : ℕ) := by omega
  have hn1 : 1 < (8 * k : ℕ) := by omega
  have hlog : 0 < Real.log (8 * k) :=
    Real.log_pos (by exact_mod_cast hn1)
  unfold powerTerm coefficient
  push_cast
  rw [oscillatingBase_eight_mul]
  rw [abs_mul, abs_div, abs_pow, abs_of_pos hlog]
  have hthree : |(3 : ℝ)| = 3 := by norm_num
  have hone_third : |(1 / 3 : ℝ)| = 1 / 3 := by norm_num
  rw [hthree, abs_pow, hone_third]
  field_simp
  rw [← mul_pow]
  norm_num

theorem gap5 :
    ∀ k : ℕ, 1 ≤ k →
      1 / Real.log (8 * k) > 1 / ((k : ℝ) + Real.log 8) := by
  intro k hk
  have hkpos_nat : 0 < k := by omega
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast hkpos_nat
  have h8 : (8 : ℝ) ≠ 0 := by norm_num
  have hk0 : (k : ℝ) ≠ 0 := ne_of_gt hkpos
  have hlog_product :
      Real.log (8 * k) = Real.log 8 + Real.log k := by
    exact Real.log_mul h8 hk0
  have hlogk : Real.log (k : ℝ) < k := by
    exact (Real.log_le_sub_one_of_pos hkpos).trans_lt (by linarith)
  have hden_lt :
      Real.log (8 * k) < (k : ℝ) + Real.log 8 := by
    rw [hlog_product]
    linarith
  have hlog_pos : 0 < Real.log (8 * k) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < 8 * k by omega)
  exact one_div_lt_one_div_of_lt hlog_pos hden_lt

theorem gap6 :
    ∀ k : ℕ, 1 ≤ k →
      1 / ((k : ℝ) + Real.log 8) > 0 := by
  intro k hk
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hlog8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  positivity

theorem gap7 :
    ∀ k : ℕ, 1 ≤ k → 1 / Real.log (8 * k) > 0 := by
  intro k hk
  have hlog : 0 < Real.log (8 * k) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < 8 * k by omega)
  positivity

theorem gap8 :
    ¬ Summable (fun k : ℕ => 1 / Real.log (8 * (k + 1))) := by
  have hlog8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have hnot :
      ¬ Summable (fun k : ℕ => 1 / ((k : ℝ) + 1 + Real.log 8)) := by
    intro hsum
    have hshift :
        Summable
          (fun k : ℕ =>
            1 / |(k : ℝ) + (1 + Real.log 8)| ^ (1 : ℝ)) := by
      apply hsum.congr
      intro k
      have hpos : 0 < (k : ℝ) + (1 + Real.log 8) := by positivity
      rw [abs_of_pos hpos, Real.rpow_one]
      congr 1
      ring
    have hfalse :=
      (Real.summable_one_div_nat_add_rpow (1 + Real.log 8) 1).mp hshift
    norm_num at hfalse
  intro hsum
  apply hnot
  exact hsum.of_nonneg_of_le
    (fun k => by
      have : 0 < (k : ℝ) + 1 + Real.log 8 := by positivity
      positivity)
    (fun k => by
      simpa [Nat.cast_add, Nat.cast_one, add_assoc] using
        (gap5 (k + 1) (by omega)).le)

theorem gap9 :
    ∀ n : ℕ, 3 ≤ n → n % 8 ≠ 0 →
      |powerTerm n (1 / 3)| ≤
        ((1 + Real.sqrt 2) / 3) ^ n := by
  intro n hn hmod
  have hlog3 : 1 < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).2 Real.exp_one_lt_three
  have hlog_le : Real.log 3 ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hlog : 1 < Real.log (n : ℝ) := hlog3.trans_le hlog_le
  have hbase := nonpeak_base_bound n hmod
  unfold powerTerm coefficient
  rw [abs_mul, abs_div, abs_pow, abs_pow,
    show |Real.log (n : ℝ)| = Real.log (n : ℝ) from
      abs_of_pos (lt_trans zero_lt_one hlog)]
  calc
    |oscillatingBase n| ^ n / Real.log (n : ℝ) * |1 / 3| ^ n ≤
        |oscillatingBase n| ^ n * |1 / 3| ^ n := by
      gcongr
      exact div_le_self (pow_nonneg (abs_nonneg _) _) hlog.le
    _ = (|oscillatingBase n| / 3) ^ n := by
      rw [← mul_pow]
      congr 1
      ring
    _ ≤ ((1 + Real.sqrt 2) / 3) ^ n := by
      gcongr

theorem gap10 :
    Summable (fun n : ℕ => ((1 + Real.sqrt 2) / 3) ^ (n + 2)) := by
  have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hs2 : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hq_nonneg : 0 ≤ (1 + Real.sqrt 2) / 3 := by positivity
  have hq : ‖(1 + Real.sqrt 2) / 3‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq_nonneg]
    linarith
  have hsum :
      Summable (fun n : ℕ => ((1 + Real.sqrt 2) / 3) ^ n) :=
    summable_geometric_of_norm_lt_one hq
  simpa [Function.comp_apply] using
    hsum.comp_injective (i := fun n : ℕ => n + 2)
      (fun _ _ h => Nat.add_right_cancel h)

theorem gap11 :
    (1 + Real.sqrt 2) / (2 - Real.sqrt 2) < 5 := by
  have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hs2eq : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hs2 : Real.sqrt 2 < 2 := by nlinarith
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

theorem gap12 :
    Summable (fun k : ℕ => |nonPeakTerm (k + 2) (1 / 3)|) := by
  refine (summable_nat_add_iff 1).mp ?_
  have hgeom :
      Summable
        (fun n : ℕ => ((1 + Real.sqrt 2) / 3) ^ ((n + 1) + 2)) :=
    (summable_nat_add_iff 1).mpr gap10
  refine hgeom.of_nonneg_of_le (fun n => abs_nonneg _) ?_
  intro n
  have hindex : (n + 1) + 2 = n + 3 := by omega
  rw [hindex]
  unfold nonPeakTerm
  split_ifs with hmod
  · simp
    positivity
  · simpa only [hindex] using gap9 (n + 3) (by omega) hmod

theorem gap13 :
    ∀ x : ℝ, |x| = 1 / 3 →
      Summable (fun k : ℕ => |nonPeakTerm (k + 2) x|) := by
  intro x hx
  apply gap12.congr
  intro k
  unfold nonPeakTerm
  split_ifs
  · rfl
  · exact abs_powerTerm_eq_of_abs_eq _
      ((by norm_num : |(1 / 3 : ℝ)| = 1 / 3).trans hx.symm)

theorem gap14 :
    ∀ x : ℝ, |x| = 1 / 3 → ¬ SeriesConvergesAt x := by
  intro x hx hsum
  change Summable (fun k : ℕ => powerTerm (k + 2) x) at hsum
  have hsub :
      Summable (fun k : ℕ => |powerTerm (8 * (k + 1)) x|) := by
    have hnorm := hsum.norm
    have hi : Function.Injective (fun k : ℕ => 8 * k + 6) := by
      intro a b h
      apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 8)
      exact Nat.add_right_cancel h
    have hcomp := hnorm.comp_injective hi
    simpa only [SeriesConvergesAt, Function.comp_apply, Real.norm_eq_abs] using
      hcomp
  apply gap8
  apply hsub.congr
  intro k
  calc
    |powerTerm (8 * (k + 1)) x| =
        |powerTerm (8 * (k + 1)) (1 / 3)| :=
      abs_powerTerm_eq_of_abs_eq _ (hx.trans (by norm_num))
    _ = 1 / Real.log (8 * (k + 1)) :=
      by
        simpa [Nat.cast_add, Nat.cast_one] using
          gap4 (k + 1) (by omega)

theorem gap15 :
    ∀ x : ℝ, x ∈ Set.Ioo (-1 / 3 : ℝ) (1 / 3) ↔
      SeriesConvergesAt x := by
  intro x
  constructor
  · intro hx
    apply series_summable_inside
    rw [Set.mem_Ioo] at hx
    rw [abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  · intro hsum
    have hle : |x| ≤ 1 / 3 := by
      exact le_of_not_gt (fun hgt => series_not_summable_outside x hgt hsum)
    have hne : |x| ≠ 1 / 3 :=
      fun heq => gap14 x heq hsum
    have hlt : |x| < 1 / 3 := lt_of_le_of_ne hle hne
    rw [abs_lt] at hlt
    rw [Set.mem_Ioo]
    constructor <;> linarith [hlt.1, hlt.2]

end

end ProofGap.Exercise2829

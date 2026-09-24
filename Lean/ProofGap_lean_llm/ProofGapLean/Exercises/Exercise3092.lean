import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace ProofGap.Exercise3092

noncomputable section

open Filter
open scoped BigOperators Topology

def p (n : ℕ) : ℝ :=
  Real.sqrt n / (Real.sqrt n + (-1 : ℝ) ^ n)

def rewrittenP (n : ℕ) : ℝ :=
  1 - (-1 : ℝ) ^ n / (Real.sqrt n + (-1 : ℝ) ^ n)

def u (k : ℕ) : ℝ :=
  Real.log (p (2 * k)) + Real.log (p (2 * k + 1))

def combinedArgument (k : ℕ) : ℝ :=
  1 - (Real.sqrt (2 * k + 1) - Real.sqrt (2 * k) - 1) /
    ((Real.sqrt (2 * k) + 1) * (Real.sqrt (2 * k + 1) - 1))

def comparison (k : ℕ) : ℝ :=
  1 / (2 * (k : ℝ))

def SummableFromOne (f : ℕ → ℝ) : Prop :=
  Summable (fun k : ℕ => f (k + 1))

def SummableFromTwo (f : ℕ → ℝ) : Prop :=
  Summable (fun k : ℕ => f (k + 2))

def partialProduct (N : ℕ) : ℝ :=
  ∏ n ∈ Finset.Icc 2 N, p n

private theorem sqrt_nat_gt_one {n : ℕ} (hn : 2 ≤ n) :
    1 < Real.sqrt n := by
  rw [← Real.sqrt_one]
  apply Real.sqrt_lt_sqrt (by norm_num)
  exact_mod_cast (show 1 < n by omega)

private theorem p_den_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < Real.sqrt n + (-1 : ℝ) ^ n := by
  have hs : (-1 : ℝ) ≤ (-1 : ℝ) ^ n := by
    have habs : |(-1 : ℝ) ^ n| = 1 := abs_neg_one_pow n
    linarith [neg_abs_le ((-1 : ℝ) ^ n)]
  linarith [sqrt_nat_gt_one hn]

private theorem gap1_proof :
    ∀ n : ℕ, 2 ≤ n → Real.log (p n) = Real.log (rewrittenP n) := by
  intro n hn
  congr 1
  unfold p rewrittenP
  field_simp [(p_den_pos hn).ne']
  ring

private theorem gap2_proof :
    ∀ k : ℕ, 1 ≤ k →
      u k =
        Real.log (1 - 1 / (Real.sqrt (2 * k) + 1)) +
        Real.log (1 + 1 / (Real.sqrt (2 * k + 1) - 1)) := by
  intro k hk
  unfold u
  rw [gap1_proof (2 * k) (by omega), gap1_proof (2 * k + 1) (by omega)]
  unfold rewrittenP
  rw [Even.neg_one_pow (n := 2 * k) ⟨k, by omega⟩,
    Odd.neg_one_pow (n := 2 * k + 1) ⟨k, by omega⟩]
  push_cast
  congr 2 <;> ring

private theorem even_root_pos (k : ℕ) (hk : 1 ≤ k) :
    0 < Real.sqrt (2 * k) := by
  apply Real.sqrt_pos.2
  exact_mod_cast (show 0 < 2 * k by omega)

private theorem odd_root_gt_one (k : ℕ) (hk : 1 ≤ k) :
    1 < Real.sqrt (2 * k + 1) := by
  rw [← Real.sqrt_one]
  apply Real.sqrt_lt_sqrt (by norm_num)
  push_cast
  norm_num
  positivity

private theorem even_log_arg_pos (k : ℕ) (hk : 1 ≤ k) :
    0 < 1 - 1 / (Real.sqrt (2 * k) + 1) := by
  have ha := even_root_pos k hk
  have hden : 1 < Real.sqrt (2 * k) + 1 := by linarith
  have hrecip : 1 / (Real.sqrt (2 * k) + 1) < 1 := by
    simpa using one_div_lt_one_div_of_lt zero_lt_one hden
  linarith

private theorem odd_log_arg_pos (k : ℕ) (hk : 1 ≤ k) :
    0 < 1 + 1 / (Real.sqrt (2 * k + 1) - 1) := by
  have hb := odd_root_gt_one k hk
  have hrecip : 0 < 1 / (Real.sqrt (2 * k + 1) - 1) :=
    one_div_pos.mpr (sub_pos.mpr hb)
  linarith

private theorem gap3_proof :
    ∀ k : ℕ, 1 ≤ k → u k = Real.log (combinedArgument k) := by
  intro k hk
  rw [gap2_proof k hk]
  rw [← Real.log_mul (even_log_arg_pos k hk).ne'
    (odd_log_arg_pos k hk).ne']
  congr 1
  have ha := even_root_pos k hk
  have hb := odd_root_gt_one k hk
  have hda : Real.sqrt (2 * k) + 1 ≠ 0 := by positivity
  have hdb : Real.sqrt (2 * k + 1) - 1 ≠ 0 := by linarith
  unfold combinedArgument
  push_cast
  field_simp [hda, hdb]
  ring

private theorem root_gap_lt_one (k : ℕ) (hk : 1 ≤ k) :
    Real.sqrt (2 * k + 1) - Real.sqrt (2 * k) < 1 := by
  have ha := even_root_pos k hk
  have hb := odd_root_gt_one k hk
  have ha_sq : Real.sqrt (2 * (k : ℝ)) ^ 2 = 2 * (k : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hb_sq : Real.sqrt (2 * (k : ℝ) + 1) ^ 2 = 2 * (k : ℝ) + 1 :=
    Real.sq_sqrt (by positivity)
  have hid :
      (Real.sqrt (2 * (k : ℝ) + 1) - Real.sqrt (2 * (k : ℝ))) *
        (Real.sqrt (2 * (k : ℝ) + 1) + Real.sqrt (2 * (k : ℝ))) = 1 := by
    nlinarith
  by_contra h
  have hdiff : 1 ≤ Real.sqrt (2 * (k : ℝ) + 1) -
      Real.sqrt (2 * (k : ℝ)) := le_of_not_gt h
  have hsumpos : 0 ≤ Real.sqrt (2 * (k : ℝ) + 1) +
      Real.sqrt (2 * (k : ℝ)) := by positivity
  have hle :
      Real.sqrt (2 * (k : ℝ) + 1) + Real.sqrt (2 * (k : ℝ)) ≤
        (Real.sqrt (2 * (k : ℝ) + 1) - Real.sqrt (2 * (k : ℝ))) *
          (Real.sqrt (2 * (k : ℝ) + 1) + Real.sqrt (2 * (k : ℝ))) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hdiff hsumpos
  nlinarith

private theorem combinedArgument_gt_one (k : ℕ) (hk : 1 ≤ k) :
    1 < combinedArgument k := by
  have ha := even_root_pos k hk
  have hb := odd_root_gt_one k hk
  have hnum : Real.sqrt (2 * k + 1) - Real.sqrt (2 * k) - 1 < 0 := by
    linarith [root_gap_lt_one k hk]
  have hden :
      0 < (Real.sqrt (2 * k) + 1) *
        (Real.sqrt (2 * k + 1) - 1) :=
    mul_pos (by linarith) (sub_pos.mpr hb)
  unfold combinedArgument
  have hfrac :
      (Real.sqrt (2 * k + 1) - Real.sqrt (2 * k) - 1) /
        ((Real.sqrt (2 * k) + 1) *
          (Real.sqrt (2 * k + 1) - 1)) < 0 := div_neg_of_neg_of_pos hnum hden
  linarith

private theorem gap4_proof :
    ∀ k : ℕ, 1 ≤ k → 0 < Real.log (combinedArgument k) := by
  intro k hk
  exact Real.log_pos (combinedArgument_gt_one k hk)

private theorem gap5_proof :
    ∀ k : ℕ, 1 ≤ k → 0 < u k := by
  intro k hk
  rw [gap3_proof k hk]
  exact gap4_proof k hk

private def aRoot (k : ℕ) : ℝ := Real.sqrt (2 * (k : ℝ))
private def bRoot (k : ℕ) : ℝ := Real.sqrt (2 * (k : ℝ) + 1)
private def delta (k : ℕ) : ℝ := combinedArgument k - 1

private theorem aRoot_sq (k : ℕ) : aRoot k ^ 2 = 2 * (k : ℝ) := by
  unfold aRoot
  exact Real.sq_sqrt (by positivity)

private theorem bRoot_sq (k : ℕ) : bRoot k ^ 2 = 2 * (k : ℝ) + 1 := by
  unfold bRoot
  exact Real.sq_sqrt (by positivity)

private theorem aRoot_tendsto_atTop : Tendsto aRoot atTop atTop := by
  have harg : Tendsto (fun k : ℕ => 2 * (k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  exact Real.tendsto_sqrt_atTop.comp harg

private theorem bRoot_tendsto_atTop : Tendsto bRoot atTop atTop := by
  have harg0 : Tendsto (fun k : ℕ => 2 * (k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have harg : Tendsto (fun k : ℕ => 2 * (k : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 harg0
  exact Real.tendsto_sqrt_atTop.comp harg

private theorem root_diff_tendsto_zero :
    Tendsto (fun k : ℕ => bRoot k - aRoot k) atTop (𝓝 0) := by
  have hsum : Tendsto (fun k : ℕ => bRoot k + aRoot k) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ aRoot_tendsto_atTop
    filter_upwards with k
    exact le_add_of_nonneg_left (Real.sqrt_nonneg _)
  have hinv : Tendsto (fun k : ℕ => 1 / (bRoot k + aRoot k))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hsum
  apply hinv.congr'
  filter_upwards with k
  have hb : 0 < bRoot k := by
    unfold bRoot
    positivity
  have ha0 : 0 ≤ aRoot k := by
    unfold aRoot
    exact Real.sqrt_nonneg _
  have hden : bRoot k + aRoot k ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg hb ha0)
  field_simp [hden]
  nlinarith [aRoot_sq k, bRoot_sq k]

private theorem numerator_tendsto_one :
    Tendsto (fun k : ℕ => aRoot k + 1 - bRoot k) atTop (𝓝 1) := by
  have h : Tendsto (fun k : ℕ => (1 : ℝ) - (bRoot k - aRoot k))
      atTop (𝓝 ((1 : ℝ) - 0)) :=
    tendsto_const_nhds.sub root_diff_tendsto_zero
  refine (tendsto_congr' ?_).2 (by simpa using h)
  exact Eventually.of_forall fun k => by ring

private theorem first_den_factor_tendsto_one :
    Tendsto (fun k : ℕ => aRoot k / (aRoot k + 1)) atTop (𝓝 1) := by
  have hden : Tendsto (fun k : ℕ => aRoot k + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 aRoot_tendsto_atTop
  have hzero : Tendsto (fun k : ℕ => 1 / (aRoot k + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have h : Tendsto (fun k : ℕ => (1 : ℝ) - 1 / (aRoot k + 1))
      atTop (𝓝 ((1 : ℝ) - 0)) := tendsto_const_nhds.sub hzero
  refine (tendsto_congr' ?_).2 (by simpa using h)
  exact Eventually.of_forall fun k => by
    have hne : aRoot k + 1 ≠ 0 := by
      have : 0 ≤ aRoot k := Real.sqrt_nonneg _
      linarith
    field_simp [hne]
    ring

private theorem inv_aRoot_tendsto_zero :
    Tendsto (fun k : ℕ => 1 / aRoot k) atTop (𝓝 0) := by
  simpa only [one_div] using aRoot_tendsto_atTop.inv_tendsto_atTop

private theorem second_den_factor_tendsto_one :
    Tendsto (fun k : ℕ => aRoot k / (bRoot k - 1)) atTop (𝓝 1) := by
  have hsmall : Tendsto
      (fun k : ℕ => (bRoot k - aRoot k) * (1 / aRoot k))
      atTop (𝓝 0) := by
    simpa using root_diff_tendsto_zero.mul inv_aRoot_tendsto_zero
  have hratio : Tendsto (fun k : ℕ => (bRoot k - 1) / aRoot k)
      atTop (𝓝 1) := by
    have h : Tendsto
        (fun k : ℕ => (1 : ℝ) +
          (bRoot k - aRoot k) * (1 / aRoot k) - 1 / aRoot k)
        atTop (𝓝 (((1 : ℝ) + 0) - 0)) :=
      (tendsto_const_nhds.add hsmall).sub inv_aRoot_tendsto_zero
    refine (tendsto_congr' ?_).2 (by simpa using h)
    filter_upwards [eventually_ge_atTop 1] with k hk
    have ha : 0 < aRoot k := by
      unfold aRoot
      positivity
    field_simp [ha.ne']
    ring
  have hinv := hratio.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  refine (tendsto_congr' ?_).2 (by simpa using hinv)
  filter_upwards [eventually_ge_atTop 1] with k hk
  have ha : 0 < aRoot k := by
    unfold aRoot
    positivity
  have hb : 1 < bRoot k := by
    simpa [bRoot] using odd_root_gt_one k hk
  field_simp [ha.ne', (sub_pos.mpr hb).ne']

private theorem delta_formula (k : ℕ) :
    delta k =
      (aRoot k + 1 - bRoot k) /
        ((aRoot k + 1) * (bRoot k - 1)) := by
  unfold delta combinedArgument aRoot bRoot
  push_cast
  ring

private theorem delta_div_comparison_tendsto_one :
    Tendsto (fun k : ℕ => delta k / comparison k) atTop (𝓝 1) := by
  have h := (numerator_tendsto_one.mul first_den_factor_tendsto_one).mul
    second_den_factor_tendsto_one
  refine (tendsto_congr' ?_).2 (by simpa using h)
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have ha : 0 < aRoot k := by
    unfold aRoot
    positivity
  have hb : 1 < bRoot k := by
    simpa [bRoot] using odd_root_gt_one k hk
  have hda : aRoot k + 1 ≠ 0 := by positivity
  have hdb : bRoot k - 1 ≠ 0 := (sub_pos.mpr hb).ne'
  rw [delta_formula]
  unfold comparison
  field_simp [hk0, hda, hdb]
  nlinarith [aRoot_sq k]

private theorem comparison_tendsto_zero :
    Tendsto comparison atTop (𝓝 0) := by
  have hden : Tendsto (fun k : ℕ => 2 * (k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  simpa [comparison] using tendsto_const_nhds.div_atTop hden

private theorem delta_tendsto_zero : Tendsto delta atTop (𝓝 0) := by
  have h := delta_div_comparison_tendsto_one.mul comparison_tendsto_zero
  refine (tendsto_congr' ?_).2 (by simpa using h)
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hc : comparison k ≠ 0 := by
    unfold comparison
    positivity
  field_simp [hc]

private theorem isEquivalent_log_one_plus_nhds :
    Asymptotics.IsEquivalent (𝓝 0)
      (fun x : ℝ => Real.log (1 + x)) (fun x : ℝ => x) := by
  have hinner : HasDerivAt (fun x : ℝ => 1 + x) 1 0 := by
    simpa using
      (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).add (hasDerivAt_id 0)
  have hout : HasDerivAt Real.log 1 ((fun x : ℝ => 1 + x) 0) := by
    simpa using Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)
  have hderiv : HasDerivAt (fun x : ℝ => Real.log (1 + x)) 1 0 := by
    simpa using hout.comp 0 hinner
  change (fun x : ℝ => Real.log (1 + x) - x) =o[𝓝 0] (fun x : ℝ => x)
  simpa using hderiv.isLittleO

private theorem gap6_proof :
    Asymptotics.IsEquivalent atTop u comparison := by
  have hdelta : Asymptotics.IsEquivalent atTop delta comparison :=
    Asymptotics.isEquivalent_of_tendsto_one delta_div_comparison_tendsto_one
  have hlog : Asymptotics.IsEquivalent atTop
      (fun k : ℕ => Real.log (1 + delta k)) delta :=
    isEquivalent_log_one_plus_nhds.comp_tendsto delta_tendsto_zero
  have heq : u =ᶠ[atTop] (fun k : ℕ => Real.log (1 + delta k)) := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    rw [gap3_proof k hk]
    unfold delta
    congr 1
    ring
  exact heq.isEquivalent.trans (hlog.trans hdelta)

private theorem comparison_not_summable : ¬Summable comparison := by
  intro hs
  have hscaled : Summable (fun n : ℕ => (2 : ℝ) * comparison n) :=
    hs.mul_left 2
  apply Real.not_summable_one_div_natCast
  apply hscaled.congr
  intro n
  unfold comparison
  by_cases hn : n = 0
  · simp [hn]
  · have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp [hnR]

private theorem gap7_proof : ¬SummableFromOne u := by
  intro hu
  unfold SummableFromOne at hu
  have huAll : Summable u := (summable_nat_add_iff 1).1 hu
  have hc : Summable comparison :=
    (Asymptotics.IsEquivalent.summable_iff_nat gap6_proof).1 huAll
  exact comparison_not_summable hc

private theorem gap8_proof :
    ¬SummableFromTwo (fun n => Real.log (p n)) := by
  intro hp
  unfold SummableFromTwo at hp
  have hpAll : Summable (fun n : ℕ => Real.log (p n)) :=
    (summable_nat_add_iff 2).1 hp
  have heven : Summable (fun k : ℕ => Real.log (p (2 * k))) := by
    have hinj : Function.Injective (fun k : ℕ => 2 * k) := by
      intro a b hab
      exact mul_left_cancel₀ (by norm_num : (2 : ℕ) ≠ 0) hab
    exact hpAll.comp_injective hinj
  have hodd : Summable (fun k : ℕ => Real.log (p (2 * k + 1))) := by
    have hinj : Function.Injective (fun k : ℕ => 2 * k + 1) := by
      intro a b hab
      have hmul : 2 * a = 2 * b := Nat.add_right_cancel hab
      exact mul_left_cancel₀ (by norm_num : (2 : ℕ) ≠ 0) hmul
    exact hpAll.comp_injective hinj
  have huAll : Summable u := by
    simpa only [u] using heven.add hodd
  apply gap7_proof
  unfold SummableFromOne
  exact (summable_nat_add_iff 1).2 huAll

private theorem p_pos {n : ℕ} (hn : 2 ≤ n) : 0 < p n := by
  unfold p
  exact div_pos (Real.sqrt_pos.2 (by exact_mod_cast (show 0 < n by omega)))
    (p_den_pos hn)

private theorem pair_eq_exp_u (k : ℕ) (hk : 1 ≤ k) :
    p (2 * k) * p (2 * k + 1) = Real.exp (u k) := by
  unfold u
  rw [Real.exp_add, Real.exp_log (p_pos (by omega)),
    Real.exp_log (p_pos (by omega))]

private theorem partialProduct_succ (N : ℕ) (hN : 1 ≤ N) :
    partialProduct (N + 1) = partialProduct N * p (N + 1) := by
  unfold partialProduct
  rw [Finset.prod_Icc_succ_top (by omega)]

private theorem partialProduct_odd_formula (m : ℕ) :
    partialProduct (2 * m + 1) =
      Real.exp (∑ k ∈ Finset.range m, u (k + 1)) := by
  induction m with
  | zero =>
      simp [partialProduct]
  | succ m ih =>
      calc
        partialProduct (2 * (m + 1) + 1) =
            partialProduct (2 * m + 2) * p (2 * m + 3) := by
          convert partialProduct_succ (2 * m + 2) (by omega) using 1 <;> omega
        _ = (partialProduct (2 * m + 1) * p (2 * m + 2)) *
              p (2 * m + 3) := by
          rw [partialProduct_succ (2 * m + 1) (by omega)]
        _ = partialProduct (2 * m + 1) * Real.exp (u (m + 1)) := by
          rw [← pair_eq_exp_u (m + 1) (by omega)]
          ring
        _ = Real.exp (∑ k ∈ Finset.range (m + 1), u (k + 1)) := by
          rw [ih, Finset.sum_range_succ, Real.exp_add]

private theorem paired_sum_tendsto_atTop :
    Tendsto (fun m : ℕ => ∑ k ∈ Finset.range m, u (k + 1))
      atTop atTop := by
  have hnonneg : ∀ k : ℕ, 0 ≤ u (k + 1) := by
    intro k
    exact (gap5_proof (k + 1) (by omega)).le
  have hnsum : ¬Summable (fun k : ℕ => u (k + 1)) := by
    simpa only [SummableFromOne] using gap7_proof
  exact (not_summable_iff_tendsto_nat_atTop_of_nonneg hnonneg).mp hnsum

private theorem partialProduct_odd_tendsto_atTop :
    Tendsto (fun m : ℕ => partialProduct (2 * m + 1)) atTop atTop := by
  have h := Real.tendsto_exp_atTop.comp paired_sum_tendsto_atTop
  apply h.congr'
  exact Eventually.of_forall fun m => (partialProduct_odd_formula m).symm

private theorem p_even_shift_tendsto_one :
    Tendsto (fun m : ℕ => p (2 * m + 2)) atTop (𝓝 1) := by
  have h := first_den_factor_tendsto_one.comp (tendsto_add_atTop_nat 1)
  apply h.congr'
  exact Eventually.of_forall fun m => by
    simp only [Function.comp_apply]
    unfold p aRoot
    rw [Even.neg_one_pow (n := 2 * m + 2) ⟨m + 1, by omega⟩]
    push_cast
    congr 2 <;> ring

private theorem partialProduct_even_shift_tendsto_atTop :
    Tendsto (fun m : ℕ => partialProduct (2 * m + 2)) atTop atTop := by
  have h := partialProduct_odd_tendsto_atTop.atTop_mul_pos zero_lt_one
    p_even_shift_tendsto_one
  apply h.congr'
  exact Eventually.of_forall fun m => by
    simp only
    rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega,
      partialProduct_succ (2 * m + 1) (by omega)]

private theorem partialProduct_even_tendsto_atTop :
    Tendsto (fun m : ℕ => partialProduct (2 * m)) atTop atTop := by
  apply (tendsto_add_atTop_iff_nat 1).1
  simpa [Nat.mul_add] using partialProduct_even_shift_tendsto_atTop

private theorem gap9_proof : Tendsto partialProduct atTop atTop := by
  have heven := partialProduct_even_tendsto_atTop
  have hodd := partialProduct_odd_tendsto_atTop
  rw [tendsto_atTop] at heven hodd ⊢
  intro b
  obtain ⟨Ne, hNe⟩ := (eventually_atTop.1 (heven b))
  obtain ⟨No, hNo⟩ := (eventually_atTop.1 (hodd b))
  apply eventually_atTop.2
  refine ⟨2 * max Ne No + 1, ?_⟩
  intro n hn
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · exact hNe k (by omega)
  · exact hNo k (by omega)

/-- Source: `proof_gap/exercise_3092/1.txt`; exclude the zero denominator at `n = 1`. -/
theorem gap1 :
    ∀ n : ℕ, 2 ≤ n → Real.log (p n) = Real.log (rewrittenP n) := by
  exact gap1_proof

/-- Source: `proof_gap/exercise_3092/2.txt`; paired terms start at `k = 1`. -/
theorem gap2 :
    ∀ k : ℕ, 1 ≤ k →
      u k =
        Real.log (1 - 1 / (Real.sqrt (2 * k) + 1)) +
        Real.log (1 + 1 / (Real.sqrt (2 * k + 1) - 1)) := by
  exact gap2_proof

/-- Source: `proof_gap/exercise_3092/3.txt`; combine the positive logarithm arguments. -/
theorem gap3 :
    ∀ k : ℕ, 1 ≤ k → u k = Real.log (combinedArgument k) := by
  exact gap3_proof

/-- Source: `proof_gap/exercise_3092/4.txt`; retain the positive paired range. -/
theorem gap4 :
    ∀ k : ℕ, 1 ≤ k → 0 < Real.log (combinedArgument k) := by
  exact gap4_proof

/-- Source: `proof_gap/exercise_3092/5.txt`. -/
theorem gap5 :
    ∀ k : ℕ, 1 ≤ k → 0 < u k := by
  exact gap5_proof

/-- Source: `proof_gap/exercise_3092/6.txt`; bind the whole asymptotic functions. -/
theorem gap6 :
    Asymptotics.IsEquivalent atTop u comparison := by
  exact gap6_proof

/-- Source: `proof_gap/exercise_3092/7.txt`. -/
theorem gap7 : ¬SummableFromOne u := by
  exact gap7_proof

/-- Source: `proof_gap/exercise_3092/8.txt`. -/
theorem gap8 :
    ¬SummableFromTwo (fun n => Real.log (p n)) := by
  exact gap8_proof

/-- Source: `proof_gap/exercise_3092/9.txt`; `+∞` is the filter `atTop`. -/
theorem gap9 :
    Tendsto partialProduct atTop atTop := by
  exact gap9_proof

end

end ProofGap.Exercise3092

import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ProofGap.Exercise2739_2

noncomputable section

open Filter Asymptotics
open scoped BigOperators Topology

def fallingFactorial (x : ℝ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (x - k)

def risingShift (t : ℝ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, ((k + 1 : ℕ) + t)

def weightedTerm (p x : ℝ) (n : ℕ) : ℝ :=
  Real.rpow n (-p) * fallingFactorial x n / n.factorial

def alternatingModel (p t : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n - 1) * risingShift t n /
    ((n.factorial : ℝ) * Real.rpow n p)

def isNonnegativeInteger (x : ℝ) : Prop :=
  ∃ m : ℕ, x = m

def ConditionallySummable (p x : ℝ) : Prop :=
  ProofGap.SeriesConverges (fun n : ℕ => weightedTerm p x (n + 1)) ∧
    ¬ Summable (fun n : ℕ => |weightedTerm p x (n + 1)|)

private theorem fallingFactorial_eq_risingShift (n : ℕ) (x : ℝ) (hn : 1 ≤ n) :
    fallingFactorial x n =
      -(-1 : ℝ) ^ (n - 1) * risingShift (-(1 + x)) n := by
  have hsign : (-1 : ℝ) ^ n = -(-1 : ℝ) ^ (n - 1) := by
    calc
      (-1 : ℝ) ^ n = (-1 : ℝ) ^ ((n - 1) + 1) := by congr 1 <;> omega
      _ = -(-1 : ℝ) ^ (n - 1) := by rw [pow_succ]; ring
  unfold fallingFactorial risingShift
  calc
    (∏ k ∈ Finset.range n, (x - k)) =
        ∏ k ∈ Finset.range n, ((-1 : ℝ) * (((k + 1 : ℕ) : ℝ) + -(1 + x))) := by
      apply Finset.prod_congr rfl
      intro k hk
      push_cast
      ring
    _ = (-1 : ℝ) ^ n *
        ∏ k ∈ Finset.range n, (((k + 1 : ℕ) : ℝ) + -(1 + x)) := by
      rw [Finset.prod_mul_distrib]
      simp
    _ = -(-1 : ℝ) ^ (n - 1) *
        ∏ k ∈ Finset.range n, (((k + 1 : ℕ) : ℝ) + -(1 + x)) := by
      rw [hsign]

private theorem fallingFactorial_eq_reflected (n : ℕ) (x : ℝ) (hn : 1 ≤ n) :
    fallingFactorial x n =
      (-1 : ℝ) ^ (n - 1) *
        (x * (∏ k ∈ Finset.range (n - 1),
          (((n - 1 - k : ℕ) : ℝ) - x))) := by
  cases n with
  | zero => omega
  | succ m =>
      simp only [Nat.succ_sub_one]
      rw [fallingFactorial_eq_risingShift (m + 1) x (by omega)]
      have hrise : risingShift (-(1 + x)) (m + 1) =
          ∏ k ∈ Finset.range (m + 1), ((k : ℝ) - x) := by
        unfold risingShift
        apply Finset.prod_congr rfl
        intro k hk
        push_cast
        ring
      rw [hrise, Finset.prod_range_succ']
      simp only [Nat.cast_zero, zero_sub]
      have hreflect := Finset.prod_range_reflect
        (fun j : ℕ => (((j + 1 : ℕ) : ℝ) - x)) m
      have hreflect' :
          (∏ j ∈ Finset.range m, (((m - j : ℕ) : ℝ) - x)) =
            ∏ j ∈ Finset.range m, (((j + 1 : ℕ) : ℝ) - x) := by
        rw [← hreflect]
        apply Finset.prod_congr rfl
        intro j hj
        have hjlt : j < m := Finset.mem_range.mp hj
        have hnat : m - 1 - j + 1 = m - j := by omega
        rw [hnat]
      rw [← hreflect']
      have hexp : m + 1 - 1 = m := by omega
      rw [hexp]
      ring

private theorem weightedTerm_eq_neg_alternatingModel (p x : ℝ) (n : ℕ)
    (hn : 1 ≤ n) :
    weightedTerm p x n = -alternatingModel p (-(1 + x)) n := by
  unfold weightedTerm alternatingModel
  rw [fallingFactorial_eq_risingShift n x hn]
  have hrpow : Real.rpow (n : ℝ) (-p) = (Real.rpow (n : ℝ) p)⁻¹ :=
    Real.rpow_neg (Nat.cast_nonneg n) p
  rw [hrpow]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : Real.rpow (n : ℝ) p ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hnR p)
  have hfac : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp [hn0, hfac]

private def asymptoticModel (p x : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (-(p + x + 1)) / |Real.Gamma (-x)|

private theorem gamma_neg_ne_zero {x : ℝ} (hx : ¬isNonnegativeInteger x) :
    Real.Gamma (-x) ≠ 0 := by
  apply Real.Gamma_ne_zero
  intro m hm
  apply hx
  exact ⟨m, by push_cast at hm; linarith⟩

private theorem risingShift_special_eq_gammaDenom (x : ℝ) (n : ℕ) :
    risingShift (-(1 + x)) (n + 1) =
      ∏ j ∈ Finset.range (n + 1), (-x + (j : ℝ)) := by
  unfold risingShift
  apply Finset.prod_congr rfl
  intro j hj
  push_cast
  ring

private theorem risingShift_special_ne_zero {x : ℝ}
    (hx : ¬isNonnegativeInteger x) (n : ℕ) :
    risingShift (-(1 + x)) (n + 1) ≠ 0 := by
  rw [risingShift_special_eq_gammaDenom]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj hzero
  apply hx
  exact ⟨j, by push_cast at hzero; linarith⟩

private theorem abs_risingShift_div_factorial_eq_gammaSeq {x : ℝ}
    (hx : ¬isNonnegativeInteger x) (n : ℕ) (hn : 1 ≤ n) :
    |risingShift (-(1 + x)) (n + 1)| / (((n + 1).factorial : ℕ) : ℝ) =
      (n : ℝ) ^ (-x) /
        (((n + 1 : ℕ) : ℝ) * |Real.GammaSeq (-x) n|) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hD := risingShift_special_ne_zero hx n
  have hGabs :
      |Real.GammaSeq (-x) n| =
        (n : ℝ) ^ (-x) * (n.factorial : ℝ) /
          |risingShift (-(1 + x)) (n + 1)| := by
    unfold Real.GammaSeq
    change |(n : ℝ) ^ (-x) * (n.factorial : ℝ) /
        (∏ j ∈ Finset.range (n + 1), (-x + (j : ℝ)))| = _
    rw [← risingShift_special_eq_gammaDenom]
    rw [abs_div, abs_mul,
      abs_of_pos (Real.rpow_pos_of_pos hnR (-x)),
      abs_of_pos (by positivity : (0 : ℝ) < (n.factorial : ℝ))]
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, hGabs]
  have hDabs : |risingShift (-(1 + x)) (n + 1)| ≠ 0 := abs_ne_zero.mpr hD
  have hpow : (n : ℝ) ^ (-x) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hnR (-x))
  have hfac : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp [hDabs, hpow, hfac]

private theorem abs_weightedTerm_eq_gammaModel {p x : ℝ}
    (hx : ¬isNonnegativeInteger x) (n : ℕ) (hn : 1 ≤ n) :
    |weightedTerm p x (n + 1)| =
      (((n + 1 : ℕ) : ℝ) ^ (-p) * (n : ℝ) ^ (-x)) /
        (((n + 1 : ℕ) : ℝ) * |Real.GammaSeq (-x) n|) := by
  calc
    |weightedTerm p x (n + 1)| =
        (((n + 1 : ℕ) : ℝ) ^ (-p)) *
          (|risingShift (-(1 + x)) (n + 1)| /
            (((n + 1).factorial : ℕ) : ℝ)) := by
      unfold weightedTerm
      change |((n + 1 : ℕ) : ℝ) ^ (-p) * fallingFactorial x (n + 1) /
          (((n + 1).factorial : ℕ) : ℝ)| = _
      rw [fallingFactorial_eq_risingShift (n + 1) x (by omega)]
      have hn1R : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      have habsPow : |(((n + 1 : ℕ) : ℝ) ^ (-p))| =
          ((n + 1 : ℕ) : ℝ) ^ (-p) :=
        abs_of_pos (Real.rpow_pos_of_pos hn1R (-p))
      have habsFac : |((((n + 1).factorial : ℕ) : ℝ))| =
          (((n + 1).factorial : ℕ) : ℝ) :=
        abs_of_pos (by positivity)
      rw [abs_div, abs_mul, habsPow, habsFac]
      simp only [abs_mul, abs_neg, abs_pow, abs_one, one_pow, one_mul]
      ring
    _ = ((((n + 1 : ℕ) : ℝ) ^ (-p)) * (n : ℝ) ^ (-x)) /
        (((n + 1 : ℕ) : ℝ) * |Real.GammaSeq (-x) n|) := by
      rw [abs_risingShift_div_factorial_eq_gammaSeq hx n hn]
      ring

private theorem abs_weightedTerm_isEquivalent {p x : ℝ}
    (hx : ¬isNonnegativeInteger x) :
    (fun n : ℕ => |weightedTerm p x (n + 1)|) ~[atTop]
      asymptoticModel p x := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hnorm :
      Tendsto (norm ∘ fun n : ℕ => (n : ℝ)) atTop atTop := by
    simpa [Function.comp_def, Real.norm_eq_abs, abs_of_nonneg] using hcast
  have hN0 : (fun n : ℕ => (n : ℝ)) ~[atTop] fun n : ℕ => (n : ℝ) :=
    IsEquivalent.refl
  have hN : (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) ~[atTop]
      fun n : ℕ => (n : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one] using
      (hN0.add_const_of_norm_tendsto_atTop (c := (1 : ℝ)) hnorm)
  have hpEq : (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-p)) ~[atTop]
      (fun n : ℕ => (n : ℝ) ^ (-p)) := by
    exact hN.rpow (fun n => Nat.cast_nonneg n)
  have hxEq : (fun n : ℕ => (n : ℝ) ^ (-x)) ~[atTop]
      (fun n : ℕ => (n : ℝ) ^ (-x)) := IsEquivalent.refl
  have hGammaT : Tendsto (fun n : ℕ => |Real.GammaSeq (-x) n|) atTop
      (𝓝 |Real.Gamma (-x)|) :=
    (continuous_abs.tendsto _).comp (Real.GammaSeq_tendsto_Gamma (-x))
  have hGammaNe : |Real.Gamma (-x)| ≠ 0 :=
    abs_ne_zero.mpr (gamma_neg_ne_zero hx)
  have hGammaEq : (fun n : ℕ => |Real.GammaSeq (-x) n|) ~[atTop]
      (fun _ : ℕ => |Real.Gamma (-x)|) :=
    (isEquivalent_const_iff_tendsto hGammaNe).2 hGammaT
  have hfrac := (hpEq.mul hxEq).div (hN.mul hGammaEq)
  have hright :
      (fun n : ℕ =>
          ((n : ℝ) ^ (-p) * (n : ℝ) ^ (-x)) /
            ((n : ℝ) * |Real.Gamma (-x)|)) =ᶠ[atTop]
        asymptoticModel p x := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    dsimp [asymptoticModel]
    rw [show -(p + x + 1) = (-p + -x) - 1 by ring,
      Real.rpow_sub_one hnR.ne' (-p + -x),
      Real.rpow_add hnR (-p) (-x)]
    ring
  have hleft :
      (fun n : ℕ =>
          (((n + 1 : ℕ) : ℝ) ^ (-p) * (n : ℝ) ^ (-x)) /
            (((n + 1 : ℕ) : ℝ) * |Real.GammaSeq (-x) n|)) =ᶠ[atTop]
        (fun n : ℕ => |weightedTerm p x (n + 1)|) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (abs_weightedTerm_eq_gammaModel hx n hn).symm
  exact (hfrac.congr_left hleft).congr_right hright

private theorem abs_weightedTerm_summable_iff {p x : ℝ}
    (hx : ¬isNonnegativeInteger x) :
    Summable (fun n : ℕ => |weightedTerm p x (n + 1)|) ↔ -x < p := by
  rw [(abs_weightedTerm_isEquivalent hx).summable_iff_nat]
  unfold asymptoticModel
  rw [summable_div_const_iff (abs_ne_zero.mpr (gamma_neg_ne_zero hx)),
    Real.summable_nat_rpow]
  constructor <;> intro h <;> linarith

private theorem fallingFactorial_natCast_eq_zero (m n : ℕ) (h : m < n) :
    fallingFactorial (m : ℝ) n = 0 := by
  unfold fallingFactorial
  apply Finset.prod_eq_zero (Finset.mem_range.mpr h)
  norm_num

private theorem abs_weightedTerm_summable_of_nat (p : ℝ) (m : ℕ) :
    Summable (fun n : ℕ => |weightedTerm p (m : ℝ) (n + 1)|) := by
  apply summable_of_ne_finset_zero (s := Finset.range m)
  intro n hn
  have hmn : m < n + 1 := by
    simp only [Finset.mem_range, not_lt] at hn
    omega
  unfold weightedTerm
  rw [fallingFactorial_natCast_eq_zero m (n + 1) hmn, mul_zero, zero_div, abs_zero]

private theorem seriesConverges_alternating_of_antitone
    (b : ℕ → ℝ) (hanti : Antitone b) (ht : Tendsto b atTop (nhds 0)) :
    ProofGap.SeriesConverges (fun n : ℕ => (-1 : ℝ) ^ n * b n) := by
  obtain ⟨s, hs⟩ := hanti.tendsto_alternating_series_of_tendsto_zero ht
  unfold ProofGap.SeriesConverges
  refine ⟨s, ?_⟩
  simpa only [HasSum, SummationFilter.conditional_filter_eq_map_range,
    tendsto_map'_iff, Function.comp_apply] using hs

private theorem seriesConverges_of_tail (u : ℕ → ℝ) (K : ℕ)
    (h : ProofGap.SeriesConverges (fun n : ℕ => u (n + K))) :
    ProofGap.SeriesConverges u := by
  unfold ProofGap.SeriesConverges at h ⊢
  rcases h with ⟨s, hs⟩
  have ht : Tendsto
      (fun n : ℕ => ∑ i ∈ Finset.range n, u (i + K)) atTop (nhds s) := by
    simpa only [HasSum, SummationFilter.conditional_filter_eq_map_range,
      tendsto_map'_iff, Function.comp_apply] using hs
  have ht' := ht.comp (tendsto_sub_atTop_nat K)
  have hfull : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, u i) atTop
      (nhds ((∑ i ∈ Finset.range K, u i) + s)) := by
    refine (tendsto_const_nhds.add ht').congr' ?_
    filter_upwards [eventually_ge_atTop K] with n hn
    rw [show n = K + (n - K) by omega, Finset.sum_range_add]
    simp only [Function.comp_apply, Nat.add_sub_cancel_left]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    omega
  refine ⟨(∑ i ∈ Finset.range K, u i) + s, ?_⟩
  simpa only [HasSum, SummationFilter.conditional_filter_eq_map_range,
    tendsto_map'_iff, Function.comp_apply] using hfull

private theorem seriesConverges_tendsto_zero {u : ℕ → ℝ}
    (h : ProofGap.SeriesConverges u) : Tendsto u atTop (nhds 0) := by
  unfold ProofGap.SeriesConverges at h
  rcases h with ⟨s, hs⟩
  have hpartial : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, u i)
      atTop (nhds s) := by
    simpa only [HasSum, SummationFilter.conditional_filter_eq_map_range,
      tendsto_map'_iff, Function.comp_apply] using hs
  have hshift := hpartial.comp (tendsto_add_atTop_nat 1)
  have hdiff := hshift.sub hpartial
  convert hdiff using 1
  · funext n
    change u n = (∑ i ∈ Finset.range (n + 1), u i) - ∑ i ∈ Finset.range n, u i
    rw [Finset.sum_range_succ]
    ring
  · simp

private theorem weightedTerm_succ (p x : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    weightedTerm p x (n + 1) =
      -weightedTerm p x n *
        ((1 + (-(1 + x)) / (n + 1 : ℝ)) *
          Real.rpow (1 - 1 / (n + 1 : ℝ)) p) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1R : (0 : ℝ) < n + 1 := by positivity
  have hbase : 1 - 1 / (n + 1 : ℝ) = (n : ℝ) / (n + 1 : ℝ) := by
    field_simp
    ring
  have hrpow : Real.rpow (n + 1 : ℝ) (-p) =
      Real.rpow (n : ℝ) (-p) * Real.rpow (1 - 1 / (n + 1 : ℝ)) p := by
    simp only [Real.rpow_eq_pow]
    rw [hbase, Real.div_rpow hnR.le hn1R.le,
      Real.rpow_neg hnR.le, Real.rpow_neg hn1R.le]
    have hnPow : Real.rpow (n : ℝ) p ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hnR p)
    have hn1Pow : Real.rpow (n + 1 : ℝ) p ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos hn1R p)
    field_simp [hnPow, hn1Pow]
  unfold weightedTerm fallingFactorial
  rw [Finset.prod_range_succ, Nat.factorial_succ]
  rw [show Real.rpow (((n + 1 : ℕ) : ℝ)) (-p) =
      Real.rpow (n : ℝ) (-p) * Real.rpow (1 - 1 / (n + 1 : ℝ)) p by
    simpa only [Nat.cast_add, Nat.cast_one] using hrpow]
  push_cast
  have hfac : (n.factorial : ℝ) ≠ 0 := by positivity
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hn10 : (n + 1 : ℝ) ≠ 0 := ne_of_gt hn1R
  field_simp [hfac, hn0, hn10]
  ring

private theorem eventually_ratio_lt_one (p t : ℝ) (hp : t < p) :
    ∀ᶠ n : ℕ in atTop,
      (1 + t / (n + 1 : ℝ)) * Real.rpow (1 - 1 / (n + 1 : ℝ)) p < 1 := by
  let F : ℝ → ℝ := fun z => (1 + t * z) * Real.rpow (1 - z) p
  have hinner : HasDerivAt (fun z : ℝ => 1 - z) (-1) 0 := by
    convert (hasDerivAt_const 0 (1 : ℝ)).sub (hasDerivAt_id 0) using 1 <;> ring
  have hpow : HasDerivAt (fun z : ℝ => Real.rpow (1 - z) p) (-p) 0 := by
    convert hinner.rpow_const (p := p) (Or.inl (by norm_num)) using 1 <;>
      norm_num <;> ring
  have hlinear : HasDerivAt (fun z : ℝ => 1 + t * z) t 0 := by
    convert (hasDerivAt_const 0 (1 : ℝ)).add
      ((hasDerivAt_id 0).const_mul t) using 1 <;> ring
  have hF : HasDerivAt F (t - p) 0 := by
    dsimp [F]
    convert hlinear.mul hpow using 1 <;> norm_num <;> ring
  let z : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ)⁻¹
  have hz0 : Tendsto z atTop (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact ((tendsto_natCast_atTop_atTop.comp
        (tendsto_add_atTop_nat 1)).inv_tendsto_atTop)
    · exact Filter.Eventually.of_forall fun n => by
        change 0 < (((n + 1 : ℕ) : ℝ))⁻¹
        positivity
  have hslope := hF.tendsto_slope_zero_right.comp hz0
  have hevent : ∀ᶠ n : ℕ in atTop,
      (z n)⁻¹ • (F (0 + z n) - F 0) < 0 :=
    hslope.eventually (Iio_mem_nhds (sub_neg.mpr hp))
  filter_upwards [hevent] with n hn
  have hzpos : 0 < z n := by
    dsimp [z]
    positivity
  rw [smul_neg_iff_of_pos_left (inv_pos.mpr hzpos)] at hn
  have hFlt : F (z n) < F 0 := by simpa using hn
  simpa [F, z, div_eq_mul_inv] using hFlt

private theorem abs_weightedTerm_tendsto_zero {p x : ℝ}
    (hx : ¬isNonnegativeInteger x) (hp : -(1 + x) < p) :
    Tendsto (fun n : ℕ => |weightedTerm p x (n + 1)|) atTop (nhds 0) := by
  have hexp : 0 < p + x + 1 := by linarith
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(p + x + 1)))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hexp).comp tendsto_natCast_atTop_atTop
  have hmodel : Tendsto (asymptoticModel p x) atTop (nhds 0) := by
    unfold asymptoticModel
    simpa using hpow.div_const |Real.Gamma (-x)|
  exact (abs_weightedTerm_isEquivalent hx).tendsto_nhds_iff.mpr hmodel

private theorem weightedTerm_seriesConverges {p x : ℝ}
    (hx : ¬isNonnegativeInteger x) (hp : -(1 + x) < p) :
    ProofGap.SeriesConverges (fun n : ℕ => weightedTerm p x (n + 1)) := by
  let t : ℝ := -(1 + x)
  let ratio : ℕ → ℝ := fun n =>
    (1 + t / (n + 1 : ℝ)) * Real.rpow (1 - 1 / (n + 1 : ℝ)) p
  have hratioLt : ∀ᶠ n : ℕ in atTop, ratio n < 1 := by
    simpa [ratio, t] using eventually_ratio_lt_one p (-(1 + x)) hp
  have hcast : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hlarge : ∀ᶠ n : ℕ in atTop, -t < ((n + 1 : ℕ) : ℝ) :=
    hcast.eventually (eventually_gt_atTop (-t))
  have hratioPos : ∀ᶠ n : ℕ in atTop, 0 < ratio n := by
    filter_upwards [hlarge, eventually_ge_atTop 1] with n hnLarge hnOne
    push_cast at hnLarge
    have hn1 : (0 : ℝ) < n + 1 := by positivity
    have hfirst : 0 < 1 + t / (n + 1 : ℝ) := by
      rw [show 1 + t / (n + 1 : ℝ) = ((n + 1 : ℝ) + t) / (n + 1 : ℝ) by
        field_simp]
      exact div_pos (by linarith) hn1
    have hbase : 0 < 1 - 1 / (n + 1 : ℝ) := by
      rw [show 1 - 1 / (n + 1 : ℝ) = (n : ℝ) / (n + 1 : ℝ) by
        field_simp
        ring]
      exact div_pos (by exact_mod_cast hnOne) hn1
    exact mul_pos hfirst (Real.rpow_pos_of_pos hbase p)
  have hratio : ∀ᶠ n : ℕ in atTop, 0 < ratio n ∧ ratio n < 1 :=
    hratioPos.and hratioLt
  rcases eventually_atTop.1 hratio with ⟨K, hK⟩
  let a : ℕ → ℝ := fun n => weightedTerm p x (n + K + 1)
  let b : ℕ → ℝ := fun n => |a n|
  let r : ℕ → ℝ := fun n => ratio (n + K + 1)
  have hr (n : ℕ) : 0 < r n ∧ r n < 1 := by
    exact hK (n + K + 1) (by omega)
  have hrec (n : ℕ) : a (n + 1) = -a n * r n := by
    dsimp [a, r, ratio, t]
    simpa [add_assoc, add_comm, add_left_comm] using
      weightedTerm_succ p x (n + K + 1) (by omega)
  have hbanti : Antitone b := by
    apply antitone_nat_of_succ_le
    intro n
    dsimp [b]
    rw [hrec n, abs_mul, abs_neg, abs_of_pos (hr n).1]
    exact mul_le_of_le_one_right (abs_nonneg _) (hr n).2.le
  have hbtend : Tendsto b atTop (nhds 0) := by
    have hzero := (abs_weightedTerm_tendsto_zero hx hp).comp
      (tendsto_add_atTop_nat K)
    simpa [b, a, add_assoc, add_comm, add_left_comm] using hzero
  have halt := seriesConverges_alternating_of_antitone b hbanti hbtend
  let σ : ℝ := if 0 ≤ a 0 then 1 else -1
  have hrepr : ∀ n : ℕ, a n = σ * ((-1 : ℝ) ^ n * b n) := by
    intro n
    induction n with
    | zero =>
        dsimp [σ, b]
        split_ifs with h
        · rw [abs_of_nonneg h]
          ring
        · have ha0 : a 0 < 0 := lt_of_not_ge h
          rw [abs_of_neg ha0]
          ring
    | succ n ih =>
        have hbrec : b (n + 1) = b n * r n := by
          dsimp [b]
          rw [hrec n, abs_mul, abs_neg, abs_of_pos (hr n).1]
        rw [hrec n, ih, hbrec, pow_succ]
        ring
  have htail : ProofGap.SeriesConverges a := by
    unfold ProofGap.SeriesConverges at halt ⊢
    rcases halt with ⟨s, hs⟩
    refine ⟨σ * s, ?_⟩
    convert hs.mul_left σ using 1
    funext n
    exact hrepr n
  apply seriesConverges_of_tail
    (fun n : ℕ => weightedTerm p x (n + 1)) K
  simpa [a, add_assoc, add_comm, add_left_comm] using htail

private theorem weightedTerm_seriesConverges_imp_lower {p x : ℝ}
    (hx : ¬isNonnegativeInteger x)
    (hconv : ProofGap.SeriesConverges
      (fun n : ℕ => weightedTerm p x (n + 1))) :
    -(1 + x) < p := by
  have habs : Tendsto (fun n : ℕ => |weightedTerm p x (n + 1)|)
      atTop (nhds 0) := by
    have ht := seriesConverges_tendsto_zero hconv
    simpa using (continuous_abs.tendsto 0).comp ht
  have hmodel : Tendsto (asymptoticModel p x) atTop (nhds 0) :=
    (abs_weightedTerm_isEquivalent hx).tendsto_nhds_iff.mp habs
  by_contra hp
  have hle : p + x + 1 ≤ 0 := by linarith
  rcases eq_or_lt_of_le hle with heq | hlt
  · have hconst : Tendsto (asymptoticModel p x) atTop
        (nhds (1 / |Real.Gamma (-x)|)) := by
      have hfun : asymptoticModel p x =
          fun _ : ℕ => 1 / |Real.Gamma (-x)| := by
        funext n
        unfold asymptoticModel
        rw [heq]
        norm_num
      rw [hfun]
      exact tendsto_const_nhds
    have hzero : (0 : ℝ) = 1 / |Real.Gamma (-x)| :=
      tendsto_nhds_unique hmodel hconst
    exact (one_div_ne_zero (abs_ne_zero.mpr (gamma_neg_ne_zero hx))) hzero.symm
  · have hexp : 0 < -(p + x + 1) := by linarith
    have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(p + x + 1)))
        atTop atTop :=
      (tendsto_rpow_atTop hexp).comp tendsto_natCast_atTop_atTop
    have hmodelTop : Tendsto (asymptoticModel p x) atTop atTop := by
      unfold asymptoticModel
      exact Tendsto.atTop_div_const
        (abs_pos.mpr (gamma_neg_ne_zero hx)) hpow
    exact not_tendsto_nhds_of_tendsto_atTop hmodelTop 0 hmodel

theorem gap1 (n : ℕ) (x : ℝ) :
    fallingFactorial x n = ∏ k ∈ Finset.range n, (x - k) := by
  rfl

theorem gap2 (n : ℕ) (x : ℝ) (hn : 1 ≤ n) :
    fallingFactorial x n =
      (-1 : ℝ) ^ (n - 1) *
        (x * (∏ k ∈ Finset.range (n - 1),
          (((n - 1 - k : ℕ) : ℝ) - x))) := by
  exact fallingFactorial_eq_reflected n x hn

theorem gap3 (n : ℕ) (x : ℝ) (hn : 1 ≤ n) :
    fallingFactorial x n =
      -(-1 : ℝ) ^ (n - 1) * risingShift (-(1 + x)) n := by
  exact fallingFactorial_eq_risingShift n x hn

theorem gap4 (p x : ℝ) :
    ∑' n : ℕ, weightedTerm p x (n + 1) =
      -(∑' n : ℕ, alternatingModel p (-(1 + x)) (n + 1)) := by
  have hfun : (fun n : ℕ => weightedTerm p x (n + 1)) =
      fun n : ℕ => -alternatingModel p (-(1 + x)) (n + 1) := by
    funext n
    exact weightedTerm_eq_neg_alternatingModel p x (n + 1) (by omega)
  rw [hfun, tsum_neg]

theorem gap5 (p x : ℝ) (hp : p > -(1 + x) + 1) :
    Summable (fun n : ℕ => |weightedTerm p x (n + 1)|) := by
  by_cases hx : isNonnegativeInteger x
  · obtain ⟨m, rfl⟩ := hx
    exact abs_weightedTerm_summable_of_nat p m
  · apply (abs_weightedTerm_summable_iff hx).2
    linarith

theorem gap6 (p x : ℝ) (hp : p > -x) :
    Summable (fun n : ℕ => |weightedTerm p x (n + 1)|) := by
  by_cases hx : isNonnegativeInteger x
  · obtain ⟨m, rfl⟩ := hx
    exact abs_weightedTerm_summable_of_nat p m
  · exact (abs_weightedTerm_summable_iff hx).2 hp

theorem gap7 (p x : ℝ) (hx : isNonnegativeInteger x) :
    Summable (fun n : ℕ => |weightedTerm p x (n + 1)|) := by
  obtain ⟨m, rfl⟩ := hx
  exact abs_weightedTerm_summable_of_nat p m

theorem gap8 (p x : ℝ) (hx : ¬ isNonnegativeInteger x)
    (hp₁ : -(1 + x) < p) (hp₂ : p ≤ -x) :
    ConditionallySummable p x := by
  refine ⟨weightedTerm_seriesConverges hx hp₁, ?_⟩
  intro hs
  have hp : -x < p := (abs_weightedTerm_summable_iff hx).1 hs
  linarith

theorem gap9 (p x : ℝ) (hx : ¬ isNonnegativeInteger x)
    (hp₁ : -(1 + x) < p) (hp₂ : p ≤ -x) :
    ConditionallySummable p x := by
  exact gap8 p x hx hp₁ hp₂

theorem gap10 :
    {q : ℝ × ℝ |
        Summable (fun n : ℕ => |weightedTerm q.1 q.2 (n + 1)|)} =
      {q : ℝ × ℝ | -q.2 < q.1 ∨ isNonnegativeInteger q.2} := by
  ext q
  simp only [Set.mem_setOf_eq]
  by_cases hx : isNonnegativeInteger q.2
  · simp [hx, gap7 q.1 q.2 hx]
  · simp [hx, abs_weightedTerm_summable_iff hx]

theorem gap11 :
    {q : ℝ × ℝ | ConditionallySummable q.1 q.2} =
      {q : ℝ × ℝ |
        ¬ isNonnegativeInteger q.2 ∧ -(1 + q.2) < q.1 ∧ q.1 ≤ -q.2} := by
  ext q
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h
    have hx : ¬isNonnegativeInteger q.2 := by
      intro hx
      exact h.2 (gap7 q.1 q.2 hx)
    have hp₁ : -(1 + q.2) < q.1 :=
      weightedTerm_seriesConverges_imp_lower hx h.1
    have hp₂ : q.1 ≤ -q.2 := by
      by_contra hp₂
      apply h.2
      exact (abs_weightedTerm_summable_iff hx).2 (lt_of_not_ge hp₂)
    exact ⟨hx, hp₁, hp₂⟩
  · rintro ⟨hx, hp₁, hp₂⟩
    exact gap8 q.1 q.2 hx hp₁ hp₂

end

end ProofGap.Exercise2739_2

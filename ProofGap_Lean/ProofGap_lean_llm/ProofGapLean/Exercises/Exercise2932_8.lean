import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Central
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.InfiniteSum.Order

namespace ProofGap.Exercise2932_8

noncomputable section

open scoped BigOperators Interval

def integrand (x : ℝ) : ℝ :=
  1 / Real.sqrt (1 + x ^ 4)

def centralCoefficient (n : ℕ) : ℝ :=
  (Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n

def binomialTerm (n : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ n * centralCoefficient n * x ^ (4 * n)

def integratedTerm (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * centralCoefficient n / (4 * n + 1 : ℕ)

def targetIntegral : ℝ :=
  ∫ x in (0 : ℝ)..1, integrand x

def partialIntegral : ℝ :=
  ∑ n ∈ Finset.range 24, integratedTerm n

def remainder : ℝ :=
  targetIntegral - partialIntegral

def firstOmittedTerm : ℝ :=
  centralCoefficient 24 / 97

def Approx (u v ε : ℝ) : Prop :=
  |u - v| < ε

private def positiveHalfChoose (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * Ring.choose (-(1 / 2 : ℝ)) n

private theorem ringChoose_succ (r : ℝ) (n : ℕ) :
    Ring.choose r (n + 1) =
      Ring.choose r n * (r - n) / (n + 1) := by
  rw [Ring.choose_eq_smul, Ring.choose_eq_smul]
  simp only [smul_eq_mul, descPochhammer_succ_right,
    Polynomial.smeval_mul, Polynomial.smeval_sub,
    Polynomial.smeval_X, Polynomial.smeval_natCast,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hf, hn]
  ring

private theorem positiveHalfChoose_succ (n : ℕ) :
    positiveHalfChoose (n + 1) =
      positiveHalfChoose n * (2 * (n : ℝ) + 1) /
        (2 * ((n : ℝ) + 1)) := by
  rw [positiveHalfChoose, positiveHalfChoose, ringChoose_succ, pow_succ]
  push_cast
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hn]
  ring

private theorem centralCoefficient_succ (n : ℕ) :
    centralCoefficient (n + 1) =
      centralCoefficient n * (2 * (n : ℝ) + 1) /
        (2 * ((n : ℝ) + 1)) := by
  have hnat := Nat.succ_mul_centralBinom_succ n
  have hreal := congrArg (fun m : ℕ => (m : ℝ)) hnat
  push_cast at hreal
  change
    (Nat.centralBinom (n + 1) : ℝ) / (4 : ℝ) ^ (n + 1) =
      ((Nat.centralBinom n : ℝ) / (4 : ℝ) ^ n) *
        (2 * (n : ℝ) + 1) / (2 * ((n : ℝ) + 1))
  rw [pow_succ]
  have hp : (4 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hp, hn]
  nlinarith

private theorem positiveHalfChoose_eq_centralCoefficient (n : ℕ) :
    positiveHalfChoose n = centralCoefficient n := by
  induction n with
  | zero =>
      norm_num [positiveHalfChoose, centralCoefficient,
        Ring.choose_zero_right]
  | succ n ih =>
      rw [positiveHalfChoose_succ, centralCoefficient_succ, ih]

private theorem centralCoefficient_pos (n : ℕ) :
    0 < centralCoefficient n := by
  change 0 < (Nat.centralBinom n : ℝ) / (4 : ℝ) ^ n
  apply div_pos
  · exact_mod_cast Nat.centralBinom_pos n
  · positivity

private theorem centralCoefficient_nonneg (n : ℕ) :
    0 ≤ centralCoefficient n := (centralCoefficient_pos n).le

private theorem centralCoefficient_strictAnti :
    StrictAnti centralCoefficient := by
  apply strictAnti_nat_of_succ_lt
  intro n
  rw [centralCoefficient_succ]
  have hc := centralCoefficient_pos n
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  apply (div_lt_iff₀ (by positivity)).2
  nlinarith

private theorem centralCoefficient_sq_mul_succ_le_one (n : ℕ) :
    centralCoefficient n ^ 2 * ((n + 1 : ℕ) : ℝ) ≤ 1 := by
  induction n with
  | zero =>
      norm_num [centralCoefficient]
  | succ n ih =>
      rw [centralCoefficient_succ]
      push_cast at ih ⊢
      let c := centralCoefficient n
      let t := (n : ℝ)
      have ht : 0 ≤ t := by positivity
      have hfac :
          (2 * t + 1) ^ 2 * (t + 2) ≤
            4 * (t + 1) ^ 3 := by
        nlinarith [sq_nonneg t]
      have hfacmul :=
        mul_le_mul_of_nonneg_left hfac (sq_nonneg c)
      have hscale :
          c ^ 2 * (t + 1) * (4 * (t + 1) ^ 2) ≤
            4 * (t + 1) ^ 2 := by
        have hs0 : 0 ≤ 4 * (t + 1) ^ 2 := by positivity
        nlinarith [mul_le_mul_of_nonneg_right ih hs0]
      have ht1 : t + 1 ≠ 0 := by positivity
      dsimp [c, t] at hfacmul hscale ⊢
      field_simp [ht1]
      nlinarith

private theorem centralCoefficient_le_inv_sqrt (n : ℕ) :
    centralCoefficient n ≤
      1 / Real.sqrt (((n + 1 : ℕ) : ℝ)) := by
  have ha : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hs : 0 < Real.sqrt (((n + 1 : ℕ) : ℝ)) :=
    Real.sqrt_pos.2 ha
  apply (le_div_iff₀ hs).2
  have hsquare :
      (centralCoefficient n *
          Real.sqrt (((n + 1 : ℕ) : ℝ))) ^ 2 ≤ 1 := by
    rw [mul_pow, Real.sq_sqrt ha.le]
    exact centralCoefficient_sq_mul_succ_le_one n
  have hnonneg :
      0 ≤ centralCoefficient n *
        Real.sqrt (((n + 1 : ℕ) : ℝ)) :=
    mul_nonneg (centralCoefficient_nonneg n) (Real.sqrt_nonneg _)
  nlinarith

private def integratedMagnitude (n : ℕ) : ℝ :=
  centralCoefficient n / (((4 * n + 1 : ℕ) : ℝ))

private theorem integratedMagnitude_pos (n : ℕ) :
    0 < integratedMagnitude n := by
  unfold integratedMagnitude
  exact div_pos (centralCoefficient_pos n) (by positivity)

private theorem integratedMagnitude_strictAnti :
    StrictAnti integratedMagnitude := by
  apply strictAnti_nat_of_succ_lt
  intro n
  unfold integratedMagnitude
  have hc := centralCoefficient_strictAnti (Nat.lt_succ_self n)
  have hden : (0 : ℝ) < (((4 * (n + 1) + 1 : ℕ) : ℝ)) := by
    positivity
  have hnum : 0 ≤ centralCoefficient n := centralCoefficient_nonneg n
  calc
    centralCoefficient (n + 1) / (((4 * (n + 1) + 1 : ℕ) : ℝ)) <
        centralCoefficient n / (((4 * (n + 1) + 1 : ℕ) : ℝ)) :=
      div_lt_div_of_pos_right hc hden
    _ ≤ centralCoefficient n / (((4 * n + 1 : ℕ) : ℝ)) := by
      exact div_le_div_of_nonneg_left hnum (by positivity) (by norm_num)

private def pMajorant (n : ℕ) : ℝ :=
  Real.rpow (((n + 1 : ℕ) : ℝ)) (-(3 / 2 : ℝ))

private theorem pMajorant_eq (n : ℕ) :
    pMajorant n =
      1 / ((((n + 1 : ℕ) : ℝ)) *
        Real.sqrt (((n + 1 : ℕ) : ℝ))) := by
  have ha : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
  have hapos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  unfold pMajorant
  rw [show (-(3 / 2 : ℝ)) = -(1 + 1 / 2) by ring]
  calc
    Real.rpow (((n + 1 : ℕ) : ℝ)) (-(1 + 1 / 2)) =
        (Real.rpow (((n + 1 : ℕ) : ℝ)) (1 + 1 / 2))⁻¹ :=
      Real.rpow_neg ha (1 + 1 / 2)
    _ = (((((n + 1 : ℕ) : ℝ)) *
          Real.sqrt (((n + 1 : ℕ) : ℝ))))⁻¹ := by
      apply congrArg Inv.inv
      have hadd :
          Real.rpow (((n + 1 : ℕ) : ℝ)) (1 + 1 / 2) =
            Real.rpow (((n + 1 : ℕ) : ℝ)) 1 *
              Real.rpow (((n + 1 : ℕ) : ℝ)) (1 / 2) :=
        Real.rpow_add hapos 1 (1 / 2)
      rw [hadd, Real.rpow_eq_pow, Real.rpow_eq_pow,
        Real.rpow_one, ← Real.sqrt_eq_rpow]
    _ = 1 / ((((n + 1 : ℕ) : ℝ)) *
          Real.sqrt (((n + 1 : ℕ) : ℝ))) :=
      inv_eq_one_div _

private theorem integratedMagnitude_le_pMajorant (n : ℕ) :
    integratedMagnitude n ≤ pMajorant n := by
  rw [pMajorant_eq]
  have hc := centralCoefficient_le_inv_sqrt n
  have hden :
      (((n + 1 : ℕ) : ℝ)) ≤ (((4 * n + 1 : ℕ) : ℝ)) := by
    norm_cast
    omega
  unfold integratedMagnitude
  have hs : 0 < Real.sqrt (((n + 1 : ℕ) : ℝ)) := by positivity
  calc
    centralCoefficient n / (((4 * n + 1 : ℕ) : ℝ)) ≤
        (1 / Real.sqrt (((n + 1 : ℕ) : ℝ))) /
          (((4 * n + 1 : ℕ) : ℝ)) := by
      exact div_le_div_of_nonneg_right hc (by positivity)
    _ ≤ (1 / Real.sqrt (((n + 1 : ℕ) : ℝ))) /
          (((n + 1 : ℕ) : ℝ)) := by
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = 1 / ((((n + 1 : ℕ) : ℝ)) *
          Real.sqrt (((n + 1 : ℕ) : ℝ))) := by
      field_simp

private theorem summable_pMajorant : Summable pMajorant := by
  have hbase :
      Summable (fun n : ℕ =>
        Real.rpow (n : ℝ) (-(3 / 2 : ℝ))) :=
    Real.summable_nat_rpow.2 (by norm_num)
  have hinj : Function.Injective (fun n : ℕ => n + 1) := by
    intro a b h
    exact Nat.add_right_cancel h
  apply (hbase.comp_injective hinj).congr
  intro n
  norm_num [pMajorant, Function.comp_def, Nat.cast_add]

private theorem summable_integratedMagnitude :
    Summable integratedMagnitude :=
  Summable.of_nonneg_of_le
    (fun n => (integratedMagnitude_pos n).le)
    integratedMagnitude_le_pMajorant summable_pMajorant

private theorem integratedTerm_eq_alternating (n : ℕ) :
    integratedTerm n = (-1 : ℝ) ^ n * integratedMagnitude n := by
  unfold integratedTerm integratedMagnitude
  ring

private theorem binomialTerm_intervalIntegrable (n : ℕ) :
    IntervalIntegrable (binomialTerm n) MeasureTheory.volume
      (0 : ℝ) 1 := by
  apply Continuous.intervalIntegrable
  unfold binomialTerm
  fun_prop

private theorem integral_binomialTerm (n : ℕ) :
    (∫ x in (0 : ℝ)..1, binomialTerm n x) =
      integratedTerm n := by
  have hfun :
      (fun x : ℝ => binomialTerm n x) =
        fun x : ℝ =>
          ((-1 : ℝ) ^ n * centralCoefficient n) *
            x ^ (4 * n) := by
    rfl
  rw [hfun, intervalIntegral.integral_const_mul, integral_pow]
  simp only [one_pow, zero_pow, Nat.succ_ne_zero, ne_eq,
    not_false_eq_true, sub_zero]
  unfold integratedTerm
  push_cast
  ring

private theorem norm_binomialTerm (n : ℕ) (x : ℝ) :
    ‖binomialTerm n x‖ =
      centralCoefficient n * x ^ (4 * n) := by
  have hp : 0 ≤ x ^ (4 * n) := by
    rw [show 4 * n = 2 * (2 * n) by omega, pow_mul]
    positivity
  rw [Real.norm_eq_abs]
  unfold binomialTerm
  rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_nonneg (centralCoefficient_nonneg n), abs_of_nonneg hp]
  simp

private theorem integral_norm_binomialTerm (n : ℕ) :
    (∫ x in (0 : ℝ)..1, ‖binomialTerm n x‖) =
      integratedMagnitude n := by
  simp_rw [norm_binomialTerm]
  rw [intervalIntegral.integral_const_mul, integral_pow]
  simp only [one_pow, zero_pow, Nat.succ_ne_zero, ne_eq,
    not_false_eq_true, sub_zero]
  unfold integratedMagnitude
  push_cast
  ring

private theorem norm_integratedTerm (n : ℕ) :
    ‖integratedTerm n‖ = integratedMagnitude n := by
  rw [integratedTerm_eq_alternating, norm_mul, norm_pow]
  norm_num [Real.norm_eq_abs, abs_of_pos (integratedMagnitude_pos n)]

private theorem summable_integratedTerm :
    Summable integratedTerm := by
  apply Summable.of_norm
  simpa only [norm_integratedTerm] using summable_integratedMagnitude

private theorem summable_integral_norm_binomialTerm :
    Summable
      (fun n : ℕ => ∫ x in (0 : ℝ)..1, ‖binomialTerm n x‖) := by
  apply summable_integratedMagnitude.congr
  intro n
  exact (integral_norm_binomialTerm n).symm

private theorem intervalIntegral_tsum_binomialTerm :
    (∫ x in (0 : ℝ)..1, ∑' n : ℕ, binomialTerm n x) =
      ∑' n : ℕ, ∫ x in (0 : ℝ)..1, binomialTerm n x := by
  have hint (n : ℕ) :
      MeasureTheory.IntegrableOn (binomialTerm n) (Set.Ioc (0 : ℝ) 1) :=
    (binomialTerm_intervalIntegrable n).1
  have hnorm :
      Summable (fun n : ℕ =>
        ∫ x in Set.Ioc (0 : ℝ) 1, ‖binomialTerm n x‖) := by
    simpa only [intervalIntegral.integral_of_le
      (by norm_num : (0 : ℝ) ≤ 1)] using
        summable_integral_norm_binomialTerm
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [← MeasureTheory.integral_tsum_of_summable_integral_norm hint hnorm]
  apply tsum_congr
  intro n
  exact (intervalIntegral.integral_of_le
    (μ := MeasureTheory.volume) (f := binomialTerm n)
    (by norm_num : (0 : ℝ) ≤ 1)).symm

private theorem binomialTerm_hasSum (x : ℝ) (hx : |x| < 1) :
    HasSum (fun n : ℕ => binomialTerm n x)
      (Real.rpow (1 + x ^ 4) (-(1 / 2 : ℝ))) := by
  have hz : x ^ 4 ∈ Metric.eball (0 : ℝ) 1 := by
    simp only [Metric.mem_eball, edist_dist, dist_zero_right,
      ENNReal.ofReal_lt_one]
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_lt_one₀ (abs_nonneg x) hx (by omega)
  have h :=
    (Real.one_add_rpow_hasFPowerSeriesOnBall_zero
      (a := -(1 / 2 : ℝ))).hasSum hz
  have hfun :
      (fun n : ℕ =>
        (binomialSeries ℝ (-(1 / 2 : ℝ)) n)
          (fun _ => x ^ 4)) =
        fun n : ℕ => binomialTerm n x := by
    funext n
    rw [binomialSeries_apply]
    simp only [smul_eq_mul]
    rw [show (List.ofFn (fun _ : Fin n => x ^ 4)).prod =
        (x ^ 4) ^ n by simp]
    unfold binomialTerm
    rw [← positiveHalfChoose_eq_centralCoefficient]
    unfold positiveHalfChoose
    rw [pow_mul]
    have hsign : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
      rw [← pow_add, show n + n = 2 * n by omega, pow_mul]
      norm_num
    rw [← mul_assoc, hsign, one_mul]
  rw [hfun] at h
  simpa only [zero_add] using h

private theorem targetIntegral_eq_rpowIntegral :
    targetIntegral =
      ∫ x in (0 : ℝ)..1,
        Real.rpow (1 + x ^ 4) (-1 / 2 : ℝ) := by
  apply intervalIntegral.integral_congr
  intro x _
  have hpos : 0 < 1 + x ^ 4 := by positivity
  unfold integrand
  rw [Real.sqrt_eq_rpow]
  change 1 / Real.rpow (1 + x ^ 4) (1 / 2 : ℝ) =
    Real.rpow (1 + x ^ 4) (-1 / 2 : ℝ)
  rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring]
  simpa [one_div] using
    (Real.rpow_neg hpos.le (1 / 2 : ℝ)).symm

private theorem rpowIntegral_eq_integral_tsum :
    (∫ x in (0 : ℝ)..1,
        Real.rpow (1 + x ^ 4) (-1 / 2 : ℝ)) =
      ∫ x in (0 : ℝ)..1, ∑' n : ℕ, binomialTerm n x := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume 1]
    with x hx1
  intro hx
  simp only [Set.mem_uIoc] at hx
  rcases hx with hx | hx
  · have hxlt : x < 1 := lt_of_le_of_ne hx.2 hx1
    have habs : |x| < 1 := by
      rw [abs_of_nonneg hx.1.le]
      exact hxlt
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring]
    exact (binomialTerm_hasSum x habs).tsum_eq.symm
  · exfalso
    linarith [hx.1, hx.2]

private theorem integratedTerm_hasSum_target :
    HasSum integratedTerm targetIntegral := by
  have heq : targetIntegral = ∑' n : ℕ, integratedTerm n := by
    calc
      targetIntegral =
          ∫ x in (0 : ℝ)..1,
            Real.rpow (1 + x ^ 4) (-1 / 2 : ℝ) :=
        targetIntegral_eq_rpowIntegral
      _ = ∫ x in (0 : ℝ)..1, ∑' n : ℕ, binomialTerm n x :=
        rpowIntegral_eq_integral_tsum
      _ = ∑' n : ℕ, ∫ x in (0 : ℝ)..1, binomialTerm n x :=
        intervalIntegral_tsum_binomialTerm
      _ = ∑' n : ℕ, integratedTerm n :=
        tsum_congr integral_binomialTerm
  rw [heq]
  exact summable_integratedTerm.hasSum

private theorem integrated_partial_tendsto :
    Filter.Tendsto
      (fun n => ∑ i ∈ Finset.range n,
        (-1 : ℝ) ^ i * integratedMagnitude i)
      Filter.atTop (nhds targetIntegral) := by
  have heq :
      (fun n => ∑ i ∈ Finset.range n,
        (-1 : ℝ) ^ i * integratedMagnitude i) =
      fun n => ∑ i ∈ Finset.range n, integratedTerm i := by
    funext n
    apply Finset.sum_congr rfl
    intro i hi
    exact (integratedTerm_eq_alternating i).symm
  rw [heq]
  exact integratedTerm_hasSum_target.tendsto_sum_nat

private theorem alternating_sum_range_24 :
    (∑ i ∈ Finset.range 24,
      (-1 : ℝ) ^ i * integratedMagnitude i) =
      partialIntegral := by
  unfold partialIntegral
  apply Finset.sum_congr rfl
  intro i hi
  exact (integratedTerm_eq_alternating i).symm

private theorem alternating_sum_range_26 :
    (∑ i ∈ Finset.range 26,
      (-1 : ℝ) ^ i * integratedMagnitude i) =
      partialIntegral + integratedMagnitude 24 -
        integratedMagnitude 25 := by
  rw [show 26 = 25 + 1 by norm_num, Finset.sum_range_succ,
    show 25 = 24 + 1 by norm_num, Finset.sum_range_succ,
    alternating_sum_range_24]
  norm_num <;> ring

private theorem alternating_sum_range_27 :
    (∑ i ∈ Finset.range 27,
      (-1 : ℝ) ^ i * integratedMagnitude i) =
      partialIntegral + integratedMagnitude 24 -
        integratedMagnitude 25 + integratedMagnitude 26 := by
  rw [show 27 = 26 + 1 by norm_num, Finset.sum_range_succ,
    alternating_sum_range_26]
  norm_num <;> ring

private theorem partialIntegral_bounds :
    partialIntegral < targetIntegral ∧
      targetIntegral < partialIntegral + integratedMagnitude 24 := by
  have hanti : Antitone integratedMagnitude :=
    integratedMagnitude_strictAnti.antitone
  have hlo :=
    hanti.alternating_series_le_tendsto integrated_partial_tendsto 13
  have hhi :=
    hanti.tendsto_le_alternating_series integrated_partial_tendsto 13
  norm_num [alternating_sum_range_26] at hlo
  norm_num [alternating_sum_range_27] at hhi
  have h25 :
      integratedMagnitude 25 < integratedMagnitude 24 :=
    integratedMagnitude_strictAnti (by norm_num)
  have h26 :
      integratedMagnitude 26 < integratedMagnitude 25 :=
    integratedMagnitude_strictAnti (by norm_num)
  constructor <;> linarith

theorem gap1 :
    targetIntegral =
      ∫ x in (0 : ℝ)..1,
        Real.rpow (1 + x ^ 4) (-1 / 2 : ℝ) := by
  exact targetIntegral_eq_rpowIntegral

theorem gap2 :
    (∫ x in (0 : ℝ)..1,
        Real.rpow (1 + x ^ 4) (-1 / 2 : ℝ)) =
      ∫ x in (0 : ℝ)..1, ∑' n : ℕ, binomialTerm n x := by
  exact rpowIntegral_eq_integral_tsum

theorem gap3 :
    targetIntegral =
      ∫ x in (0 : ℝ)..1, ∑' n : ℕ, binomialTerm n x := by
  exact targetIntegral_eq_rpowIntegral.trans
    rpowIntegral_eq_integral_tsum

theorem gap4 :
    targetIntegral = ∑' n : ℕ, integratedTerm n := by
  exact integratedTerm_hasSum_target.tsum_eq.symm

theorem gap5 :
    Approx targetIntegral (927 / 1000 : ℝ)
      (1 / 1000 : ℝ) := by
  have hlo : (926 / 1000 : ℝ) < partialIntegral := by
    norm_num [partialIntegral, integratedTerm, centralCoefficient,
      Finset.sum_range_succ, Nat.choose]
  have hhi :
      partialIntegral + integratedMagnitude 24 <
        (928 / 1000 : ℝ) := by
    norm_num [partialIntegral, integratedTerm, integratedMagnitude,
      centralCoefficient, Finset.sum_range_succ, Nat.choose]
  rw [Approx, abs_lt]
  rcases partialIntegral_bounds with ⟨hblo, hbhi⟩
  constructor <;> linarith

theorem gap6 :
    0 < remainder := by
  unfold remainder
  linarith [partialIntegral_bounds.1]

theorem gap7 :
    remainder < firstOmittedTerm := by
  rcases partialIntegral_bounds with ⟨hlo, hhi⟩
  unfold remainder firstOmittedTerm
  unfold integratedMagnitude at hhi
  norm_num at hhi ⊢
  linarith

theorem gap8 :
    firstOmittedTerm < (1 / 10 ^ 2 : ℝ) := by
  norm_num [firstOmittedTerm, centralCoefficient, Nat.choose]

theorem gap9 :
    (0 : ℝ) < 1 / 10 ^ 3 := by
  norm_num

end

end ProofGap.Exercise2932_8

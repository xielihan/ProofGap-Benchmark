import ProofGapLean.Prelude.Analysis
import ProofGapLean.Exercises.Exercise2922
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order

namespace ProofGap.Exercise2932_9

noncomputable section

open scoped BigOperators Interval

def logTerm (k : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ k / (k + 1 : ℕ) *
    (1 / x : ℝ) ^ (k + 1)

def integratedCorrectionTerm (k : ℕ) : ℝ :=
  let n := k + 1
  (-1 : ℝ) ^ k / ((n : ℝ) ^ 2 * (10 : ℝ) ^ n) *
    (1 - 1 / (10 : ℝ) ^ n)

def targetIntegral : ℝ :=
  ∫ x in (10 : ℝ)..100, Real.log (1 + x) / x

def baseIntegral : ℝ :=
  ∫ x in (10 : ℝ)..100, Real.log x / x

def Approx (u v ε : ℝ) : Prop :=
  |u - v| < ε

private def correctionTerm (k : ℕ) (x : ℝ) : ℝ :=
  logTerm k x / x

private theorem correctionTerm_eq (k : ℕ) (x : ℝ) :
    correctionTerm k x =
      ((-1 : ℝ) ^ k / (k + 1 : ℕ)) * (1 / x : ℝ) ^ (k + 2) := by
  simp only [correctionTerm, logTerm]
  rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
  push_cast
  ring

private theorem logTerm_hasSum (x : ℝ) (hx : |1 / x| < 1) :
    HasSum (fun k : ℕ => logTerm k x) (Real.log (1 + 1 / x)) := by
  have hs :=
    (Real.hasSum_pow_div_log_of_abs_lt_one
      (x := -(1 / x)) (by simpa only [abs_neg] using hx)).mul_left (-1 : ℝ)
  convert hs using 1
  · funext k
    simp only [logTerm]
    rw [neg_pow]
    push_cast
    ring
  · simp

private theorem integral_correctionTerm (k : ℕ) :
    (∫ x in (10 : ℝ)..100, correctionTerm k x) =
      integratedCorrectionTerm k := by
  have hz := integral_zpow
    (a := (10 : ℝ)) (b := 100) (n := -((k + 2 : ℕ) : ℤ))
    (Or.inr ⟨by omega, by norm_num [Set.mem_uIcc]⟩)
  have hexp :
      -((k + 2 : ℕ) : ℤ) + 1 = -((k + 1 : ℕ) : ℤ) := by
    omega
  rw [hexp] at hz
  simp only [zpow_neg, zpow_natCast] at hz
  have heq : correctionTerm k = fun x : ℝ =>
      ((-1 : ℝ) ^ k / (k + 1 : ℕ)) * (x ^ (k + 2))⁻¹ := by
    funext x
    rw [correctionTerm_eq]
    simp only [one_div, inv_pow]
  rw [heq, intervalIntegral.integral_const_mul, hz]
  simp only [integratedCorrectionTerm]
  dsimp
  push_cast
  rw [show -((k : ℝ) + 2) + 1 = -((k : ℝ) + 1) by ring]
  have h100 : (100 : ℝ) ^ (k + 1) =
      (10 : ℝ) ^ (k + 1) * (10 : ℝ) ^ (k + 1) := by
    rw [show (100 : ℝ) = 10 * 10 by norm_num, mul_pow]
  rw [h100]
  field_simp [show (k : ℝ) + 1 ≠ 0 by positivity,
    show (10 : ℝ) ^ (k + 1) ≠ 0 by positivity]
  ring

private theorem correctionTerm_hasSum (x : ℝ) (hx : 10 ≤ x) :
    HasSum (fun k : ℕ => correctionTerm k x)
      (Real.log (1 + x) / x - Real.log x / x) := by
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have honepos : 0 < 1 + 1 / x := by positivity
  have habs : |1 / x| < 1 := by
    rw [abs_of_pos (one_div_pos.mpr hxpos)]
    calc
      1 / x ≤ 1 / 10 := one_div_le_one_div_of_le (by norm_num) hx
      _ < 1 := by norm_num
  have hs := (logTerm_hasSum x habs).div_const x
  convert hs using 1
  have harg : x * (1 + 1 / x) = 1 + x := by
    field_simp [hx0]
    <;> ring
  have hlog := Real.log_mul hx0 (ne_of_gt honepos)
  rw [harg] at hlog
  rw [hlog]
  ring

private theorem correctionTerm_measurable (k : ℕ) :
    MeasureTheory.AEStronglyMeasurable (correctionTerm k)
      (MeasureTheory.volume.restrict (Set.uIoc (10 : ℝ) 100)) := by
  apply Measurable.aestronglyMeasurable
  unfold correctionTerm logTerm
  measurability

private theorem correctionTerm_norm_le
    (k : ℕ) (x : ℝ) (hx : x ∈ Set.uIcc (10 : ℝ) 100) :
    ‖correctionTerm k x‖ ≤ (1 / 10 : ℝ) ^ (k + 2) := by
  rw [Set.uIcc_of_le (by norm_num : (10 : ℝ) ≤ 100)] at hx
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx.1
  have hq : ‖(1 / x : ℝ)‖ ≤ (1 / 10 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hxpos)]
    exact one_div_le_one_div_of_le (by norm_num) hx.1
  have hc : ‖((-1 : ℝ) ^ k / (k + 1 : ℕ))‖ ≤ 1 := by
    rw [norm_div, norm_pow]
    simp only [norm_neg, norm_one, one_pow]
    rw [Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < (k + 1 : ℕ))]
    have hden : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by norm_num
    have h := one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) hden
    simpa only [one_div, inv_one] using h
  rw [correctionTerm_eq, norm_mul, norm_pow]
  calc
    ‖(-1 : ℝ) ^ k / ↑(k + 1)‖ * ‖1 / x‖ ^ (k + 2) ≤
        1 * (1 / 10 : ℝ) ^ (k + 2) := by gcongr
    _ = (1 / 10 : ℝ) ^ (k + 2) := one_mul _

private theorem summable_correctionMajorant :
    Summable (fun k : ℕ => (1 / 10 : ℝ) ^ (k + 2)) := by
  have h : Summable (fun k : ℕ => (1 / 10 : ℝ) ^ k) :=
    summable_geometric_of_norm_lt_one
      (by norm_num [Real.norm_eq_abs] : ‖(1 / 10 : ℝ)‖ < 1)
  apply (h.mul_left ((1 / 10 : ℝ) ^ 2)).congr
  intro k
  rw [pow_add]
  ring

private theorem targetIntegrand_intervalIntegrable :
    IntervalIntegrable (fun x : ℝ => Real.log (1 + x) / x)
      MeasureTheory.volume 10 100 := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  rw [Set.uIcc_of_le (by norm_num : (10 : ℝ) ≤ 100)] at hx
  have hx0 : x ≠ 0 := by nlinarith [hx.1]
  have harg0 : 1 + x ≠ 0 := by nlinarith [hx.1]
  exact (((Real.continuousAt_log harg0).comp
    (continuousAt_const.add continuousAt_id)).div continuousAt_id hx0).continuousWithinAt

private theorem baseIntegrand_intervalIntegrable :
    IntervalIntegrable (fun x : ℝ => Real.log x / x)
      MeasureTheory.volume 10 100 := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  rw [Set.uIcc_of_le (by norm_num : (10 : ℝ) ≤ 100)] at hx
  have hx0 : x ≠ 0 := by nlinarith [hx.1]
  exact ((Real.continuousAt_log hx0).div continuousAt_id hx0).continuousWithinAt

private theorem correctionIntegral_hasSum :
    HasSum
      (fun k : ℕ => ∫ x in (10 : ℝ)..100, correctionTerm k x)
      (targetIntegral - baseIntegral) := by
  have hs := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := (10 : ℝ)) (b := 100)
    (f := fun x : ℝ => Real.log (1 + x) / x - Real.log x / x)
    (F := correctionTerm)
    (fun k (_ : ℝ) => (1 / 10 : ℝ) ^ (k + 2))
    correctionTerm_measurable
    (by
      intro k
      filter_upwards with x hx
      exact correctionTerm_norm_le k x (Set.uIoc_subset_uIcc hx))
    (by
      filter_upwards with x hx
      exact summable_correctionMajorant)
    intervalIntegrable_const
    (by
      filter_upwards with x hx
      rw [Set.uIoc_of_le (by norm_num : (10 : ℝ) ≤ 100)] at hx
      exact correctionTerm_hasSum x hx.1.le)
  convert hs using 1
  rw [targetIntegral, baseIntegral,
    intervalIntegral.integral_sub targetIntegrand_intervalIntegrable
      baseIntegrand_intervalIntegrable]

private theorem integratedCorrection_hasSum :
    HasSum integratedCorrectionTerm (targetIntegral - baseIntegral) := by
  apply correctionIntegral_hasSum.congr_fun
  intro k
  exact (integral_correctionTerm k).symm

private theorem baseIntegral_eq :
    baseIntegral = (3 / 2 : ℝ) * Real.log 10 ^ 2 := by
  have hderiv : ∀ x ∈ Set.uIcc (10 : ℝ) 100,
      HasDerivAt (fun y : ℝ => Real.log y ^ 2 / 2)
        (Real.log x / x) x := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (10 : ℝ) ≤ 100)] at hx
    have hx0 : x ≠ 0 := by nlinarith [hx.1]
    have hd := ((Real.hasDerivAt_log hx0).pow 2).div_const 2
    convert hd using 1 <;> ring
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (10 : ℝ)) (b := 100) hderiv baseIntegrand_intervalIntegrable
  have hlog100 : Real.log (100 : ℝ) = 2 * Real.log 10 := by
    rw [show (100 : ℝ) = 10 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  calc
    baseIntegral = Real.log 100 ^ 2 / 2 - Real.log 10 ^ 2 / 2 := by
      simpa only [baseIntegral] using hint
    _ = (3 / 2 : ℝ) * Real.log 10 ^ 2 := by
      rw [hlog100]
      ring

private theorem logTen_bounds :
    (230257 / 100000 : ℝ) < Real.log 10 ∧
      Real.log 10 < (23026 / 10000 : ℝ) := by
  have h125 := ProofGap.Exercise2922.gap29
  unfold ProofGap.Exercise2922.Approx at h125
  rw [abs_lt] at h125
  have hlog : Real.log (10 : ℝ) =
      3 * Real.log 2 + Real.log (125 / 100 : ℝ) := by
    rw [show (10 : ℝ) = 2 ^ (3 : ℕ) * (125 / 100 : ℝ) by norm_num,
      Real.log_mul (pow_ne_zero 3 (by norm_num : (2 : ℝ) ≠ 0))
        (by norm_num : (125 / 100 : ℝ) ≠ 0),
      Real.log_pow]
    norm_num
  rw [hlog]
  constructor <;>
    nlinarith [Real.log_two_gt_d9, Real.log_two_lt_d9]

private theorem integratedCorrectionTerm_abs_le (k : ℕ) :
    |integratedCorrectionTerm k| ≤ (1 / 10 : ℝ) ^ (k + 1) := by
  have hn : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by norm_num
  have hpow : (1 : ℝ) ≤ 10 ^ (k + 1) := one_le_pow₀ (by norm_num)
  have hinv_nonneg : (0 : ℝ) ≤ 1 / 10 ^ (k + 1) := by positivity
  have hinv_le : (1 : ℝ) / 10 ^ (k + 1) ≤ 1 := by
    exact (div_le_one (by positivity)).2 hpow
  have hfactor_nonneg : (0 : ℝ) ≤ 1 - 1 / 10 ^ (k + 1) :=
    sub_nonneg.mpr hinv_le
  have hfactor_le : (1 : ℝ) - 1 / 10 ^ (k + 1) ≤ 1 := by linarith
  have hden : (10 : ℝ) ^ (k + 1) ≤
      ((k + 1 : ℕ) : ℝ) ^ 2 * 10 ^ (k + 1) := by
    have hnsq : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hnsq
      (show (0 : ℝ) ≤ 10 ^ (k + 1) by positivity)
    simpa only [one_mul] using hm
  unfold integratedCorrectionTerm
  dsimp
  rw [abs_mul, abs_div, abs_pow]
  norm_num only [abs_neg, abs_one, one_pow]
  rw [abs_of_pos (by positivity : (0 : ℝ) < (((k + 1 : ℕ) : ℝ) ^ 2 * 10 ^ (k + 1))),
    abs_of_nonneg hfactor_nonneg]
  rw [one_div_pow]
  calc
    1 / (((k + 1 : ℕ) : ℝ) ^ 2 * 10 ^ (k + 1)) *
          (1 - 1 / 10 ^ (k + 1)) ≤
        1 / (((k + 1 : ℕ) : ℝ) ^ 2 * 10 ^ (k + 1)) * 1 := by
      gcongr
    _ ≤ 1 / 10 ^ (k + 1) := by
      rw [mul_one]
      exact one_div_le_one_div_of_le (by positivity) hden

private theorem integratedCorrection_summable :
    Summable integratedCorrectionTerm := integratedCorrection_hasSum.summable

private theorem correctionTail_abs_le :
    |∑' k : ℕ, integratedCorrectionTerm (k + 3)| ≤ (1 / 9000 : ℝ) := by
  have hmajorant : Summable (fun k : ℕ => (1 / 10 : ℝ) ^ (k + 4)) := by
    have h : Summable (fun k : ℕ => (1 / 10 : ℝ) ^ k) :=
      summable_geometric_of_norm_lt_one
        (by norm_num [Real.norm_eq_abs] : ‖(1 / 10 : ℝ)‖ < 1)
    apply (h.mul_left ((1 / 10 : ℝ) ^ 4)).congr
    intro k
    rw [pow_add]
    ring
  have hnorm : Summable (fun k : ℕ => ‖integratedCorrectionTerm (k + 3)‖) := by
    apply Summable.of_nonneg_of_le (fun k => norm_nonneg _)
      (fun k => ?_) hmajorant
    rw [Real.norm_eq_abs]
    convert integratedCorrectionTerm_abs_le (k + 3) using 1 <;> omega
  calc
    |∑' k : ℕ, integratedCorrectionTerm (k + 3)| ≤
        ∑' k : ℕ, ‖integratedCorrectionTerm (k + 3)‖ := by
      simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' k : ℕ, (1 / 10 : ℝ) ^ (k + 4) :=
      Summable.tsum_le_tsum
        (fun k => by
          rw [Real.norm_eq_abs]
          convert integratedCorrectionTerm_abs_le (k + 3) using 1 <;> omega)
        hnorm hmajorant
    _ = (1 / 9000 : ℝ) := by
      simp_rw [pow_add]
      rw [tsum_mul_right, tsum_geometric_of_norm_lt_one
        (by norm_num [Real.norm_eq_abs] : ‖(1 / 10 : ℝ)‖ < 1)]
      norm_num

private theorem correctionSeries_bounds :
    (∑ k ∈ Finset.range 3, integratedCorrectionTerm k) - (1 / 9000 : ℝ) ≤
        ∑' k : ℕ, integratedCorrectionTerm k ∧
      (∑' k : ℕ, integratedCorrectionTerm k) ≤
        (∑ k ∈ Finset.range 3, integratedCorrectionTerm k) + (1 / 9000 : ℝ) := by
  have hsplit := integratedCorrection_summable.sum_add_tsum_nat_add 3
  have htail := correctionTail_abs_le
  rw [abs_le] at htail
  constructor <;> linarith [hsplit]

theorem gap1 :
    ∀ x : ℝ, 10 ≤ x → x ≤ 100 →
      Real.log (1 + x) =
        Real.log (x * (1 + 1 / x)) := by
  intro x hx _
  congr 1
  have hx0 : x ≠ 0 := by positivity
  field_simp [hx0]
  <;> ring

theorem gap2 :
    ∀ x : ℝ, 10 ≤ x → x ≤ 100 →
      Real.log (x * (1 + 1 / x)) =
        Real.log x + ∑' k : ℕ, logTerm k x := by
  intro x hx _
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have honepos : 0 < 1 + 1 / x := by positivity
  rw [Real.log_mul hx0 (ne_of_gt honepos)]
  congr 1
  exact (logTerm_hasSum x (by
    rw [abs_of_pos (one_div_pos.mpr hxpos)]
    calc
      1 / x ≤ 1 / 10 := one_div_le_one_div_of_le (by norm_num) hx
      _ < 1 := by norm_num)).tsum_eq.symm

theorem gap3 :
    ∀ x : ℝ, 10 ≤ x → x ≤ 100 →
      Real.log (1 + x) =
        Real.log x + ∑' k : ℕ, logTerm k x := by
  intro x hx hX
  exact (gap1 x hx hX).trans (gap2 x hx hX)

theorem gap4 :
    targetIntegral =
      baseIntegral + ∑' k : ℕ, integratedCorrectionTerm k := by
  rw [integratedCorrection_hasSum.tsum_eq]
  ring

theorem gap5 :
    targetIntegral =
      (3 / 2 : ℝ) * Real.log 10 ^ 2 +
        ∑' k : ℕ, integratedCorrectionTerm k := by
  rw [gap4, baseIntegral_eq]

theorem gap6 :
    Approx targetIntegral (8041 / 1000 : ℝ)
      (1 / 1000 : ℝ) := by
  rcases logTen_bounds with ⟨hlogLower, hlogUpper⟩
  rcases correctionSeries_bounds with ⟨hseriesLower, hseriesUpper⟩
  norm_num [integratedCorrectionTerm, Finset.sum_range_succ] at hseriesLower hseriesUpper
  have hlogPos : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have hlowerProduct :
      0 < (Real.log 10 - (230257 / 100000 : ℝ)) *
        (Real.log 10 + (230257 / 100000 : ℝ)) := by
    apply mul_pos (sub_pos.mpr hlogLower)
    nlinarith
  have hupperProduct :
      0 < ((23026 / 10000 : ℝ) - Real.log 10) *
        ((23026 / 10000 : ℝ) + Real.log 10) := by
    apply mul_pos (sub_pos.mpr hlogUpper)
    nlinarith
  rw [Approx, abs_lt, gap5]
  simp only [integratedCorrectionTerm]
  push_cast at hseriesLower hseriesUpper ⊢
  simp only [one_div] at hseriesLower hseriesUpper ⊢
  constructor <;> nlinarith

end

end ProofGap.Exercise2932_9

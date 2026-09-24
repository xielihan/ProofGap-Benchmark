import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise2372
noncomputable section

open Filter MeasureTheory
open scoped Interval

def integrand (x : ℝ) : ℝ := Real.log x / (1 - x ^ 2)

private theorem continuousOn_integrand_unit :
    ContinuousOn integrand (Set.Ioo (0 : ℝ) 1) := by
  intro x hx
  have hx0 : 0 < x := hx.1
  have hx1 : x < 1 := hx.2
  have hden : 1 - x ^ 2 ≠ 0 := by
    have hx2 : x ^ 2 < 1 := by nlinarith
    linarith
  unfold integrand
  exact ((Real.continuousAt_log hx0.ne').div
    (continuousAt_const.sub (continuousAt_id.pow 2)) hden).continuousWithinAt

private theorem locallyIntegrableOn_integrand_unit :
    LocallyIntegrableOn integrand (Set.Ioo (0 : ℝ) 1) :=
  continuousOn_integrand_unit.locallyIntegrableOn measurableSet_Ioo

private theorem zero_scaled_tendsto :
    Tendsto (fun x => Real.sqrt x * integrand x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hnum :
      Tendsto
        (fun x : ℝ => Real.log x * x ^ (1 / 2 : ℝ))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    tendsto_log_mul_rpow_nhdsGT_zero (by norm_num)
  have hx :
      Tendsto (fun x : ℝ => x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hden :
      Tendsto (fun x : ℝ => 1 - x ^ 2)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    convert tendsto_const_nhds.sub (hx.pow 2) using 1 <;> norm_num
  have hnum' :
      Tendsto (fun x : ℝ => Real.sqrt x * Real.log x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa only [Real.sqrt_eq_rpow, mul_comm] using hnum
  have hquot :=
    hnum'.div hden (by norm_num : (1 : ℝ) ≠ 0)
  convert hquot using 1
  · funext x
    unfold integrand
    simp only [Pi.div_apply]
    ring
  · norm_num

private theorem one_scaled_tendsto :
    Tendsto (fun x => Real.sqrt (1 - x) * integrand x)
      (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := by
  have hslope :
      Tendsto (fun x : ℝ => Real.log x / (x - 1))
        (nhdsWithin 1 (Set.Iio 1)) (nhds 1) := by
    have h :=
      (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto_slope
    have hleft :=
      h.mono_left (nhdsLT_le_nhdsNE (1 : ℝ))
    have hleft' :
        Tendsto (slope Real.log 1)
          (nhdsWithin 1 (Set.Iio 1)) (nhds 1) := by
      simpa using hleft
    apply hleft'.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [slope_def_field]
    simp [div_eq_mul_inv, mul_comm]
  have hx :
      Tendsto (fun x : ℝ => x)
        (nhdsWithin 1 (Set.Iio 1)) (nhds 1) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have ht :
      Tendsto (fun x : ℝ => 1 - x)
        (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := by
    convert tendsto_const_nhds.sub hx using 1 <;> norm_num
  have hsqrt :
      Tendsto (fun x : ℝ => Real.sqrt (1 - x))
        (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := by
    simpa using Real.continuous_sqrt.continuousAt.tendsto.comp ht
  have hplus :
      Tendsto (fun x : ℝ => 1 + x)
        (nhdsWithin 1 (Set.Iio 1)) (nhds 2) := by
    convert tendsto_const_nhds.add hx using 1 <;> norm_num
  have hfactor :
      Tendsto (fun x : ℝ => -Real.sqrt (1 - x) / (1 + x))
        (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := by
    convert hsqrt.neg.div hplus (by norm_num : (2 : ℝ) ≠ 0) using 1 <;>
      norm_num
  have hprod :
      Tendsto
        (fun x : ℝ =>
          (Real.log x / (x - 1)) *
            (-Real.sqrt (1 - x) / (1 + x)))
        (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := by
    simpa using hslope.mul hfactor
  apply hprod.congr'
  have hxpos :
      ∀ᶠ x in
        (nhdsWithin (1 : ℝ) (Set.Iio 1) : Filter ℝ), (0 : ℝ) < x :=
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono
      (nhdsWithin_le_nhds :
        nhdsWithin (1 : ℝ) (Set.Iio 1) ≤ nhds 1)
  filter_upwards [self_mem_nhdsWithin, hxpos] with x hxlt hx0
  have hx1 : x < 1 := hxlt
  have hxne : x - 1 ≠ 0 := sub_ne_zero.mpr hxlt.ne
  have hplusne : 1 + x ≠ 0 := by linarith
  have hden : 1 - x ^ 2 ≠ 0 := by
    have hx2 : x ^ 2 < 1 := by nlinarith
    linarith
  unfold integrand
  field_simp [hxne, hplusne, hden]
  ring

private theorem intervalIntegrable_zero_half :
    IntervalIntegrable integrand volume 0 (1 / 2 : ℝ) := by
  have hlog :
      IntervalIntegrable Real.log volume 0 (1 / 2 : ℝ) :=
    intervalIntegral.intervalIntegrable_log'
  have hcontinuous :
      ContinuousOn (fun x : ℝ => 1 / (1 - x ^ 2))
        [[(0 : ℝ), (1 / 2 : ℝ)]] := by
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) (1 / 2 : ℝ) := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hx
    have hx0 : 0 ≤ x := hx'.1
    have hxhalf : x ≤ (1 / 2 : ℝ) := hx'.2
    have hden : 1 - x ^ 2 ≠ 0 := by
      have hx2 : x ^ 2 < 1 := by nlinarith
      linarith
    exact
      (continuousAt_const.div
        (continuousAt_const.sub (continuousAt_id.pow 2)) hden).continuousWithinAt
  have h :=
    hlog.mul_continuousOn hcontinuous
  simpa [integrand, div_eq_mul_inv] using h

private theorem stronglyMeasurableAtFilter_integrand_one :
    StronglyMeasurableAtFilter integrand
      (nhdsWithin 1 (Set.Iio 1)) :=
  AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem
    (continuousOn_integrand_unit.aestronglyMeasurable measurableSet_Ioo)
    (Ioo_mem_nhdsLT zero_lt_one)

private theorem integrableAtFilter_integrand_one :
    IntegrableAtFilter integrand (nhdsWithin 1 (Set.Iio 1)) := by
  let m : ℝ → ℝ :=
    fun x => (1 - x) ^ (-(1 / 2 : ℝ))
  have hbound :
      ∀ᶠ x in nhdsWithin 1 (Set.Iio 1),
        ‖Real.sqrt (1 - x) * integrand x‖ ≤ 1 := by
    filter_upwards [
      one_scaled_tendsto.eventually
        (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one)] with x hx
    have hx' : ‖Real.sqrt (1 - x) * integrand x‖ < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hx
    exact hx'.le
  have hO : integrand =O[nhdsWithin 1 (Set.Iio 1)] m := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [hbound, self_mem_nhdsWithin] with x hb hx
    have ht : 0 < 1 - x := sub_pos.mpr hx
    have hprod :
        Real.sqrt (1 - x) * m x = 1 := by
      unfold m
      rw [Real.sqrt_eq_rpow]
      calc
        (1 - x) ^ (1 / 2 : ℝ) *
            (1 - x) ^ (-(1 / 2 : ℝ)) =
            (1 - x) ^ ((1 / 2 : ℝ) + -(1 / 2 : ℝ)) :=
          (Real.rpow_add ht (1 / 2 : ℝ) (-(1 / 2 : ℝ))).symm
        _ = (1 - x) ^ (0 : ℝ) := by congr 1 <;> ring
        _ = 1 := Real.rpow_zero _
    have heq :
        integrand x =
          (Real.sqrt (1 - x) * integrand x) * m x := by
      calc
        integrand x = 1 * integrand x := by ring
        _ = (Real.sqrt (1 - x) * m x) * integrand x := by
          rw [hprod]
        _ = (Real.sqrt (1 - x) * integrand x) * m x := by ring
    rw [heq, norm_mul, one_mul]
    nlinarith [norm_nonneg (m x)]
  have hbase :
      IntegrableOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ)))
        (Set.Ioo 0 (1 / 2)) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff
      (by norm_num : (0 : ℝ) < 1 / 2)).2 (by norm_num)
  have hbaseInterval :
      IntervalIntegrable (fun t : ℝ => t ^ (-(1 / 2 : ℝ)))
        volume 0 (1 / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le
      (by norm_num : (0 : ℝ) ≤ 1 / 2)).2 hbase
  have hmInterval :
      IntervalIntegrable m volume (1 / 2) 1 := by
    unfold m
    convert (hbaseInterval.comp_sub_left (1 : ℝ)).symm using 1 <;>
      norm_num
  have hm :
      IntegrableOn m (Set.Ioo (1 / 2) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le
      (by norm_num : (1 / 2 : ℝ) ≤ 1)).1 hmInterval
  have hmFilter :
      IntegrableAtFilter m (nhdsWithin 1 (Set.Iio 1)) :=
    ⟨Set.Ioo (1 / 2) 1, Ioo_mem_nhdsLT (by norm_num), hm⟩
  exact hO.integrableAtFilter
    stronglyMeasurableAtFilter_integrand_one hmFilter

private theorem integrableOn_upper_half_one :
    IntegrableOn integrand (Set.Ioo (1 / 2 : ℝ) 1) := by
  rcases integrableAtFilter_integrand_one with ⟨u, hu, hint⟩
  obtain ⟨b, hb, hsub⟩ :=
    mem_nhdsLT_iff_exists_Ioo_subset.mp hu
  have hlarge : IntegrableOn integrand (Set.Ioo b 1) :=
    hint.mono_set hsub
  by_cases hbhalf : b ≤ (1 / 2 : ℝ)
  · exact hlarge.mono_set fun x hx =>
      ⟨lt_of_le_of_lt hbhalf hx.1, hx.2⟩
  · have hhalfb : (1 / 2 : ℝ) ≤ b := le_of_not_ge hbhalf
    have hmidIcc :
        IntegrableOn integrand (Set.Icc (1 / 2 : ℝ) b) :=
      locallyIntegrableOn_integrand_unit.integrableOn_compact_subset
        (fun x hx => ⟨by linarith [hx.1], lt_of_le_of_lt hx.2 hb⟩)
        isCompact_Icc
    have hmid :
        IntegrableOn integrand (Set.Ioc (1 / 2 : ℝ) b) :=
      hmidIcc.mono_set Set.Ioc_subset_Icc_self
    rw [← Set.Ioc_union_Ioo_eq_Ioo hhalfb hb, integrableOn_union]
    exact ⟨hmid, hlarge⟩

private theorem intervalIntegrable_unit :
    IntervalIntegrable integrand volume 0 1 := by
  have hzero :
      IntegrableOn integrand (Set.Ioc (0 : ℝ) (1 / 2)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by norm_num : (0 : ℝ) ≤ 1 / 2)).1 intervalIntegrable_zero_half
  have hfull : IntegrableOn integrand (Set.Ioo (0 : ℝ) 1) := by
    rw [← Set.Ioc_union_Ioo_eq_Ioo
        (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1),
      integrableOn_union]
    exact ⟨hzero, integrableOn_upper_half_one⟩
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le
    (by norm_num : (0 : ℝ) ≤ 1)).2 hfull

theorem gap1 :
    (∫ x in (0 : ℝ)..1, integrand x) =
      (∫ x in (0 : ℝ)..(1 / 2), integrand x) +
        ∫ x in (1 / 2 : ℝ)..1, integrand x := by
  have hmem : (1 / 2 : ℝ) ∈ [[(0 : ℝ), 1]] := by
    norm_num [Set.uIcc_of_le]
  have hsplit :
      IntervalIntegrable integrand volume 0 (1 / 2) ∧
        IntervalIntegrable integrand volume (1 / 2) 1 :=
    (IntervalIntegrable.trans_iff hmem).1 intervalIntegrable_unit
  exact
    (intervalIntegral.integral_add_adjacent_intervals
      hsplit.1 hsplit.2).symm

theorem gap2 :
    Tendsto (fun x => Real.sqrt x * integrand x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  exact zero_scaled_tendsto

theorem gap3 :
    ∃ L : ℝ,
      Tendsto (fun a => ∫ x in a..(1 / 2 : ℝ), integrand x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
  have hIcc :
      IntegrableOn integrand (Set.Icc (0 : ℝ) (1 / 2)) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le
      (by norm_num : (0 : ℝ) ≤ 1 / 2)).1 intervalIntegrable_zero_half
  have hcont :
      ContinuousOn
        (fun a => ∫ x in a..(1 / 2 : ℝ), integrand x)
        [[(0 : ℝ), (1 / 2 : ℝ)]] :=
    intervalIntegral.continuousOn_primitive_interval_left
      (by simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hIcc)
  have hle :
      nhdsWithin 0 (Set.Ioi 0) ≤
        nhdsWithin 0 [[(0 : ℝ), (1 / 2 : ℝ)]] := by
    rw [nhdsWithin_le_iff]
    filter_upwards [
      self_mem_nhdsWithin,
      nhdsWithin_le_nhds
        (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with x hx hxhalf
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    exact ⟨hx.le, hxhalf⟩
  refine ⟨∫ x in (0 : ℝ)..(1 / 2), integrand x, ?_⟩
  exact (hcont 0 Set.left_mem_uIcc).tendsto.mono_left hle

theorem gap4 :
    Tendsto (fun x => Real.sqrt (1 - x) * integrand x)
      (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := by
  exact one_scaled_tendsto

theorem gap5 :
    ∃ L : ℝ,
      Tendsto (fun b => ∫ x in (1 / 2 : ℝ)..b, integrand x)
        (nhdsWithin 1 (Set.Iio 1)) (nhds L) := by
  have hmem : (1 / 2 : ℝ) ∈ [[(0 : ℝ), 1]] := by
    norm_num [Set.uIcc_of_le]
  have hhalfOne :
      IntervalIntegrable integrand volume (1 / 2) 1 :=
    ((IntervalIntegrable.trans_iff hmem).1 intervalIntegrable_unit).2
  have hIcc :
      IntegrableOn integrand (Set.Icc (1 / 2 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le
      (by norm_num : (1 / 2 : ℝ) ≤ 1)).1 hhalfOne
  have hcont :
      ContinuousOn
        (fun b => ∫ x in (1 / 2 : ℝ)..b, integrand x)
        [[(1 / 2 : ℝ), 1]] :=
    intervalIntegral.continuousOn_primitive_interval
      (by
        rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)]
        exact hIcc)
  have hle :
      nhdsWithin 1 (Set.Iio 1) ≤
        nhdsWithin 1 [[(1 / 2 : ℝ), 1]] := by
    rw [nhdsWithin_le_iff]
    filter_upwards [
      self_mem_nhdsWithin,
      nhdsWithin_le_nhds
        (Ici_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))] with x hx hxhalf
    rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)]
    exact ⟨hxhalf, hx.le⟩
  refine ⟨∫ x in (1 / 2 : ℝ)..1, integrand x, ?_⟩
  exact (hcont 1 Set.right_mem_uIcc).tendsto.mono_left hle

theorem gap6 :
    ∃ L : ℝ,
      Tendsto (fun b => ∫ x in (0 : ℝ)..b, integrand x)
        (nhdsWithin 1 (Set.Iio 1)) (nhds L) := by
  have hIcc :
      IntegrableOn integrand (Set.Icc (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le
      (by norm_num : (0 : ℝ) ≤ 1)).1 intervalIntegrable_unit
  have hcont :
      ContinuousOn
        (fun b => ∫ x in (0 : ℝ)..b, integrand x)
        [[(0 : ℝ), 1]] :=
    intervalIntegral.continuousOn_primitive_interval
      (by simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hIcc)
  have hle :
      nhdsWithin 1 (Set.Iio 1) ≤
        nhdsWithin 1 [[(0 : ℝ), 1]] := by
    rw [nhdsWithin_le_iff]
    filter_upwards [
      self_mem_nhdsWithin,
      nhdsWithin_le_nhds
        (Ici_mem_nhds (by norm_num : (0 : ℝ) < 1))] with x hx hx0
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ⟨hx0, hx.le⟩
  refine ⟨∫ x in (0 : ℝ)..1, integrand x, ?_⟩
  exact (hcont 1 Set.right_mem_uIcc).tendsto.mono_left hle

end
end ProofGap.Exercise2372

import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Defs.Filter
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise2393
noncomputable section

open Filter Set
open scoped Interval

def integrand (x : ℝ) : ℝ := 1 / (x * Real.log x)

def pvTrunc (ε : ℝ) : ℝ :=
  (∫ x in (1 / 2 : ℝ)..(1 - ε), integrand x) +
    ∫ x in (1 + ε)..2, integrand x

def logExpression (ε : ℝ) : ℝ :=
  Real.log |Real.log (1 - ε)| - Real.log (Real.log 2) +
    Real.log (Real.log 2) - Real.log |Real.log (1 + ε)|

private theorem tendsto_log_ratio :
    Tendsto (fun ε : ℝ => Real.log (1 - ε) / Real.log (1 + ε))
      (nhdsWithin 0 (Ioi 0)) (nhds (-1)) := by
  have hm : HasDerivAt (fun ε : ℝ => Real.log (1 - ε)) (-1) 0 := by
    have hi : HasDerivAt (fun ε : ℝ => 1 - ε) (-1) 0 := by
      convert
        ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (hasDerivAt_id 0)) using 1 <;>
        norm_num
    convert hi.log (by norm_num : (1 - (0 : ℝ)) ≠ 0) using 1 <;>
      norm_num
  have hp : HasDerivAt (fun ε : ℝ => Real.log (1 + ε)) 1 0 := by
    have hi : HasDerivAt (fun ε : ℝ => 1 + ε) 1 0 := by
      convert
        ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).add (hasDerivAt_id 0)) using 1 <;>
        norm_num
    convert hi.log (by norm_num : (1 + (0 : ℝ)) ≠ 0) using 1 <;>
      norm_num
  have hfilter :
      nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhdsWithin 0 ({0} : Set ℝ)ᶜ := by
    apply nhdsWithin_mono
    intro x hx
    simpa only [mem_compl_iff, mem_singleton_iff] using ne_of_gt hx
  have hm' :
      Tendsto (fun ε : ℝ => Real.log (1 - ε) / ε)
        (nhdsWithin 0 (Ioi 0)) (nhds (-1)) := by
    have hs := ((hasDerivAt_iff_tendsto_slope).1 hm).mono_left hfilter
    change Tendsto
      (fun ε : ℝ => (ε - 0)⁻¹ *
        (Real.log (1 - ε) - Real.log (1 - 0)))
      (nhdsWithin 0 (Ioi 0)) (nhds (-1)) at hs
    simpa [Real.log_one, div_eq_mul_inv, mul_comm] using hs
  have hp' :
      Tendsto (fun ε : ℝ => Real.log (1 + ε) / ε)
        (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
    have hs := ((hasDerivAt_iff_tendsto_slope).1 hp).mono_left hfilter
    change Tendsto
      (fun ε : ℝ => (ε - 0)⁻¹ *
        (Real.log (1 + ε) - Real.log (1 + 0)))
      (nhdsWithin 0 (Ioi 0)) (nhds 1) at hs
    simpa [Real.log_one, div_eq_mul_inv, mul_comm] using hs
  have hquot := hm'.div hp' (by norm_num : (1 : ℝ) ≠ 0)
  have heq :
      (fun ε : ℝ => Real.log (1 - ε) / Real.log (1 + ε)) =ᶠ[
        nhdsWithin 0 (Ioi 0)]
      (fun ε : ℝ =>
        (Real.log (1 - ε) / ε) / (Real.log (1 + ε) / ε)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hεpos : 0 < ε := hε
    have hε0 : ε ≠ 0 := ne_of_gt hεpos
    have hplus : (1 : ℝ) < 1 + ε := by linarith
    have hlog : Real.log (1 + ε) ≠ 0 :=
      ne_of_gt (Real.log_pos hplus)
    field_simp [hε0, hlog]
  simpa using hquot.congr' heq.symm

theorem gap1 (ε : ℝ) (hε : ε ∈ Ioo 0 (1 / 2 : ℝ)) :
    pvTrunc ε = logExpression ε := by
  have hab : (1 / 2 : ℝ) ≤ 1 - ε := by linarith [hε.2]
  have hcd : 1 + ε ≤ (2 : ℝ) := by linarith [hε.2]
  have hleftDeriv :
      ∀ x ∈ [[(1 / 2 : ℝ), 1 - ε]],
        HasDerivAt (fun y : ℝ => Real.log (-Real.log y)) (integrand x) x := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    have hx0 : 0 < x := by linarith [hx.1]
    have hx1 : x < 1 := by linarith [hx.2, hε.1]
    have hlogneg : Real.log x < 0 := Real.log_neg hx0 hx1
    have hdinner := (Real.hasDerivAt_log (ne_of_gt hx0)).neg
    change HasDerivAt (fun y : ℝ => -Real.log y) (-x⁻¹) x at hdinner
    have hd :
        HasDerivAt (fun y : ℝ => Real.log (-Real.log y))
          ((-x⁻¹) / (-Real.log x)) x :=
      hdinner.log (ne_of_gt (neg_pos.mpr hlogneg))
    have hderiv : (-x⁻¹) / (-Real.log x) = integrand x := by
      unfold integrand
      field_simp [ne_of_gt hx0, ne_of_lt hlogneg]
    rw [← hderiv]
    exact hd
  have hleftCont :
      ContinuousOn integrand [[(1 / 2 : ℝ), 1 - ε]] := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    have hx0 : 0 < x := by linarith [hx.1]
    have hx1 : x < 1 := by linarith [hx.2, hε.1]
    have hlogneg : Real.log x < 0 := Real.log_neg hx0 hx1
    have hden : x * Real.log x ≠ 0 :=
      mul_ne_zero (ne_of_gt hx0) (ne_of_lt hlogneg)
    unfold integrand
    exact
      (continuousAt_const.div
        (continuousAt_id.mul (Real.continuousAt_log (ne_of_gt hx0)))
        hden).continuousWithinAt
  have hleft :
      (∫ x in (1 / 2 : ℝ)..(1 - ε), integrand x) =
        Real.log (-Real.log (1 - ε)) -
          Real.log (-Real.log (1 / 2 : ℝ)) := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      hleftDeriv hleftCont.intervalIntegrable
  have hrightDeriv :
      ∀ x ∈ [[1 + ε, (2 : ℝ)]],
        HasDerivAt (fun y : ℝ => Real.log (Real.log y)) (integrand x) x := by
    intro x hx
    rw [uIcc_of_le hcd] at hx
    have hx0 : 0 < x := by linarith [hx.1, hε.1]
    have hx1 : 1 < x := by linarith [hx.1, hε.1]
    have hlogpos : 0 < Real.log x := Real.log_pos hx1
    have hdinner := Real.hasDerivAt_log (ne_of_gt hx0)
    have hd :
        HasDerivAt (fun y : ℝ => Real.log (Real.log y))
          (x⁻¹ / Real.log x) x :=
      hdinner.log (ne_of_gt hlogpos)
    have hderiv : x⁻¹ / Real.log x = integrand x := by
      unfold integrand
      field_simp [ne_of_gt hx0, ne_of_gt hlogpos]
    rw [← hderiv]
    exact hd
  have hrightCont :
      ContinuousOn integrand [[1 + ε, (2 : ℝ)]] := by
    intro x hx
    rw [uIcc_of_le hcd] at hx
    have hx0 : 0 < x := by linarith [hx.1, hε.1]
    have hx1 : 1 < x := by linarith [hx.1, hε.1]
    have hlogpos : 0 < Real.log x := Real.log_pos hx1
    have hden : x * Real.log x ≠ 0 :=
      mul_ne_zero (ne_of_gt hx0) (ne_of_gt hlogpos)
    unfold integrand
    exact
      (continuousAt_const.div
        (continuousAt_id.mul (Real.continuousAt_log (ne_of_gt hx0)))
        hden).continuousWithinAt
  have hright :
      (∫ x in (1 + ε)..(2 : ℝ), integrand x) =
        Real.log (Real.log 2) - Real.log (Real.log (1 + ε)) := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      hrightDeriv hrightCont.intervalIntegrable
  have hm : Real.log (1 - ε) < 0 :=
    Real.log_neg (by linarith [hε.2]) (by linarith [hε.1])
  have hp : 0 < Real.log (1 + ε) :=
    Real.log_pos (by linarith [hε.1])
  have hhalf : -Real.log (1 / 2 : ℝ) = Real.log 2 := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
      (by norm_num : (2 : ℝ) ≠ 0), Real.log_one]
    ring
  unfold pvTrunc logExpression
  rw [hleft, hright]
  simp only [abs_of_neg hm, abs_of_pos hp]
  rw [hhalf]
  ring

theorem gap2 (ε : ℝ) (hε : ε ∈ Ioo 0 (1 / 2 : ℝ)) :
    logExpression ε =
      Real.log |Real.log (1 - ε) / Real.log (1 + ε)| := by
  have hm : Real.log (1 - ε) < 0 :=
    Real.log_neg (by linarith [hε.2]) (by linarith [hε.1])
  have hp : 0 < Real.log (1 + ε) :=
    Real.log_pos (by linarith [hε.1])
  have ha : Real.log (1 - ε) ≠ 0 := ne_of_lt hm
  have hb : Real.log (1 + ε) ≠ 0 := ne_of_gt hp
  unfold logExpression
  rw [abs_div]
  rw [Real.log_div (abs_ne_zero.mpr ha) (abs_ne_zero.mpr hb)]
  ring

theorem gap3 :
    Tendsto
      (fun ε => Real.log |Real.log (1 - ε) / Real.log (1 + ε)|)
      (nhdsWithin 0 (Ioi 0)) (nhds (Real.log 1)) := by
  have habs :
      Tendsto
        (fun ε => |Real.log (1 - ε) / Real.log (1 + ε)|)
        (nhdsWithin 0 (Ioi 0)) (nhds |-1|) :=
    continuous_abs.continuousAt.tendsto.comp tendsto_log_ratio
  have hlog :=
    (Real.continuousAt_log (by norm_num : (|-1| : ℝ) ≠ 0)).tendsto.comp habs
  change Tendsto
    (Real.log ∘ fun ε : ℝ =>
      |Real.log (1 - ε) / Real.log (1 + ε)|)
    (nhdsWithin 0 (Ioi 0)) (nhds (Real.log 1))
  simpa only [abs_neg, abs_one] using hlog

theorem gap4 :
    Tendsto (fun ε => Real.log (1 - ε) / Real.log (1 + ε))
      (nhdsWithin 0 (Ioi 0)) (nhds (-1)) := by
  exact tendsto_log_ratio

theorem gap5 : Real.log |-1| = Real.log 1 := by
  norm_num [Real.log_one]

theorem gap6 : Real.log 1 = 0 := by
  exact Real.log_one

theorem gap7 :
    Tendsto pvTrunc (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hsmallNhds : ∀ᶠ ε in nhds (0 : ℝ), ε < (1 / 2 : ℝ) :=
    Iio_mem_nhds (by norm_num)
  have hsmall :
      ∀ᶠ ε in nhdsWithin (0 : ℝ) (Ioi 0), ε < (1 / 2 : ℝ) :=
    hsmallNhds.filter_mono (by exact inf_le_left)
  have heq :
      pvTrunc =ᶠ[nhdsWithin 0 (Ioi 0)]
        (fun ε => Real.log |Real.log (1 - ε) / Real.log (1 + ε)|) := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with ε hpos hlt
    exact (gap1 ε ⟨hpos, hlt⟩).trans (gap2 ε ⟨hpos, hlt⟩)
  have ht :
      Tendsto
        (fun ε => Real.log |Real.log (1 - ε) / Real.log (1 + ε)|)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa [Real.log_one] using gap3
  exact ht.congr' heq.symm

end
end ProofGap.Exercise2393

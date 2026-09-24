import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2338
noncomputable section

open Filter
open scoped Interval

def integrand (x : ℝ) : ℝ := 1 / (x ^ 2 + x - 2)

def antiderivative (x : ℝ) : ℝ :=
  (1 / 3 : ℝ) * Real.log ((x - 1) / (x + 2))

def endpointExpression (b : ℝ) : ℝ :=
  (1 / 3 : ℝ) * (Real.log ((b - 1) / (b + 2)) + 2 * Real.log 2)

def HasImproperValue (L : ℝ) : Prop :=
  Tendsto (fun b => ∫ x in (2 : ℝ)..b, integrand x) atTop (nhds L)

private theorem hasDerivAt_antiderivative {x : ℝ} (hx : 1 < x) :
    HasDerivAt antiderivative (integrand x) x := by
  have hx1 : x - 1 ≠ 0 := by linarith
  have hx2 : x + 2 ≠ 0 := by linarith
  have hdiv :=
    ((hasDerivAt_id x).sub_const 1).div
      ((hasDerivAt_id x).add_const 2) hx2
  have hlog :=
    (Real.hasDerivAt_log (div_ne_zero hx1 hx2)).comp x hdiv
  have hscaled := hlog.const_mul (1 / 3 : ℝ)
  convert hscaled using 1
  simp only [integrand, id_eq]
  rw [show x ^ 2 + x - 2 = (x - 1) * (x + 2) by ring]
  field_simp [hx1, hx2]
  <;> ring

theorem gap1 :
    HasImproperValue ((2 / 3 : ℝ) * Real.log 2) ↔
      Tendsto (fun b => antiderivative b - antiderivative 2) atTop
        (nhds ((2 / 3 : ℝ) * Real.log 2)) := by
  unfold HasImproperValue
  have heq :
      (fun b => ∫ x in (2 : ℝ)..b, integrand x) =ᶠ[atTop]
        (fun b => antiderivative b - antiderivative 2) := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with b hb
    have hcont : ContinuousOn integrand (Set.uIcc (2 : ℝ) b) := by
      rw [Set.uIcc_of_le hb]
      intro x hx
      have hx1 : x - 1 ≠ 0 := by linarith [hx.1]
      have hx2 : x + 2 ≠ 0 := by linarith [hx.1]
      have hden : x ^ 2 + x - 2 ≠ 0 := by
        rw [show x ^ 2 + x - 2 = (x - 1) * (x + 2) by ring]
        exact mul_ne_zero hx1 hx2
      apply ContinuousAt.continuousWithinAt
      unfold integrand
      exact continuousAt_const.div
        (((continuousAt_id.pow 2).add continuousAt_id).sub continuousAt_const)
        hden
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x hx
      rw [Set.uIcc_of_le hb] at hx
      exact hasDerivAt_antiderivative (by linarith [hx.1])
    · exact hcont.intervalIntegrable
  constructor
  · intro h
    exact h.congr' heq
  · intro h
    exact h.congr' heq.symm

theorem gap2 :
    Tendsto (fun b => antiderivative b - antiderivative 2) atTop
        (nhds ((2 / 3 : ℝ) * Real.log 2)) ↔
      Tendsto endpointExpression atTop
        (nhds ((2 / 3 : ℝ) * Real.log 2)) := by
  have hquarter : Real.log ((1 : ℝ) / 4) = -2 * Real.log 2 := by
    rw [show (1 : ℝ) / 4 = ((2 : ℝ) ^ 2)⁻¹ by norm_num,
      Real.log_inv, Real.log_pow]
    ring
  have hfun :
      (fun b => antiderivative b - antiderivative 2) = endpointExpression := by
    funext b
    simp only [antiderivative, endpointExpression]
    rw [show ((2 : ℝ) - 1) / (2 + 2) = (1 : ℝ) / 4 by norm_num,
      hquarter]
    ring
  rw [hfun]

theorem gap3 :
    Tendsto endpointExpression atTop
      (nhds ((2 / 3 : ℝ) * Real.log 2)) := by
  have hden : Tendsto (fun b : ℝ => b + 2) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro a
    filter_upwards [eventually_ge_atTop (a - 2)] with b hb
    linarith
  have hinv : Tendsto (fun y : ℝ => y⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hfrac :
      Tendsto (fun b : ℝ => 3 / (b + 2)) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul (hinv.comp hden) :
        Tendsto (fun b : ℝ => 3 * (b + 2)⁻¹) atTop (nhds (3 * 0)))
  have hbase :
      Tendsto (fun b : ℝ => (1 : ℝ) - 3 / (b + 2)) atTop
        (nhds ((1 : ℝ) - 0)) :=
    tendsto_const_nhds.sub hfrac
  have heq :
      (fun b : ℝ => (1 : ℝ) - 3 / (b + 2)) =ᶠ[atTop]
        (fun b : ℝ => (b - 1) / (b + 2)) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with b hb
    have hb2 : b + 2 ≠ 0 := by linarith
    field_simp [hb2]
    ring
  have hratio :
      Tendsto (fun b : ℝ => (b - 1) / (b + 2)) atTop (nhds 1) := by
    simpa only [sub_zero] using hbase.congr' heq
  have hlog0 :
      Tendsto (fun b : ℝ => Real.log ((b - 1) / (b + 2))) atTop
        (nhds 0) := by
    have h :=
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio
    simpa using h
  have hscaled :
      Tendsto
        (fun b : ℝ => (1 / 3 : ℝ) *
          (Real.log ((b - 1) / (b + 2)) + 2 * Real.log 2))
        atTop
        (nhds ((1 / 3 : ℝ) * (0 + 2 * Real.log 2))) :=
    tendsto_const_nhds.mul (hlog0.add tendsto_const_nhds)
  have hlimit :
      (1 / 3 : ℝ) * (0 + 2 * Real.log 2) =
        (2 / 3 : ℝ) * Real.log 2 := by
    ring
  rw [hlimit] at hscaled
  simpa only [endpointExpression] using hscaled

theorem gap4 : HasImproperValue ((2 / 3 : ℝ) * Real.log 2) := by
  exact gap1.mpr (gap2.mpr gap3)

theorem gap5 : HasImproperValue ((2 / 3 : ℝ) * Real.log 2) := by
  exact gap4

end
end ProofGap.Exercise2338

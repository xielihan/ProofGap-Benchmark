import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise2345
noncomputable section

open Filter
open scoped Interval

def integrand (x : ℝ) : ℝ :=
  Real.arctan x / Real.sqrt (1 + x ^ 2) ^ 3

def transformedIntegrand (t : ℝ) : ℝ := t * Real.cos t
def primitive (t : ℝ) : ℝ := t * Real.sin t + Real.cos t

def HasImproperValue (L : ℝ) : Prop :=
  Tendsto (fun b => ∫ x in (0 : ℝ)..b, integrand x) atTop (nhds L)

private lemma hasDerivAt_primitive (t : ℝ) :
    HasDerivAt primitive (transformedIntegrand t) t := by
  unfold primitive transformedIntegrand
  convert (((hasDerivAt_id t).mul (Real.hasDerivAt_sin t)).add
    (Real.hasDerivAt_cos t)) using 1 <;> simp [id] <;> ring

private lemma hasDerivAt_composed_primitive (x : ℝ) :
    HasDerivAt (fun y => primitive (Real.arctan y)) (integrand x) x := by
  have hpos : 0 < 1 + x ^ 2 := by
    nlinarith [sq_nonneg x]
  have hspos : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.2 hpos
  have hsq : Real.sqrt (1 + x ^ 2) ^ 2 = 1 + x ^ 2 :=
    Real.sq_sqrt hpos.le
  have hcub : Real.sqrt (1 + x ^ 2) ^ 3 =
      Real.sqrt (1 + x ^ 2) * (1 + x ^ 2) := by
    calc
      Real.sqrt (1 + x ^ 2) ^ 3 =
          Real.sqrt (1 + x ^ 2) * Real.sqrt (1 + x ^ 2) ^ 2 := by ring
      _ = Real.sqrt (1 + x ^ 2) * (1 + x ^ 2) := by rw [hsq]
  have hcoef : integrand x =
      transformedIntegrand (Real.arctan x) * (1 / (1 + x ^ 2)) := by
    unfold integrand transformedIntegrand
    rw [Real.cos_arctan, hcub]
    field_simp [ne_of_gt hpos, ne_of_gt hspos] <;> ring
  have h := (hasDerivAt_primitive (Real.arctan x)).comp x
    (Real.hasDerivAt_arctan x)
  rw [hcoef]
  simpa only [Function.comp_apply] using h

private lemma continuous_integrand : Continuous integrand := by
  unfold integrand
  apply Real.continuous_arctan.div
  · exact
      ((Real.continuous_sqrt.comp
        (continuous_const.add (continuous_id.pow 2))).pow 3)
  · intro x
    exact pow_ne_zero 3 (ne_of_gt (Real.sqrt_pos.2 (by
      nlinarith [sq_nonneg x])))

private lemma integral_integrand_eq (b : ℝ) :
    (∫ x in (0 : ℝ)..b, integrand x) =
      primitive (Real.arctan b) - primitive 0 := by
  have hInt : IntervalIntegrable integrand MeasureTheory.volume 0 b :=
    continuous_integrand.intervalIntegrable 0 b
  simpa only [Real.arctan_zero] using
    (intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hasDerivAt_composed_primitive x) hInt)

private lemma continuous_primitive : Continuous primitive := by
  unfold primitive
  exact (continuous_id.mul Real.continuous_sin).add Real.continuous_cos

private lemma continuous_transformedIntegrand : Continuous transformedIntegrand := by
  unfold transformedIntegrand
  exact continuous_id.mul Real.continuous_cos

private lemma primitive_value :
    primitive (Real.pi / 2) - primitive 0 = Real.pi / 2 - 1 := by
  simp [primitive]

private lemma transformed_integral_primitive :
    (∫ t in (0 : ℝ)..(Real.pi / 2), transformedIntegrand t) =
      primitive (Real.pi / 2) - primitive 0 := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_primitive t)
    (continuous_transformedIntegrand.intervalIntegrable 0 (Real.pi / 2))

private lemma transformed_integral_value :
    (∫ t in (0 : ℝ)..(Real.pi / 2), transformedIntegrand t) =
      Real.pi / 2 - 1 :=
  transformed_integral_primitive.trans primitive_value

private lemma improper_value : HasImproperValue (Real.pi / 2 - 1) := by
  unfold HasImproperValue
  have hfun :
      (fun b : ℝ => ∫ x in (0 : ℝ)..b, integrand x) =
        (fun b : ℝ => primitive (Real.arctan b) - primitive 0) := by
    funext b
    exact integral_integrand_eq b
  rw [hfun]
  have hcont :
      Tendsto primitive
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
        (nhds (primitive (Real.pi / 2))) :=
    continuous_primitive.continuousAt.mono_left inf_le_left
  have hp :
      Tendsto (fun b : ℝ => primitive (Real.arctan b)) atTop
        (nhds (primitive (Real.pi / 2))) :=
    hcont.comp Real.tendsto_arctan_atTop
  have hc :
      Tendsto (fun _ : ℝ => primitive 0) atTop (nhds (primitive 0)) :=
    tendsto_const_nhds
  have hs := hp.sub hc
  rw [primitive_value] at hs
  exact hs

theorem gap1 :
    HasImproperValue (Real.pi / 2 - 1) ↔
      (∫ t in (0 : ℝ)..(Real.pi / 2), transformedIntegrand t) =
        Real.pi / 2 - 1 := by
  constructor
  · intro _
    exact transformed_integral_value
  · intro _
    exact improper_value

theorem gap2 :
    (∫ t in (0 : ℝ)..(Real.pi / 2), transformedIntegrand t) =
      primitive (Real.pi / 2) - primitive 0 := by
  exact transformed_integral_primitive

theorem gap3 :
    primitive (Real.pi / 2) - primitive 0 = Real.pi / 2 - 1 := by
  exact primitive_value

theorem gap4 : HasImproperValue (Real.pi / 2 - 1) := by
  exact gap1.mpr (gap2.trans gap3)

end
end ProofGap.Exercise2345

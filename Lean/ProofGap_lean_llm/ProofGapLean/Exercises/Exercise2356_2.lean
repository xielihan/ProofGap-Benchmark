import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2356_2
noncomputable section

open Filter
open scoped Interval

def average (x : ℝ) : ℝ :=
  (1 / x) * ∫ ξ in (0 : ℝ)..x, Real.arctan ξ
def primitiveAverage (x : ℝ) : ℝ :=
  (1 / x) * (x * Real.arctan x - (1 / 2 : ℝ) * Real.log (1 + x ^ 2))
def logarithmicRemainder (x : ℝ) : ℝ :=
  Real.log (1 + x ^ 2) / (2 * x)
def derivativeQuotient (x : ℝ) : ℝ := x / (1 + x ^ 2)
def HasMean (L : ℝ) : Prop := Tendsto average atTop (nhds L)

private theorem mean_limit_aux :
    Tendsto logarithmicRemainder atTop (nhds 0) ∧
      Tendsto derivativeQuotient atTop (nhds 0) := by
  have hinv : Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hone :
      Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hinv_sq :
      Tendsto (fun x : ℝ => (x⁻¹) ^ 2) atTop (nhds 0) := by
    simpa using hinv.pow 2
  have hden :
      Tendsto (fun x : ℝ => 1 + (x⁻¹) ^ 2) atTop (nhds 1) := by
    simpa using hone.add hinv_sq
  have hquotform :
      Tendsto (fun x : ℝ => x⁻¹ / (1 + (x⁻¹) ^ 2)) atTop (nhds 0) := by
    convert hinv.div hden (by norm_num : (1 : ℝ) ≠ 0) using 1 <;> norm_num
  have hquot : Tendsto derivativeQuotient atTop (nhds 0) := by
    refine hquotform.congr' (Filter.Eventually.of_forall ?_)
    intro x
    unfold derivativeQuotient
    by_cases hx : x = 0
    · simp [hx]
    · field_simp [hx]
      <;> ring
  have hlogdiv :
      Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
    simpa only [id_eq] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hlogsmall :
      Tendsto (fun x : ℝ => Real.log (1 + (x⁻¹) ^ 2)) atTop (nhds 0) := by
    have ht :=
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hden
    simpa using ht
  have hsum :
      Tendsto
        (fun x : ℝ =>
          Real.log x / x +
            (Real.log (1 + (x⁻¹) ^ 2) * x⁻¹) / 2)
        atTop (nhds 0) := by
    simpa using hlogdiv.add ((hlogsmall.mul hinv).div_const 2)
  have hrem : Tendsto logarithmicRemainder atTop (nhds 0) := by
    refine hsum.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    have hu : 1 + (x⁻¹) ^ 2 ≠ 0 := by
      nlinarith [sq_nonneg (x⁻¹)]
    have hfactor :
        1 + x ^ 2 = x ^ 2 * (1 + (x⁻¹) ^ 2) := by
      field_simp [hx0]
      <;> ring
    unfold logarithmicRemainder
    rw [hfactor, Real.log_mul (pow_ne_zero 2 hx0) hu, Real.log_pow]
    field_simp [hx0]
    <;> ring
  exact ⟨hrem, hquot⟩

theorem gap1 :
    HasMean (Real.pi / 2) ↔
      Tendsto average atTop (nhds (Real.pi / 2)) := by
  rfl

theorem gap2 :
    Tendsto average atTop (nhds (Real.pi / 2)) ↔
      Tendsto primitiveAverage atTop (nhds (Real.pi / 2)) := by
  have hprimitive_deriv (y : ℝ) :
      HasDerivAt
        (fun t : ℝ =>
          t * Real.arctan t - (1 / 2 : ℝ) * Real.log (1 + t ^ 2))
        (Real.arctan y) y := by
    have hy : 1 + y ^ 2 ≠ 0 := by
      nlinarith [sq_nonneg y]
    have hinner :
        HasDerivAt (fun t : ℝ => 1 + t ^ 2) (y * 2) y := by
      simpa [id_eq, mul_comm] using
        ((hasDerivAt_id y).pow 2).const_add (1 : ℝ)
    have hlog :
        HasDerivAt (fun t : ℝ => Real.log (1 + t ^ 2))
          ((1 + y ^ 2)⁻¹ * (y * 2)) y := by
      simpa [Function.comp_def] using
        (Real.hasDerivAt_log hy).comp y hinner
    have hprod :
        HasDerivAt (fun t : ℝ => t * Real.arctan t)
          (Real.arctan y + y * (1 / (1 + y ^ 2))) y := by
      simpa [id_eq] using
        (hasDerivAt_id y).mul (Real.hasDerivAt_arctan y)
    have hscaled :
        HasDerivAt
          (fun t : ℝ => (1 / 2 : ℝ) * Real.log (1 + t ^ 2))
          ((1 / 2 : ℝ) * ((1 + y ^ 2)⁻¹ * (y * 2))) y := by
      simpa using
        (hasDerivAt_const y (1 / 2 : ℝ)).mul hlog
    convert hprod.sub hscaled using 1 <;>
      field_simp [hy] <;> ring
  have hintegral (x : ℝ) :
      (∫ ξ in (0 : ℝ)..x, Real.arctan ξ) =
        x * Real.arctan x - (1 / 2 : ℝ) * Real.log (1 + x ^ 2) := by
    have hfund :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun y (_hy : y ∈ Set.uIcc (0 : ℝ) x) => hprimitive_deriv y)
    simpa using
      (hfund (Real.continuous_arctan.intervalIntegrable (0 : ℝ) x))
  have heq : average =ᶠ[atTop] primitiveAverage := by
    apply Filter.Eventually.of_forall
    intro x
    unfold average primitiveAverage
    rw [hintegral x]
  exact tendsto_congr' heq

theorem gap3 :
    HasMean (Real.pi / 2) ↔
      Tendsto primitiveAverage atTop (nhds (Real.pi / 2)) := by
  exact gap1.trans gap2

theorem gap4 :
    Tendsto primitiveAverage atTop (nhds (Real.pi / 2)) ↔
      Tendsto (fun x => Real.pi / 2 - logarithmicRemainder x)
        atTop (nhds (Real.pi / 2)) := by
  have hatan :
      Tendsto Real.arctan atTop (nhds (Real.pi / 2)) :=
    Real.tendsto_arctan_atTop.mono_right inf_le_left
  have hprimitive :
      primitiveAverage =ᶠ[atTop]
        (fun x => Real.arctan x - logarithmicRemainder x) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    unfold primitiveAverage logarithmicRemainder
    field_simp [ne_of_gt hx]
    <;> ring
  constructor
  · intro h
    have hrem : Tendsto logarithmicRemainder atTop (nhds 0) := by
      have ht := hatan.sub h
      have heq :
          (fun x => Real.arctan x - primitiveAverage x) =ᶠ[atTop]
            logarithmicRemainder := by
        filter_upwards [hprimitive] with x hx
        rw [hx]
        ring
      simpa using ht.congr' heq
    simpa using
      ((tendsto_const_nhds :
          Tendsto (fun _ : ℝ => Real.pi / 2) atTop
            (nhds (Real.pi / 2))).sub hrem)
  · intro h
    have hrem : Tendsto logarithmicRemainder atTop (nhds 0) := by
      have ht :=
        (tendsto_const_nhds :
          Tendsto (fun _ : ℝ => Real.pi / 2) atTop
            (nhds (Real.pi / 2))).sub h
      simpa using ht
    have ht := hatan.sub hrem
    simpa using ht.congr' hprimitive.symm

theorem gap5 :
    Tendsto logarithmicRemainder atTop (nhds 0) ↔
      Tendsto derivativeQuotient atTop (nhds 0) := by
  exact iff_of_true mean_limit_aux.1 mean_limit_aux.2

theorem gap6 :
    Tendsto derivativeQuotient atTop (nhds 0) := by
  exact mean_limit_aux.2

theorem gap7 : HasMean (Real.pi / 2) := by
  apply gap3.mpr
  apply gap4.mpr
  have hrem : Tendsto logarithmicRemainder atTop (nhds 0) :=
    gap5.mpr gap6
  simpa using
    ((tendsto_const_nhds :
        Tendsto (fun _ : ℝ => Real.pi / 2) atTop
          (nhds (Real.pi / 2))).sub hrem)

end
end ProofGap.Exercise2356_2

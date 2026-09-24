import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open Filter
open MeasureTheory
open scoped Interval Topology

namespace ProofGap.Exercise2476

noncomputable section

def XAxisVolume (V : ℝ) : Prop :=
  Tendsto (fun A : ℝ =>
    Real.pi * ∫ x in 0..A, Real.exp (-2 * x)) atTop (nhds V)

def yAxisVolume : ℝ :=
  Real.pi * ∫ y in (0 : ℝ)..1, (-Real.log y) ^ 2

private theorem expIntegral (A : ℝ) :
    (∫ x in (0 : ℝ)..A, Real.exp (-2 * x)) =
      (1 - Real.exp (-2 * A)) / 2 := by
  rw [intervalIntegral.integral_comp_mul_left (f := Real.exp)
    (c := (-2 : ℝ)) (by norm_num), integral_exp]
  simp only [smul_eq_mul]
  simp only [mul_zero, Real.exp_zero]
  ring_nf

private def logSqPrimitive (x : ℝ) : ℝ :=
  x * Real.log x ^ 2 - 2 * (x * Real.log x) + 2 * x

private theorem tendsto_mul_log_sq_zero :
    Tendsto (fun x : ℝ => x * Real.log x ^ 2) (𝓝[>] 0) (nhds 0) := by
  have h :=
    (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp
      tendsto_inv_nhdsGT_zero
  refine h.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  simp only [Function.comp_apply, one_mul, add_zero, Real.log_inv]
  field_simp [hx0]

private theorem continuousOn_mul_log_sq :
    ContinuousOn (fun x : ℝ => x * Real.log x ^ 2) (Set.Icc 0 1) := by
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    have hge : ContinuousWithinAt (fun x : ℝ => x * Real.log x ^ 2)
        (Set.Ici 0) 0 := by
      rw [ContinuousWithinAt, ← nhdsGT_sup_nhdsWithin_singleton, tendsto_sup]
      constructor
      · simpa using tendsto_mul_log_sq_zero
      · exact continuousWithinAt_singleton
    exact hge.mono Set.Icc_subset_Ici_self
  · exact
      (continuous_id'.continuousAt.mul ((Real.continuousAt_log hx0).pow 2)).continuousWithinAt

private theorem logSqPrimitive_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt logSqPrimitive (Real.log x ^ 2) x := by
  unfold logSqPrimitive
  convert
    (((hasDerivAt_id x).mul ((Real.hasDerivAt_log hx.ne').pow 2)).sub
      ((Real.hasDerivAt_mul_log hx.ne').const_mul 2)).add
        ((hasDerivAt_id x).const_mul 2) using 1 <;>
    simp only [id_eq, Pi.pow_apply] <;>
    field_simp [hx.ne'] <;> ring

private theorem intervalIntegrable_log_sq :
    IntervalIntegrable (fun x : ℝ => Real.log x ^ 2) volume 0 1 := by
  have hcont : ContinuousOn logSqPrimitive (Set.Icc 0 1) := by
    unfold logSqPrimitive
    exact
      (continuousOn_mul_log_sq.sub
        (continuous_const.mul Real.continuous_mul_log).continuousOn).add
          (continuous_const.mul continuous_id').continuousOn
  apply intervalIntegral.intervalIntegrable_deriv_of_nonneg (g := logSqPrimitive)
  · simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hcont
  · intro x hx
    apply logSqPrimitive_hasDerivAt
    simpa using hx.1
  · intro x hx
    positivity

private theorem tendsto_logSqPrimitive_zero :
    Tendsto logSqPrimitive (𝓝[>] 0) (nhds 0) := by
  have hmulLog : Tendsto (fun x : ℝ => x * Real.log x) (𝓝[>] 0) (nhds 0) := by
    simpa only [Real.rpow_one, mul_comm] using
      (tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one)
  have hid : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (nhds 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have htwo : Tendsto (fun _ : ℝ => (2 : ℝ)) (𝓝[>] 0) (nhds 2) :=
    tendsto_const_nhds
  simpa [logSqPrimitive] using
    (tendsto_mul_log_sq_zero.sub (htwo.mul hmulLog)).add (htwo.mul hid)

private theorem tendsto_logSqPrimitive_one :
    Tendsto logSqPrimitive (𝓝[<] 1) (nhds 2) := by
  have hcont : ContinuousAt logSqPrimitive 1 := by
    unfold logSqPrimitive
    fun_prop (disch := norm_num)
  simpa [logSqPrimitive] using
    (tendsto_nhdsWithin_of_tendsto_nhds hcont.tendsto)

private theorem integral_log_sq :
    (∫ y in (0 : ℝ)..1, Real.log y ^ 2) = 2 := by
  simpa using
    (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
      (f := logSqPrimitive) (f' := fun y : ℝ => Real.log y ^ 2)
      (fa := 0) (fb := 2) (by norm_num)
      (fun x hx => logSqPrimitive_hasDerivAt hx.1)
      intervalIntegrable_log_sq tendsto_logSqPrimitive_zero tendsto_logSqPrimitive_one)

theorem gap1 (Vₓ : ℝ) (hV : XAxisVolume Vₓ) :
    Tendsto (fun A : ℝ =>
      Real.pi * ∫ x in 0..A, Real.exp (-2 * x)) atTop (nhds Vₓ) := by
  exact hV

theorem gap2 :
    Tendsto (fun A : ℝ =>
      Real.pi * ∫ x in 0..A, Real.exp (-2 * x))
        atTop (nhds (Real.pi / 2)) := by
  have hzero : Tendsto (fun A : ℝ => Real.exp (-2 * A)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by norm_num : (-2 : ℝ) < 0))
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  simpa only [expIntegral, one_div, one_mul, sub_zero] using
    ((hone.sub hzero).div_const (2 : ℝ)).const_mul Real.pi

theorem gap3 (Vₓ : ℝ) (hV : XAxisVolume Vₓ) :
    Vₓ = Real.pi / 2 := by
  exact tendsto_nhds_unique (gap1 Vₓ hV) gap2

theorem gap4 (Vᵧ : ℝ) (hV : Vᵧ = yAxisVolume) :
    Vᵧ = Real.pi * ∫ y in (0 : ℝ)..1, (-Real.log y) ^ 2 := by
  simpa [yAxisVolume] using hV

theorem gap5 :
    Real.pi * (∫ y in (0 : ℝ)..1, (-Real.log y) ^ 2) =
      2 * Real.pi := by
  have hlog : (∫ y in (0 : ℝ)..1, (-Real.log y) ^ 2) = 2 := by
    simpa [pow_two] using integral_log_sq
  rw [hlog]
  ring

theorem gap6 (Vᵧ : ℝ) (hV : Vᵧ = yAxisVolume) :
    Vᵧ = 2 * Real.pi := by
  exact (gap4 Vᵧ hV).trans gap5

end

end ProofGap.Exercise2476

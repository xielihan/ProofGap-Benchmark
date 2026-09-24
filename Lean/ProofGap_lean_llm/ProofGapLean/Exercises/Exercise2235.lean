import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter Topology
open scoped Interval

namespace ProofGap.Exercise2235

noncomputable section

def rightZero := nhdsWithin (0 : ℝ) (Set.Ioi 0)

def originalRatio (x : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..Real.sin x, Real.sqrt (Real.tan t)) /
    (∫ t in (0 : ℝ)..Real.tan x, Real.sqrt (Real.sin t))

def derivativeRatio (x : ℝ) : ℝ :=
  (Real.sqrt (Real.tan (Real.sin x)) * deriv Real.sin x) /
    (Real.sqrt (Real.sin (Real.tan x)) * deriv Real.tan x)

def rewrittenRatio (x : ℝ) : ℝ :=
  Real.sqrt
      ((Real.tan (Real.sin x) / Real.sin x) *
        (Real.sin x / Real.tan x) *
        (Real.tan x / Real.sin x)) *
    Real.cos x ^ 3

private theorem sin_maps_rightZero :
    Tendsto Real.sin rightZero rightZero := by
  unfold rightZero nhdsWithin
  refine tendsto_inf.2 ⟨?_, ?_⟩
  · have hs0 : ContinuousAt Real.sin 0 := Real.continuous_sin.continuousAt
    simpa using hs0.tendsto.mono_left inf_le_left
  rw [tendsto_principal]
  filter_upwards [Ioo_mem_nhdsGT Real.pi_pos] with x hx
  exact Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2

private theorem tan_maps_rightZero :
    Tendsto Real.tan rightZero rightZero := by
  unfold rightZero nhdsWithin
  have htan0 : ContinuousAt Real.tan 0 :=
    Real.continuousAt_tan.mpr (by norm_num)
  refine tendsto_inf.2 ⟨?_, ?_⟩
  · simpa using htan0.tendsto.mono_left inf_le_left
  rw [tendsto_principal]
  filter_upwards [Ioo_mem_nhdsGT Real.pi_div_two_pos] with x hx
  exact Real.tan_pos_of_pos_of_lt_pi_div_two hx.1 hx.2

private theorem tendsto_sin_div_self_right :
    Tendsto (fun x : ℝ => Real.sin x / x) rightZero (nhds 1) := by
  have h := (Real.hasDerivAt_sin 0).tendsto_slope_zero_right
  simpa [rightZero, div_eq_mul_inv, mul_comm] using h

private theorem tendsto_tan_div_self_right :
    Tendsto (fun x : ℝ => Real.tan x / x) rightZero (nhds 1) := by
  have h := (Real.hasDerivAt_tan (x := 0) (by norm_num)).tendsto_slope_zero_right
  simpa [rightZero, div_eq_mul_inv, mul_comm] using h

private theorem tendsto_sin_div_tan_right :
    Tendsto (fun x : ℝ => Real.sin x / Real.tan x) rightZero (nhds 1) := by
  have hraw := tendsto_sin_div_self_right.div
    tendsto_tan_div_self_right (one_ne_zero : (1 : ℝ) ≠ 0)
  convert hraw.congr' ?_ using 1 <;> norm_num
  filter_upwards [Ioo_mem_nhdsGT Real.pi_div_two_pos] with x hx
  have hx0 : x ≠ 0 := ne_of_gt hx.1
  have htan0 : Real.tan x ≠ 0 :=
    ne_of_gt (Real.tan_pos_of_pos_of_lt_pi_div_two hx.1 hx.2)
  change (Real.sin x / x) / (Real.tan x / x) = Real.sin x / Real.tan x
  field_simp [hx0, htan0]

private theorem tendsto_tan_div_sin_right :
    Tendsto (fun x : ℝ => Real.tan x / Real.sin x) rightZero (nhds 1) := by
  have hraw := tendsto_tan_div_self_right.div
    tendsto_sin_div_self_right (one_ne_zero : (1 : ℝ) ≠ 0)
  convert hraw.congr' ?_ using 1 <;> norm_num
  filter_upwards [Ioo_mem_nhdsGT Real.pi_div_two_pos] with x hx
  have hx0 : x ≠ 0 := ne_of_gt hx.1
  have hsin0 : Real.sin x ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hx.1
      (lt_trans hx.2 (by nlinarith [Real.pi_pos])))
  change (Real.tan x / x) / (Real.sin x / x) = Real.tan x / Real.sin x
  field_simp [hx0, hsin0]

private theorem tendsto_tan_sin_div_sin_right :
    Tendsto (fun x : ℝ => Real.tan (Real.sin x) / Real.sin x)
      rightZero (nhds 1) := by
  simpa only [Function.comp_apply] using
    tendsto_tan_div_self_right.comp sin_maps_rightZero

private theorem tendsto_sin_tan_div_tan_right :
    Tendsto (fun x : ℝ => Real.sin (Real.tan x) / Real.tan x)
      rightZero (nhds 1) := by
  simpa only [Function.comp_apply] using
    tendsto_sin_div_self_right.comp tan_maps_rightZero

private theorem tendsto_tan_div_sin_tan_right :
    Tendsto (fun x : ℝ => Real.tan x / Real.sin (Real.tan x))
      rightZero (nhds 1) := by
  simpa [inv_div] using
    tendsto_sin_tan_div_tan_right.inv₀ (one_ne_zero : (1 : ℝ) ≠ 0)

private theorem rewrittenRatio_tendsto_one :
    Tendsto rewrittenRatio rightZero (nhds 1) := by
  have hinside : Tendsto
      (fun x : ℝ =>
        (Real.tan (Real.sin x) / Real.sin x) *
          (Real.sin x / Real.tan x) *
          (Real.tan x / Real.sin x))
      rightZero (nhds 1) := by
    simpa using
      (tendsto_tan_sin_div_sin_right.mul tendsto_sin_div_tan_right).mul
        tendsto_tan_div_sin_right
  have hsqrt : Tendsto
      (fun x : ℝ => Real.sqrt
        ((Real.tan (Real.sin x) / Real.sin x) *
          (Real.sin x / Real.tan x) *
          (Real.tan x / Real.sin x)))
      rightZero (nhds 1) := by
    simpa using Real.continuous_sqrt.continuousAt.tendsto.comp hinside
  have hcos : Tendsto (fun x : ℝ => Real.cos x ^ 3) rightZero (nhds 1) := by
    have hc0 : ContinuousAt Real.cos 0 := Real.continuous_cos.continuousAt
    simpa [rightZero] using (hc0.pow 3).tendsto.mono_left inf_le_left
  simpa [rewrittenRatio] using hsqrt.mul hcos

private theorem derivativeRatio_tendsto_one :
    Tendsto derivativeRatio rightZero (nhds 1) := by
  have hquot : Tendsto
      (fun x : ℝ => Real.tan (Real.sin x) / Real.sin (Real.tan x))
      rightZero (nhds 1) := by
    have hprod :=
      (tendsto_tan_sin_div_sin_right.mul tendsto_sin_div_tan_right).mul
        tendsto_tan_div_sin_tan_right
    convert hprod.congr' ?_ using 1 <;> norm_num
    filter_upwards [Ioo_mem_nhdsGT Real.pi_div_two_pos,
      sin_maps_rightZero.eventually (Ioo_mem_nhdsGT Real.pi_div_two_pos),
      tan_maps_rightZero.eventually (Ioo_mem_nhdsGT Real.pi_pos)] with
      x hx hsx htx
    have hsin0 : Real.sin x ≠ 0 := ne_of_gt hsx.1
    have htan0 : Real.tan x ≠ 0 := ne_of_gt htx.1
    have hsinTan0 : Real.sin (Real.tan x) ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi htx.1 htx.2)
    change
      (Real.tan (Real.sin x) / Real.sin x) *
          (Real.sin x / Real.tan x) *
          (Real.tan x / Real.sin (Real.tan x)) =
        Real.tan (Real.sin x) / Real.sin (Real.tan x)
    field_simp [hsin0, htan0, hsinTan0]
  have hroot : Tendsto
      (fun x : ℝ => Real.sqrt
        (Real.tan (Real.sin x) / Real.sin (Real.tan x)))
      rightZero (nhds 1) := by
    simpa using Real.continuous_sqrt.continuousAt.tendsto.comp hquot
  have hcos : Tendsto (fun x : ℝ => Real.cos x ^ 3) rightZero (nhds 1) := by
    have hc0 : ContinuousAt Real.cos 0 := Real.continuous_cos.continuousAt
    simpa [rightZero] using (hc0.pow 3).tendsto.mono_left inf_le_left
  have hcore := hroot.mul hcos
  convert hcore.congr' ?_ using 1 <;> norm_num
  filter_upwards [Ioo_mem_nhdsGT Real.pi_div_two_pos,
    sin_maps_rightZero.eventually (Ioo_mem_nhdsGT Real.pi_div_two_pos),
    tan_maps_rightZero.eventually (Ioo_mem_nhdsGT Real.pi_pos)] with
    x hx hsx htx
  have hcospos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo
    ⟨lt_trans (neg_neg_of_pos Real.pi_div_two_pos) hx.1, hx.2⟩
  have htanSinPos : 0 < Real.tan (Real.sin x) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two hsx.1 hsx.2
  have hsinTanPos : 0 < Real.sin (Real.tan x) :=
    Real.sin_pos_of_pos_of_lt_pi htx.1 htx.2
  have hrootDen : Real.sqrt (Real.sin (Real.tan x)) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hsinTanPos
  change
    Real.sqrt (Real.tan (Real.sin x) / Real.sin (Real.tan x)) * Real.cos x ^ 3 =
      derivativeRatio x
  unfold derivativeRatio
  rw [Real.deriv_sin, Real.deriv_tan, Real.sqrt_div htanSinPos.le]
  field_simp [hrootDen, hcospos.ne']

private theorem sqrt_tan_stronglyMeasurable :
    MeasureTheory.StronglyMeasurable (fun t : ℝ => Real.sqrt (Real.tan t)) := by
  rw [show Real.tan = fun t : ℝ => Real.sin t / Real.cos t by
    funext t
    exact Real.tan_eq_sin_div_cos t]
  apply Measurable.stronglyMeasurable
  apply Real.continuous_sqrt.measurable.comp
  exact Real.continuous_sin.measurable.div Real.continuous_cos.measurable

private theorem originalRatio_tendsto_one :
    Tendsto originalRatio rightZero (nhds 1) := by
  let F : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..Real.sin x,
    Real.sqrt (Real.tan t)
  let G : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..Real.tan x,
    Real.sqrt (Real.sin t)
  let F' : ℝ → ℝ := fun x =>
    Real.sqrt (Real.tan (Real.sin x)) * deriv Real.sin x
  let G' : ℝ → ℝ := fun x =>
    Real.sqrt (Real.sin (Real.tan x)) * deriv Real.tan x
  have hsinSqrt : Continuous (fun t : ℝ => Real.sqrt (Real.sin t)) :=
    Real.continuous_sqrt.comp Real.continuous_sin
  have hFderiv : ∀ᶠ x in rightZero, HasDerivAt F (F' x) x := by
    filter_upwards
      [sin_maps_rightZero.eventually (Ioo_mem_nhdsGT Real.pi_div_two_pos)] with x hsx
    have htanOn : ContinuousOn Real.tan (Set.uIcc 0 (Real.sin x)) := by
      rw [Set.uIcc_of_le hsx.1.le]
      apply Real.continuousOn_tan_Ioo.mono
      intro y hy
      constructor
      · exact lt_of_lt_of_le (neg_neg_of_pos Real.pi_div_two_pos) hy.1
      · exact lt_of_le_of_lt hy.2 hsx.2
    have hcontOn : ContinuousOn (fun t : ℝ => Real.sqrt (Real.tan t))
        (Set.uIcc 0 (Real.sin x)) :=
      Real.continuous_sqrt.comp_continuousOn htanOn
    have hint : IntervalIntegrable (fun t : ℝ => Real.sqrt (Real.tan t))
        MeasureTheory.volume 0 (Real.sin x) := hcontOn.intervalIntegrable
    have hcosSin : Real.cos (Real.sin x) ≠ 0 :=
      (Real.cos_pos_of_mem_Ioo
        ⟨lt_trans (neg_neg_of_pos Real.pi_div_two_pos) hsx.1, hsx.2⟩).ne'
    have hcontAt : ContinuousAt (fun t : ℝ => Real.sqrt (Real.tan t))
        (Real.sin x) :=
      Real.continuous_sqrt.continuousAt.comp
        (Real.continuousAt_tan.mpr hcosSin)
    have houter := intervalIntegral.integral_hasDerivAt_right hint
      sqrt_tan_stronglyMeasurable.stronglyMeasurableAtFilter hcontAt
    have hcomp := houter.comp x (Real.hasDerivAt_sin x)
    simpa [F, F', Function.comp_def, Real.deriv_sin] using hcomp
  have hGderiv : ∀ᶠ x in rightZero, HasDerivAt G (G' x) x := by
    filter_upwards [Ioo_mem_nhdsGT Real.pi_div_two_pos] with x hx
    have hcos0 : Real.cos x ≠ 0 :=
      (Real.cos_pos_of_mem_Ioo
        ⟨lt_trans (neg_neg_of_pos Real.pi_div_two_pos) hx.1, hx.2⟩).ne'
    have houter := intervalIntegral.integral_hasDerivAt_right
      (hsinSqrt.intervalIntegrable 0 (Real.tan x))
      hsinSqrt.stronglyMeasurable.stronglyMeasurableAtFilter
      hsinSqrt.continuousAt
    have hcomp := houter.comp x (Real.hasDerivAt_tan hcos0)
    simpa [G, G', Function.comp_def, Real.deriv_tan] using hcomp
  have hG'ne : ∀ᶠ x in rightZero, G' x ≠ 0 := by
    filter_upwards [Ioo_mem_nhdsGT Real.pi_div_two_pos,
      tan_maps_rightZero.eventually (Ioo_mem_nhdsGT Real.pi_pos)] with x hx htx
    have hcos0 : Real.cos x ≠ 0 :=
      (Real.cos_pos_of_mem_Ioo
        ⟨lt_trans (neg_neg_of_pos Real.pi_div_two_pos) hx.1, hx.2⟩).ne'
    have hsinTan : 0 < Real.sin (Real.tan x) :=
      Real.sin_pos_of_pos_of_lt_pi htx.1 htx.2
    dsimp [G']
    rw [Real.deriv_tan]
    exact mul_ne_zero (Real.sqrt_ne_zero'.mpr hsinTan)
      (one_div_ne_zero (pow_ne_zero 2 hcos0))
  have hFzero : Tendsto F rightZero (nhds 0) := by
    have htan0 : ContinuousAt Real.tan 0 :=
      Real.continuousAt_tan.mpr (by norm_num)
    have hcont0 : ContinuousAt (fun t : ℝ => Real.sqrt (Real.tan t)) 0 :=
      Real.continuous_sqrt.continuousAt.comp htan0
    have hprim : HasDerivAt
        (fun u : ℝ => ∫ t in (0 : ℝ)..u, Real.sqrt (Real.tan t)) 0 0 := by
      simpa using intervalIntegral.integral_hasDerivAt_right
        (IntervalIntegrable.refl : IntervalIntegrable
          (fun t : ℝ => Real.sqrt (Real.tan t)) MeasureTheory.volume 0 0)
        sqrt_tan_stronglyMeasurable.stronglyMeasurableAtFilter hcont0
    have hsin0 : Tendsto Real.sin rightZero (nhds 0) :=
      by
        have hs : ContinuousAt Real.sin 0 := Real.continuous_sin.continuousAt
        simpa [rightZero] using hs.tendsto.mono_left inf_le_left
    simpa [F, Function.comp_def] using hprim.continuousAt.tendsto.comp hsin0
  have hGzero : Tendsto G rightZero (nhds 0) := by
    have hprim : HasDerivAt
        (fun u : ℝ => ∫ t in (0 : ℝ)..u, Real.sqrt (Real.sin t)) 0 0 := by
      simpa using intervalIntegral.integral_hasDerivAt_right
        (hsinSqrt.intervalIntegrable 0 0)
        hsinSqrt.stronglyMeasurable.stronglyMeasurableAtFilter
        hsinSqrt.continuousAt
    have htan0 : Tendsto Real.tan rightZero (nhds 0) := by
      have hc : ContinuousAt Real.tan 0 := Real.continuousAt_tan.mpr (by norm_num)
      simpa [rightZero] using hc.tendsto.mono_left inf_le_left
    simpa [G, Function.comp_def] using hprim.continuousAt.tendsto.comp htan0
  have hdiv : Tendsto (fun x => F' x / G' x) rightZero (nhds 1) := by
    simpa only [F', G', derivativeRatio] using derivativeRatio_tendsto_one
  have hratio := HasDerivAt.lhopital_zero_nhdsGT
    hFderiv hGderiv hG'ne hFzero hGzero hdiv
  simpa [originalRatio, F, G] using hratio

theorem gap1 :
    ∀ L : ℝ, Tendsto originalRatio rightZero (𝓝 L) ↔
      Tendsto derivativeRatio rightZero (𝓝 L) := by
  intro L
  letI : rightZero.NeBot := by
    unfold rightZero
    infer_instance
  constructor
  · intro h
    have hL : L = 1 := tendsto_nhds_unique h originalRatio_tendsto_one
    simpa [hL] using derivativeRatio_tendsto_one
  · intro h
    have hL : L = 1 := tendsto_nhds_unique h derivativeRatio_tendsto_one
    simpa [hL] using originalRatio_tendsto_one

theorem gap2 :
    ∀ L : ℝ, Tendsto derivativeRatio rightZero (𝓝 L) ↔
      Tendsto rewrittenRatio rightZero (𝓝 L) := by
  intro L
  letI : rightZero.NeBot := by
    unfold rightZero
    infer_instance
  constructor
  · intro h
    have hL : L = 1 := tendsto_nhds_unique h derivativeRatio_tendsto_one
    simpa [hL] using rewrittenRatio_tendsto_one
  · intro h
    have hL : L = 1 := tendsto_nhds_unique h rewrittenRatio_tendsto_one
    simpa [hL] using derivativeRatio_tendsto_one

theorem gap3 :
    Tendsto rewrittenRatio rightZero (𝓝 1) := by
  exact rewrittenRatio_tendsto_one

theorem gap4 :
    Tendsto originalRatio rightZero (𝓝 1) := by
  exact originalRatio_tendsto_one

end

end ProofGap.Exercise2235

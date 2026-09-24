import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise518

noncomputable section

def cot (x : ℝ) : ℝ := Real.cos x / Real.sin x
def original (x : ℝ) : ℝ :=
  Real.rpow (1 + Real.sin (Real.pi * x)) (cot (Real.pi * x))
def transformed (x : ℝ) : ℝ :=
  Real.rpow (1 + Real.sin (Real.pi * x))
    ((1 / Real.sin (Real.pi * x)) * Real.cos (Real.pi * x))
def HasLimitAtOne (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 518, gap 1. -/
theorem gap1 (L : ℝ) :
    HasLimitAtOne original L ↔ HasLimitAtOne transformed L := by
  unfold HasLimitAtOne
  have hfun : original = transformed := by
    funext x
    simp [original, transformed, cot, div_eq_mul_inv, mul_comm]
  rw [hfun]

/-- Exercise 518, gap 2. -/
theorem gap2 : HasLimitAtOne transformed (Real.exp (-1)) := by
  unfold HasLimitAtOne transformed
  have harg :
      HasDerivAt (fun x : ℝ => Real.pi * x) Real.pi 1 := by
    simpa using
      ((hasDerivAt_id (𝕜 := ℝ) (1 : ℝ)).const_mul Real.pi)
  have hsin_deriv :
      HasDerivAt (fun x : ℝ => Real.sin (Real.pi * x)) (-Real.pi) 1 := by
    simpa using
      ((Real.hasDerivAt_sin (Real.pi * (1 : ℝ))).comp 1 harg)
  have hbase_deriv :
      HasDerivAt
        (fun x : ℝ => 1 + Real.sin (Real.pi * x)) (-Real.pi) 1 := by
    exact hsin_deriv.const_add 1
  have hlog_outer :
      HasDerivAt Real.log 1
        (1 + Real.sin (Real.pi * (1 : ℝ))) := by
    simpa only [mul_one, Real.sin_pi, add_zero, inv_one] using
      (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0))
  have hlog_deriv :
      HasDerivAt
        (fun x : ℝ => Real.log (1 + Real.sin (Real.pi * x)))
        (-Real.pi) 1 := by
    simpa only [Function.comp_apply, one_mul, mul_one] using
      (hlog_outer.comp 1 hbase_deriv)
  have hsin_slope := hsin_deriv.tendsto_slope
  have hlog_slope := hlog_deriv.tendsto_slope
  have hcos_full :
      Filter.Tendsto
        (fun x : ℝ => Real.cos (Real.pi * x))
        (nhds (1 : ℝ)) (nhds (-1 : ℝ)) := by
    simpa only [ContinuousAt, Function.comp_apply, mul_one, Real.cos_pi] using
      (((Real.hasDerivAt_cos (Real.pi * (1 : ℝ))).comp 1 harg).continuousAt)
  have hcos :
      Filter.Tendsto
        (fun x : ℝ => Real.cos (Real.pi * x))
        (nhdsWithin (1 : ℝ) ({1} : Set ℝ)ᶜ) (nhds (-1 : ℝ)) :=
    hcos_full.mono_left inf_le_left
  have hprod :
      Filter.Tendsto
        (fun x : ℝ =>
          slope (fun y : ℝ => Real.log (1 + Real.sin (Real.pi * y))) 1 x *
            (slope (fun y : ℝ => Real.sin (Real.pi * y)) 1 x)⁻¹ *
              Real.cos (Real.pi * x))
        (nhdsWithin (1 : ℝ) ({1} : Set ℝ)ᶜ) (nhds (-1 : ℝ)) := by
    simpa [Real.pi_ne_zero] using
      ((hlog_slope.mul
        (hsin_slope.inv₀ (neg_ne_zero.mpr Real.pi_ne_zero))).mul hcos)
  have hslope_neg :
      ∀ᶠ x : ℝ in nhdsWithin (1 : ℝ) ({1} : Set ℝ)ᶜ,
        slope (fun y : ℝ => Real.sin (Real.pi * y)) 1 x < 0 :=
    hsin_slope.eventually
      (isOpen_Iio.mem_nhds (neg_lt_zero.mpr Real.pi_pos))
  have hexponent :
      Filter.Tendsto
        (fun x : ℝ =>
          Real.log (1 + Real.sin (Real.pi * x)) *
            ((1 / Real.sin (Real.pi * x)) * Real.cos (Real.pi * x)))
        (nhdsWithin (1 : ℝ) ({1} : Set ℝ)ᶜ) (nhds (-1 : ℝ)) := by
    apply hprod.congr'
    filter_upwards [hslope_neg] with x hx
    have hsub : x - 1 ≠ 0 := by
      intro h
      have hx1 : x = 1 := sub_eq_zero.mp h
      subst x
      simp [slope] at hx
    have hsin_ne : Real.sin (Real.pi * x) ≠ 0 := by
      intro h
      simp [slope, h] at hx
    have hsin_slope_eq :
        slope (fun y : ℝ => Real.sin (Real.pi * y)) 1 x =
          (x - 1)⁻¹ * Real.sin (Real.pi * x) := by
      simp [slope, smul_eq_mul]
    have hlog_slope_eq :
        slope (fun y : ℝ => Real.log (1 + Real.sin (Real.pi * y))) 1 x =
          (x - 1)⁻¹ * Real.log (1 + Real.sin (Real.pi * x)) := by
      simp [slope, smul_eq_mul]
    rw [hsin_slope_eq, hlog_slope_eq]
    field_simp [hsub, hsin_ne] <;> ring
  have hbase_full :
      Filter.Tendsto
        (fun x : ℝ => 1 + Real.sin (Real.pi * x))
        (nhds (1 : ℝ)) (nhds (1 : ℝ)) := by
    simpa only [ContinuousAt, mul_one, Real.sin_pi, add_zero] using
      hbase_deriv.continuousAt
  have hbase :
      Filter.Tendsto
        (fun x : ℝ => 1 + Real.sin (Real.pi * x))
        (nhdsWithin (1 : ℝ) ({1} : Set ℝ)ᶜ) (nhds (1 : ℝ)) :=
    hbase_full.mono_left inf_le_left
  have hbase_pos :
      ∀ᶠ x : ℝ in nhdsWithin (1 : ℝ) ({1} : Set ℝ)ᶜ,
        0 < 1 + Real.sin (Real.pi * x) :=
    hbase.eventually
      (isOpen_Ioi.mem_nhds (by norm_num : (1 : ℝ) ∈ Set.Ioi 0))
  have hexp :
      Filter.Tendsto
        (fun x : ℝ =>
          Real.exp
            (Real.log (1 + Real.sin (Real.pi * x)) *
              ((1 / Real.sin (Real.pi * x)) *
                Real.cos (Real.pi * x))))
        (nhdsWithin (1 : ℝ) ({1} : Set ℝ)ᶜ)
        (nhds (Real.exp (-1))) := by
    simpa only [Function.comp_apply] using
      (Real.continuous_exp.tendsto (-1)).comp hexponent
  apply hexp.congr'
  filter_upwards [hbase_pos] with x hx
  exact
    (Real.rpow_def_of_pos hx
      ((1 / Real.sin (Real.pi * x)) * Real.cos (Real.pi * x))).symm

/-- Exercise 518, gap 3. -/
theorem gap3 : HasLimitAtOne original (Real.exp (-1)) := by
  exact (gap1 (Real.exp (-1))).mpr gap2

end

end ProofGap.Exercise518

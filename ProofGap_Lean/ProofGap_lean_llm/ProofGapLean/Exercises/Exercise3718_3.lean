import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3718_3

noncomputable section

open scoped Interval

def integralFunction (α : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..α, Real.log (1 + α * x) / x

def leibnizDerivative (α : ℝ) : ℝ :=
  (1 / α) * Real.log (1 + α ^ 2) +
    ∫ x in (0 : ℝ)..α, 1 / (1 + α * x)

def closedDerivative (α : ℝ) : ℝ :=
  (2 / α) * Real.log (1 + α ^ 2)

private def regularLogQuotient (u : ℝ) : ℝ :=
  Function.update (slope (fun v : ℝ => Real.log (1 + v)) 0) 0 1 u

private lemma regularLogQuotient_eq (u : ℝ) (hu : u ≠ 0) :
    regularLogQuotient u = Real.log (1 + u) / u := by
  simp [regularLogQuotient, slope, hu, div_eq_mul_inv, mul_comm]

private lemma regularLogQuotient_continuousAt_zero :
    ContinuousAt regularLogQuotient 0 := by
  have hlog : HasDerivAt (fun u : ℝ => Real.log (1 + u)) 1 0 := by
    have hinner : HasDerivAt (fun u : ℝ => 1 + u) 1 0 := by
      simpa using (hasDerivAt_id (𝕜 := ℝ) 0).const_add 1
    have hcomp :=
      (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)).comp_of_eq
        0 hinner (by norm_num : (1 : ℝ) = 1 + 0)
    simpa [Function.comp_def] using hcomp
  exact continuousAt_update_same.mpr hlog.tendsto_slope

private lemma regularLogQuotient_continuousAt {u : ℝ} (hu : -1 < u) :
    ContinuousAt regularLogQuotient u := by
  by_cases hu0 : u = 0
  · simpa [hu0] using regularLogQuotient_continuousAt_zero
  · have hOne : 1 + u ≠ 0 := by linarith
    have hquot :
        ContinuousAt (fun v : ℝ => Real.log (1 + v) / v) u :=
      ((Real.continuousAt_log hOne).comp
        (continuousAt_const.add continuousAt_id)).div
        continuousAt_id hu0
    apply hquot.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hu0] with v hv
    exact regularLogQuotient_eq v hv

private lemma integralFunction_eq_regularIntegral (α : ℝ) :
    integralFunction α =
      ∫ u in (0 : ℝ)..α ^ 2, regularLogQuotient u := by
  by_cases hα : α = 0
  · simp [hα, integralFunction]
  · calc
      integralFunction α =
          ∫ x in (0 : ℝ)..α, α * regularLogQuotient (α * x) := by
            rw [integralFunction]
            apply intervalIntegral.integral_congr_ae
            filter_upwards [
              MeasureTheory.Measure.ae_ne MeasureTheory.volume (0 : ℝ)] with x hx _
            rw [regularLogQuotient_eq (α * x) (mul_ne_zero hα hx)]
            field_simp
      _ = ∫ u in (0 : ℝ)..α ^ 2, regularLogQuotient u := by
        simpa [pow_two] using
          (intervalIntegral.smul_integral_comp_mul_add
            (f := regularLogQuotient) (a := (0 : ℝ)) (b := α) α 0)

private lemma hasDerivAt_regularIntegral_sq (α : ℝ) :
    HasDerivAt
      (fun a : ℝ => ∫ u in (0 : ℝ)..a ^ 2, regularLogQuotient u)
      (2 * α * regularLogQuotient (α ^ 2)) α := by
  have hcontAt := regularLogQuotient_continuousAt
    (by nlinarith [sq_nonneg α] : -1 < α ^ 2)
  have hcontOn :
      ContinuousOn regularLogQuotient (Set.uIcc (0 : ℝ) (α ^ 2)) := by
    intro u hu
    rw [Set.uIcc_of_le (sq_nonneg α)] at hu
    exact (regularLogQuotient_continuousAt
      (by nlinarith [hu.1] : -1 < u)).continuousWithinAt
  have hmem : α ^ 2 ∈ Set.Ioi (-1 : ℝ) := by
    change -1 < α ^ 2
    nlinarith [sq_nonneg α]
  have hJ :
      HasDerivAt
        (fun t : ℝ => ∫ u in (0 : ℝ)..t, regularLogQuotient u)
        (regularLogQuotient (α ^ 2)) (α ^ 2) :=
    intervalIntegral.integral_hasDerivAt_right
      (hcontOn.intervalIntegrable)
      (ContinuousAt.stronglyMeasurableAtFilter
        (μ := MeasureTheory.volume) isOpen_Ioi
        (fun _ hu => regularLogQuotient_continuousAt hu) _
        hmem)
      hcontAt
  have hpow : HasDerivAt (fun a : ℝ => a ^ 2) (2 * α) α := by
    convert hasDerivAt_pow 2 α using 1 <;> norm_num
  simpa only [Function.comp_apply, mul_comm, mul_left_comm, mul_assoc] using
    hJ.comp (h := fun a : ℝ => a ^ 2) α hpow

private lemma deriv_integralFunction_eq_closedDerivative (α : ℝ) :
    deriv integralFunction α = closedDerivative α := by
  have hEq :
      integralFunction =
        fun a : ℝ => ∫ u in (0 : ℝ)..a ^ 2, regularLogQuotient u :=
    funext integralFunction_eq_regularIntegral
  rw [hEq, (hasDerivAt_regularIntegral_sq α).deriv, closedDerivative]
  by_cases hα : α = 0
  · simp [hα, regularLogQuotient]
  · rw [regularLogQuotient_eq (α ^ 2) (pow_ne_zero 2 hα)]
    field_simp

private lemma leibnizDerivative_eq_closedDerivative (α : ℝ) :
    leibnizDerivative α = closedDerivative α := by
  by_cases hα : α = 0
  · simp [hα, leibnizDerivative, closedDerivative]
  · have hIntegral :
        (∫ x in (0 : ℝ)..α, 1 / (1 + α * x)) =
          (1 / α) * Real.log (1 + α ^ 2) := by
      have hSub :=
        intervalIntegral.integral_comp_mul_add
          (f := fun u : ℝ => u⁻¹) (a := (0 : ℝ)) (b := α) hα 1
      rw [integral_inv_of_pos (by norm_num)
        (by nlinarith [sq_nonneg α] : 0 < α * α + 1)] at hSub
      simpa [one_div, pow_two, add_comm, mul_comm, mul_left_comm, mul_assoc] using hSub
    rw [leibnizDerivative, closedDerivative, hIntegral]
    ring

theorem gap1 (α : ℝ) :
    deriv integralFunction α = leibnizDerivative α := by
  rw [deriv_integralFunction_eq_closedDerivative,
    leibnizDerivative_eq_closedDerivative]

theorem gap2 (α : ℝ) :
    leibnizDerivative α = closedDerivative α :=
  leibnizDerivative_eq_closedDerivative α

theorem gap3 (α : ℝ) :
    deriv integralFunction α = closedDerivative α :=
  deriv_integralFunction_eq_closedDerivative α

end

end ProofGap.Exercise3718_3

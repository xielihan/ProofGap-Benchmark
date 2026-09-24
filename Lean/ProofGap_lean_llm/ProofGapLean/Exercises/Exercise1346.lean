import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Order.Filter.Tendsto
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ProofGap.Exercise1346

noncomputable section

def HasLimitAtOne (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds L)

def logRatio (x : ℝ) : ℝ := Real.log x / (1 - x)
def derivativeRatio (x : ℝ) : ℝ := (1 / x) / (-1)
def powerForm (x : ℝ) : ℝ := Real.rpow x (1 / (1 - x))

private theorem limits_at_one_pair :
    HasLimitAtOne derivativeRatio (-1) ∧ HasLimitAtOne logRatio (-1) := by
  constructor
  · unfold HasLimitAtOne derivativeRatio
    have hquot : ContinuousAt (fun x : ℝ => (1 : ℝ) / x) 1 :=
      continuousAt_const.div continuousAt_id (by norm_num)
    have hres : ContinuousAt
        (fun x : ℝ => ((1 : ℝ) / x) / (-1 : ℝ)) 1 :=
      hquot.div continuousAt_const (by norm_num)
    simpa using hres.tendsto.mono_left
      (show nhdsWithin 1 ({1} : Set ℝ)ᶜ ≤ nhds (1 : ℝ) from inf_le_left)
  · unfold HasLimitAtOne
    have hslope : Filter.Tendsto (slope Real.log 1)
        (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds (1 : ℝ)) := by
      simpa only [inv_one] using
        (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto_slope
    have heq : logRatio =ᶠ[nhdsWithin 1 ({1} : Set ℝ)ᶜ]
        (fun x : ℝ => -(slope Real.log 1 x)) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hx1 : x ≠ 1 := by simpa using hx
      have hsub : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
      have hsub' : 1 - x ≠ 0 := sub_ne_zero.mpr hx1.symm
      simp only [logRatio, slope, Real.log_one, vsub_eq_sub, sub_zero,
        smul_eq_mul]
      field_simp [hsub, hsub'] <;> ring
    exact hslope.neg.congr' heq.symm

theorem gap1 : HasLimitAtOne logRatio (-1) ↔
    HasLimitAtOne derivativeRatio (-1) := by
  constructor
  · intro _
    exact limits_at_one_pair.1
  · intro _
    exact limits_at_one_pair.2

theorem gap2 : HasLimitAtOne derivativeRatio (-1) := by
  exact limits_at_one_pair.1
theorem gap3 : HasLimitAtOne logRatio (-1) := by
  exact limits_at_one_pair.2
theorem gap4 : HasLimitAtOne powerForm (Real.exp (-1)) := by
  unfold HasLimitAtOne
  have hlog : Filter.Tendsto logRatio
      (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds (-1)) := by
    simpa [HasLimitAtOne] using limits_at_one_pair.2
  have hexp : Filter.Tendsto (fun x : ℝ => Real.exp (logRatio x))
      (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds (Real.exp (-1))) :=
    Real.continuous_exp.continuousAt.tendsto.comp hlog
  have hpos_nhds : ∀ᶠ x : ℝ in nhds (1 : ℝ), 0 < x :=
    isOpen_Ioi.mem_nhds (by norm_num)
  have hpos : ∀ᶠ x : ℝ in nhdsWithin 1 ({1} : Set ℝ)ᶜ, 0 < x :=
    hpos_nhds.filter_mono
      (show nhdsWithin 1 ({1} : Set ℝ)ᶜ ≤ nhds (1 : ℝ) from inf_le_left)
  have heq : powerForm =ᶠ[nhdsWithin 1 ({1} : Set ℝ)ᶜ]
      (fun x : ℝ => Real.exp (logRatio x)) :=
    hpos.mono (fun x hx => by
      simp [powerForm, Real.rpow_def_of_pos hx, logRatio, div_eq_mul_inv])
  exact hexp.congr' heq.symm

end

end ProofGap.Exercise1346

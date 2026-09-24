import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise1365

noncomputable section

def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

def f₀ (x : ℝ) : ℝ := Real.log ((2 / Real.pi) * Real.arccos x) / x
def f₁ (x : ℝ) : ℝ :=
  -1 / (Real.sqrt (1 - x ^ 2) * Real.arccos x)
def powerForm (x : ℝ) : ℝ :=
  Real.rpow ((2 / Real.pi) * Real.arccos x) (1 / x)

private theorem limits_at_zero :
    HasLimitAtZero f₀ (-2 / Real.pi) ∧
      HasLimitAtZero f₁ (-2 / Real.pi) := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hq0 : (2 / Real.pi) * Real.arccos 0 = 1 := by
    rw [Real.arccos_zero]
    field_simp [hpi]
  have harccos : HasDerivAt Real.arccos (-1) 0 := by
    simpa using
      (Real.hasDerivAt_arccos
        (by norm_num : (0 : ℝ) ≠ -1)
        (by norm_num : (0 : ℝ) ≠ 1))
  have hq :
      HasDerivAt (fun x : ℝ => (2 / Real.pi) * Real.arccos x)
        (-2 / Real.pi) 0 := by
    convert harccos.const_mul (2 / Real.pi) using 1 <;> ring
  have hlogq :
      HasDerivAt Real.log 1 ((2 / Real.pi) * Real.arccos 0) := by
    rw [hq0]
    simpa using Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)
  have hg :
      HasDerivAt
        (fun x : ℝ => Real.log ((2 / Real.pi) * Real.arccos x))
        (-2 / Real.pi) 0 := by
    simpa [Function.comp_def] using hlogq.comp 0 hq
  have hf₀ : HasLimitAtZero f₀ (-2 / Real.pi) := by
    unfold HasLimitAtZero
    have hlogq0 :
        Real.log ((2 / Real.pi) * Real.arccos 0) = 0 := by
      rw [hq0, Real.log_one]
    have heq :
        f₀ = fun t : ℝ =>
          t⁻¹ *
            (Real.log ((2 / Real.pi) * Real.arccos t) -
              Real.log ((2 / Real.pi) * Real.arccos 0)) := by
      funext t
      rw [hlogq0, sub_zero]
      unfold f₀
      rw [div_eq_mul_inv]
      ring
    rw [heq]
    simpa [zero_add, smul_eq_mul] using hg.tendsto_slope_zero
  have hsqrt :
      Continuous (fun x : ℝ => Real.sqrt (1 - x ^ 2)) :=
    Real.continuous_sqrt.comp
      (continuous_const.sub (continuous_id.pow 2))
  have hdencont :
      ContinuousAt
        (fun x : ℝ => Real.sqrt (1 - x ^ 2) * Real.arccos x) 0 :=
    hsqrt.continuousAt.mul Real.continuous_arccos.continuousAt
  have hden0 :
      Real.sqrt (1 - (0 : ℝ) ^ 2) * Real.arccos 0 ≠ 0 := by
    norm_num [Real.arccos_zero, hpi]
  have hf₁cont : ContinuousAt f₁ 0 := by
    unfold f₁
    exact continuousAt_const.div hdencont hden0
  have hf₁zero : f₁ 0 = -2 / Real.pi := by
    calc
      f₁ 0 = -1 / (Real.pi / 2) := by
        norm_num [f₁, Real.arccos_zero]
      _ = -2 / Real.pi := by
        field_simp [hpi]
  have hf₁ : HasLimitAtZero f₁ (-2 / Real.pi) := by
    unfold HasLimitAtZero
    simpa [hf₁zero] using
      hf₁cont.tendsto.mono_left
        (show nhdsWithin 0 ({0} : Set ℝ)ᶜ ≤ nhds 0 from inf_le_left)
  exact ⟨hf₀, hf₁⟩

theorem gap1 : HasLimitAtZero f₀ (-2 / Real.pi) ↔
    HasLimitAtZero f₁ (-2 / Real.pi) := by
  constructor
  · intro _
    exact limits_at_zero.2
  · intro _
    exact limits_at_zero.1
theorem gap2 : HasLimitAtZero f₁ (-2 / Real.pi) := by
  exact limits_at_zero.2
theorem gap3 : HasLimitAtZero f₀ (-2 / Real.pi) := by
  exact limits_at_zero.1
theorem gap4 : HasLimitAtZero powerForm (Real.exp (-2 / Real.pi)) := by
  have hf₀ := limits_at_zero.1
  unfold HasLimitAtZero at hf₀ ⊢
  have hexp :
      Filter.Tendsto (fun x : ℝ => Real.exp (f₀ x))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        (nhds (Real.exp (-2 / Real.pi))) :=
    Real.continuous_exp.continuousAt.tendsto.comp hf₀
  have hxlt_nhds : ∀ᶠ x : ℝ in nhds 0, x < 1 :=
    Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)
  have hxlt :
      ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ, x < 1 :=
    (show nhdsWithin 0 ({0} : Set ℝ)ᶜ ≤ nhds 0 from inf_le_left) hxlt_nhds
  have hcoef : 0 < (2 : ℝ) / Real.pi :=
    div_pos (by norm_num) Real.pi_pos
  have hpos :
      ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
        0 < (2 / Real.pi) * Real.arccos x :=
    hxlt.mono (fun x hx =>
      mul_pos hcoef (Real.arccos_pos.mpr hx))
  refine hexp.congr' (hpos.mono ?_)
  intro x hx
  change Real.exp (Real.log ((2 / Real.pi) * Real.arccos x) / x) =
    Real.rpow ((2 / Real.pi) * Real.arccos x) (1 / x)
  have hrpow :
      Real.rpow ((2 / Real.pi) * Real.arccos x) (1 / x) =
        Real.exp
          (Real.log ((2 / Real.pi) * Real.arccos x) * (1 / x)) := by
    change ((2 / Real.pi) * Real.arccos x) ^ (1 / x) = _
    exact Real.rpow_def_of_pos hx (1 / x)
  rw [hrpow]
  simp [div_eq_mul_inv]

end

end ProofGap.Exercise1365

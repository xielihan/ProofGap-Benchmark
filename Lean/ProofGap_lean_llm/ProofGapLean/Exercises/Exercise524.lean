import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise524

noncomputable section

def cot (x : ℝ) : ℝ := Real.cos x / Real.sin x
def original (x : ℝ) : ℝ :=
  Real.rpow (Real.tan (Real.pi / 4 - x)) (cot x)
def tangentForm (x : ℝ) : ℝ :=
  Real.rpow ((1 - Real.tan x) / (1 + Real.tan x)) (cot x)
def exponentialForm (x : ℝ) : ℝ :=
  Real.rpow (1 + 1 / ((1 + Real.tan x) / (-2 * Real.tan x)))
    ((-(1 + Real.tan x) / (2 * Real.tan x)) *
      (-2 / (1 + Real.tan x)))
def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

/-- Source: `proof_gap/exercise_524/1.txt`. -/
private theorem tendsto_of_eventuallyEq
    {α β : Type*} {l : Filter α} {F : Filter β} {f g : α → β}
    (hfg : f =ᶠ[l] g) (hf : Filter.Tendsto f l F) :
    Filter.Tendsto g l F := by
  intro s hs
  change g ⁻¹' s ∈ l
  have hfs : f ⁻¹' s ∈ l := by
    exact hf hs
  filter_upwards [hfg, hfs] with x hxeq hx
  simpa [hxeq] using hx

private theorem limit_data :
    (original =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ] tangentForm) ∧
    (tangentForm =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ] exponentialForm) ∧
    HasLimitAtZero tangentForm (Real.exp (-2)) := by
  have hsinDeriv : HasDerivAt Real.sin 1 0 := by
    simpa using (Real.hasDerivAt_sin (0 : ℝ))
  have hcosDeriv : HasDerivAt Real.cos 0 0 := by
    simpa using (Real.hasDerivAt_cos (0 : ℝ))
  have htan : HasDerivAt (fun x : ℝ => Real.tan x) 1 0 := by
    simpa [Real.tan_eq_sin_div_cos] using
      hsinDeriv.div hcosDeriv
        (by norm_num : Real.cos (0 : ℝ) ≠ 0)
  have hnum :
      HasDerivAt (fun x : ℝ => 1 - Real.tan x) (-1) 0 := by
    convert
      (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).sub htan
      using 1 <;> norm_num
  have hden :
      HasDerivAt (fun x : ℝ => 1 + Real.tan x) 1 0 := by
    convert
      (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).add htan
      using 1 <;> norm_num
  have hquot :
      HasDerivAt
        (fun x : ℝ => (1 - Real.tan x) / (1 + Real.tan x)) (-2) 0 := by
    convert hnum.div hden (by norm_num : 1 + Real.tan (0 : ℝ) ≠ 0)
      using 1 <;> norm_num
  have hlogAtOne : HasDerivAt Real.log 1 1 := by
    simpa using
      (Real.hasDerivAt_log (x := (1 : ℝ)) (by norm_num))
  have hlogAtBase :
      HasDerivAt Real.log 1
        ((1 - Real.tan (0 : ℝ)) / (1 + Real.tan (0 : ℝ))) := by
    simpa using hlogAtOne
  have hlog :
      HasDerivAt
        (fun x : ℝ =>
          Real.log ((1 - Real.tan x) / (1 + Real.tan x))) (-2) 0 := by
    simpa [Function.comp_def] using hlogAtBase.comp 0 hquot
  have hslope :
      Filter.Tendsto
        (fun x : ℝ =>
          Real.log ((1 - Real.tan x) / (1 + Real.tan x)) / x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (-2)) := by
    simpa [div_eq_mul_inv, mul_comm] using hlog.tendsto_slope_zero
  have hcosAt :
      Filter.Tendsto Real.cos (nhds (0 : ℝ))
        (nhds (Real.cos (0 : ℝ))) :=
    Real.continuous_cos.continuousAt
  have hcos :
      Filter.Tendsto Real.cos (nhds 0) (nhds 1) := by
    simpa using hcosAt
  have hsinRatio :
      Filter.Tendsto (fun x : ℝ => Real.sin x / x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa [div_eq_mul_inv, mul_comm] using hsinDeriv.tendsto_slope_zero
  have hratio :
      Filter.Tendsto
        (fun x : ℝ => Real.cos x / (Real.sin x / x))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa using
      (hcos.mono_left inf_le_left).div hsinRatio
        (by norm_num : (1 : ℝ) ≠ 0)
  have hxcot_eq (x : ℝ) :
      x * cot x = Real.cos x / (Real.sin x / x) := by
    calc
      x * cot x = Real.cos x * (x / Real.sin x) := by
        simp only [cot, div_eq_mul_inv]
        ring
      _ = Real.cos x * (Real.sin x / x)⁻¹ := by rw [inv_div]
      _ = Real.cos x / (Real.sin x / x) := by rfl
  have hxcot :
      Filter.Tendsto (fun x : ℝ => x * cot x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    convert hratio using 1
    funext x
    exact hxcot_eq x
  have hproduct :
      Filter.Tendsto
        (fun x : ℝ =>
          cot x * Real.log ((1 - Real.tan x) / (1 + Real.tan x)))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (-2)) := by
    convert hxcot.mul hslope using 1
    · funext x
      by_cases hx : x = 0
      · simp [hx, cot]
      · field_simp [hx]
    · norm_num
  have hexp :
      Filter.Tendsto
        (fun x : ℝ =>
          Real.exp
            (cot x *
              Real.log ((1 - Real.tan x) / (1 + Real.tan x))))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (Real.exp (-2))) := by
    exact Real.continuous_exp.continuousAt.tendsto.comp hproduct
  have hbase :
      Filter.Tendsto
        (fun x : ℝ => (1 - Real.tan x) / (1 + Real.tan x))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    convert hquot.continuousAt.mono_left inf_le_left using 1 <;> norm_num
  have hbase_pos :
      ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
        0 < (1 - Real.tan x) / (1 + Real.tan x) := by
    exact hbase
      (isOpen_Ioi.mem_nhds
        (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num))
  have hpowexp :
      tangentForm =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ]
        (fun x : ℝ =>
          Real.exp
            (cot x *
              Real.log ((1 - Real.tan x) / (1 + Real.tan x)))) := by
    filter_upwards [hbase_pos] with x hx
    simp only [tangentForm]
    change
      (((1 - Real.tan x) / (1 + Real.tan x)) ^ cot x : ℝ) =
        Real.exp
          (cot x * Real.log ((1 - Real.tan x) / (1 + Real.tan x)))
    rw [Real.rpow_def_of_pos hx]
    congr 1
    ring
  have htangent : HasLimitAtZero tangentForm (Real.exp (-2)) := by
    exact tendsto_of_eventuallyEq hpowexp.symm hexp
  have hcosdiff_cont :
      Continuous (fun x : ℝ => Real.cos (Real.pi / 4 - x)) :=
    Real.continuous_cos.comp (continuous_const.sub continuous_id)
  have horiginal_nhds : original =ᶠ[nhds 0] tangentForm := by
    filter_upwards
      [Real.continuous_cos.continuousAt.eventually_ne
          (by norm_num : Real.cos (0 : ℝ) ≠ 0),
       hden.continuousAt.eventually_ne
          (by norm_num : 1 + Real.tan (0 : ℝ) ≠ 0),
       hcosdiff_cont.continuousAt.eventually_ne
          (by norm_num [Real.cos_pi_div_four] :
            Real.cos (Real.pi / 4 - (0 : ℝ)) ≠ 0)]
      with x hcx hpx hcdx
    have hpx' : 1 + Real.sin x / Real.cos x ≠ 0 := by
      simpa only [Real.tan_eq_sin_div_cos] using hpx
    have hb :
        Real.tan (Real.pi / 4 - x) =
          (1 - Real.tan x) / (1 + Real.tan x) := by
      simp only [Real.tan_eq_sin_div_cos, Real.sin_sub, Real.cos_sub,
        Real.sin_pi_div_four, Real.cos_pi_div_four] at hcdx ⊢
      field_simp [hcx, hpx', hcdx] <;> ring
    simp only [original, tangentForm]
    rw [hb]
  have horiginal :
      original =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ] tangentForm :=
    horiginal_nhds.filter_mono inf_le_left
  have hexponential_nhds : tangentForm =ᶠ[nhds 0] exponentialForm := by
    filter_upwards
      [hden.continuousAt.eventually_ne
        (by norm_num : 1 + Real.tan (0 : ℝ) ≠ 0)] with x hx
    have hp : 1 + Real.tan x ≠ 0 := hx
    have hcot : cot x = 1 / Real.tan x := by
      simp [cot, Real.tan_eq_sin_div_cos, div_eq_mul_inv, mul_comm]
    have hb :
        1 + 1 / ((1 + Real.tan x) / (-2 * Real.tan x)) =
          (1 - Real.tan x) / (1 + Real.tan x) := by
      by_cases ht : Real.tan x = 0
      · simp [ht]
      · field_simp [ht, hp] <;> ring_nf
    have he :
        (-(1 + Real.tan x) / (2 * Real.tan x)) *
            (-2 / (1 + Real.tan x)) = cot x := by
      rw [hcot]
      by_cases ht : Real.tan x = 0
      · simp [ht]
      · field_simp [ht, hp] <;> ring_nf
    simp only [tangentForm, exponentialForm]
    rw [hb, he]
  have hexponential :
      tangentForm =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ] exponentialForm :=
    hexponential_nhds.filter_mono inf_le_left
  exact ⟨horiginal, hexponential, htangent⟩

theorem gap1 (L : ℝ) :
    HasLimitAtZero original L ↔ HasLimitAtZero tangentForm L := by
  constructor
  · intro h
    exact tendsto_of_eventuallyEq limit_data.1 h
  · intro h
    exact tendsto_of_eventuallyEq limit_data.1.symm h

/-- Source: `proof_gap/exercise_524/2.txt`. -/
theorem gap2 (L : ℝ) :
    HasLimitAtZero original L ↔ HasLimitAtZero exponentialForm L := by
  have hforms := limit_data.1.trans limit_data.2.1
  constructor
  · intro h
    exact tendsto_of_eventuallyEq hforms h
  · intro h
    exact tendsto_of_eventuallyEq hforms.symm h

/-- Source: `proof_gap/exercise_524/3.txt`. -/
theorem gap3 : HasLimitAtZero exponentialForm (Real.exp (-2)) := by
  exact tendsto_of_eventuallyEq limit_data.2.1 limit_data.2.2

/-- Source: `proof_gap/exercise_524/4.txt`. -/
theorem gap4 : HasLimitAtZero original (Real.exp (-2)) := by
  exact tendsto_of_eventuallyEq limit_data.1.symm limit_data.2.2

end

end ProofGap.Exercise524

import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise1348

noncomputable section

def center : ℝ := Real.pi / 4
def HasLimitAtCenter (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin center ({center} : Set ℝ)ᶜ) (nhds L)

def cot (x : ℝ) : ℝ := Real.cos x / Real.sin x
def sec (x : ℝ) : ℝ := 1 / Real.cos x
def csc (x : ℝ) : ℝ := 1 / Real.sin x
def f₀ (x : ℝ) : ℝ := Real.tan (2 * x) * Real.log (Real.tan x)
def f₁ (x : ℝ) : ℝ := Real.log (Real.tan x) / cot (2 * x)
def f₂ (x : ℝ) : ℝ :=
  (sec x ^ 2 / Real.tan x) / (-2 * csc (2 * x) ^ 2)
def f₃ (x : ℝ) : ℝ := -Real.sin (2 * x)
def powerForm (x : ℝ) : ℝ := Real.rpow (Real.tan x) (Real.tan (2 * x))

private theorem transformed_limits :
    HasLimitAtCenter f₁ (-1) ∧
      HasLimitAtCenter f₂ (-1) ∧ HasLimitAtCenter f₃ (-1) := by
  have htwo : 2 * center = Real.pi / 2 := by
    unfold center
    ring
  have htan : Real.tan center = 1 := by
    simp [center]
  have hcos : Real.cos center ≠ 0 := by
    rw [center, Real.cos_pi_div_four]
    positivity
  have hsin2 : Real.sin (2 * center) ≠ 0 := by
    rw [htwo]
    norm_num
  have hsqrt_sq : Real.sqrt (2 : ℝ) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hhalf_sq : (Real.sqrt (2 : ℝ) / 2) ^ 2 = (1 / 2 : ℝ) := by
    rw [div_pow, hsqrt_sq]
    norm_num
  have hhalf_inv : ((Real.sqrt (2 : ℝ) / 2) ^ 2)⁻¹ = 2 := by
    rw [hhalf_sq]
    norm_num
  have hu :
      HasDerivAt (fun x : ℝ => Real.log (Real.tan x)) 2 center := by
    have h :=
      (Real.hasDerivAt_log (by simpa [htan])).comp center
        (Real.hasDerivAt_tan hcos)
    convert h using 1 <;>
      simp [Function.comp_def, htan, center, Real.cos_pi_div_four,
        hhalf_inv]
  have hlin : HasDerivAt (fun x : ℝ => 2 * x) 2 center := by
    simpa using (hasDerivAt_id center).const_mul 2
  have hvraw :=
    ((Real.hasDerivAt_cos (2 * center)).comp center hlin).div
      ((Real.hasDerivAt_sin (2 * center)).comp center hlin) hsin2
  have hv : HasDerivAt (fun x : ℝ => cot (2 * x)) (-2) center := by
    unfold cot
    convert hvraw using 1 <;> simp [htwo] <;> ring
  have hslope :
      Filter.Tendsto
        (slope (fun x : ℝ => Real.log (Real.tan x)) center /
          slope (fun x : ℝ => cot (2 * x)) center)
        (nhdsWithin center ({center} : Set ℝ)ᶜ) (nhds (-1)) := by
    convert
      hu.tendsto_slope.div hv.tendsto_slope
        (by norm_num : (-2 : ℝ) ≠ 0) using 1 <;>
      norm_num
  have hlim :
      Filter.Tendsto
        (fun x : ℝ =>
          ((x - center)⁻¹ * Real.log (Real.tan x)) /
            ((x - center)⁻¹ * cot (2 * x)))
        (nhdsWithin center ({center} : Set ℝ)ᶜ) (nhds (-1)) := by
    apply hslope.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxc0 : x ≠ center := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx
    have hxc : x - center ≠ 0 := sub_ne_zero.mpr hxc0
    unfold slope
    dsimp
    simp [htan, htwo, cot, hxc]
  have hne :
      ∀ᶠ x in nhdsWithin center ({center} : Set ℝ)ᶜ, x ≠ center := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx
  have hf1 : HasLimitAtCenter f₁ (-1) := by
    unfold HasLimitAtCenter
    apply hlim.congr'
    filter_upwards [hne] with x hx
    have hd : x - center ≠ 0 := sub_ne_zero.mpr hx
    by_cases hvx : cot (2 * x) = 0
    · simp [f₁, hvx]
    · unfold f₁
      field_simp [hd, hvx] <;> ring
  have hf3 : HasLimitAtCenter f₃ (-1) := by
    have hc : ContinuousAt f₃ center := by
      unfold f₃
      exact
        (((Real.hasDerivAt_sin (2 * center)).comp center hlin).neg).continuousAt
    have hvalue : f₃ center = -1 := by
      unfold f₃
      rw [htwo]
      norm_num
    unfold HasLimitAtCenter
    simpa [hvalue] using hc.tendsto.mono_left inf_le_left
  have heq : f₂ = f₃ := by
    funext x
    unfold f₂ f₃ sec csc
    rw [Real.tan_eq_sin_div_cos, Real.sin_two_mul]
    by_cases hs : Real.sin x = 0
    · simp [hs]
    by_cases hc : Real.cos x = 0
    · simp [hc]
    field_simp [hs, hc] <;> ring
  have hf2 : HasLimitAtCenter f₂ (-1) := by
    rw [heq]
    exact hf3
  exact ⟨hf1, hf2, hf3⟩

theorem gap1 : HasLimitAtCenter f₀ (-1) ↔ HasLimitAtCenter f₁ (-1) := by
  have heq : f₀ = f₁ := by
    funext x
    unfold f₀ f₁ cot
    rw [Real.tan_eq_sin_div_cos]
    by_cases hs : Real.sin (2 * x) = 0
    · simp [hs]
    by_cases hc : Real.cos (2 * x) = 0
    · simp [hc]
    field_simp [hs, hc] <;> ring
  rw [heq]
theorem gap2 : HasLimitAtCenter f₁ (-1) ↔ HasLimitAtCenter f₂ (-1) := by
  constructor
  · intro _
    exact transformed_limits.2.1
  · intro _
    exact transformed_limits.1
theorem gap3 : HasLimitAtCenter f₂ (-1) ↔ HasLimitAtCenter f₃ (-1) := by
  constructor
  · intro _
    exact transformed_limits.2.2
  · intro _
    exact transformed_limits.2.1
theorem gap4 : HasLimitAtCenter f₃ (-1) := by
  exact transformed_limits.2.2
theorem gap5 : HasLimitAtCenter f₀ (-1) := by
  exact gap1.mpr (gap2.mpr (gap3.mpr gap4))
theorem gap6 : HasLimitAtCenter powerForm (Real.exp (-1)) := by
  unfold HasLimitAtCenter
  have hcos : Real.cos center ≠ 0 := by
    rw [center, Real.cos_pi_div_four]
    positivity
  have htan : Real.tan center = 1 := by
    simp [center]
  have hcont : ContinuousAt Real.tan center :=
    (Real.hasDerivAt_tan hcos).continuousAt
  have htan_pos : 0 < Real.tan center := by
    simp [htan]
  have htarget : ∀ᶠ y in nhds (Real.tan center), 0 < y := by
    exact isOpen_Ioi.mem_nhds htan_pos
  have hpos :
      ∀ᶠ x in nhdsWithin center ({center} : Set ℝ)ᶜ,
        0 < Real.tan x :=
    (hcont.tendsto.mono_left inf_le_left).eventually htarget
  have hf :
      Filter.Tendsto f₀
        (nhdsWithin center ({center} : Set ℝ)ᶜ) (nhds (-1)) := gap5
  have he :
      Filter.Tendsto (fun x => Real.exp (f₀ x))
        (nhdsWithin center ({center} : Set ℝ)ᶜ)
        (nhds (Real.exp (-1))) :=
    ((Real.hasDerivAt_exp (-1)).continuousAt.tendsto).comp hf
  apply he.congr'
  filter_upwards [hpos] with x hx
  simpa [powerForm, f₀, Real.rpow_def_of_pos hx, mul_comm]

end

end ProofGap.Exercise1348

import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise1352

noncomputable section

def HasLimitAt (a : ℝ) (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

def cot (x : ℝ) : ℝ := Real.cos x / Real.sin x
def sec (x : ℝ) : ℝ := 1 / Real.cos x
def f₀ (a x : ℝ) : ℝ :=
  cot (x - a) * Real.log (Real.tan x / Real.tan a)
def f₁ (a x : ℝ) : ℝ :=
  (Real.log (Real.tan x) - Real.log (Real.tan a)) / Real.tan (x - a)
def f₂ (a x : ℝ) : ℝ :=
  ((1 / Real.tan x) * sec x ^ 2) / sec (x - a) ^ 2
def powerForm (a x : ℝ) : ℝ :=
  Real.rpow (Real.tan x / Real.tan a) (cot (x - a))

private theorem trig_ne_zero (a : ℝ) (ha : Real.sin (2 * a) ≠ 0) :
    Real.sin a ≠ 0 ∧ Real.cos a ≠ 0 ∧ Real.tan a ≠ 0 := by
  have hsa : Real.sin a ≠ 0 := by
    intro h
    apply ha
    rw [Real.sin_two_mul, h]
    ring
  have hca : Real.cos a ≠ 0 := by
    intro h
    apply ha
    rw [Real.sin_two_mul, h]
    ring
  have hta : Real.tan a ≠ 0 := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_ne_zero hsa hca
  exact ⟨hsa, hca, hta⟩

private theorem main_limits (a : ℝ) (ha : Real.sin (2 * a) ≠ 0) :
    HasLimitAt a (f₀ a) (2 / Real.sin (2 * a)) ∧
      HasLimitAt a (f₁ a) (2 / Real.sin (2 * a)) ∧
        HasLimitAt a (f₂ a) (2 / Real.sin (2 * a)) := by
  obtain ⟨hsa, hca, hta⟩ := trig_ne_zero a ha
  let D : ℝ := 2 / Real.sin (2 * a)
  let g : ℝ → ℝ := fun x => x - a
  have hsub : HasDerivAt g 1 a := by
    simpa [g] using (hasDerivAt_id a).sub_const a

  have hlogtan :
      HasDerivAt (fun x : ℝ => Real.log (Real.tan x)) D a := by
    dsimp [D]
    convert (Real.hasDerivAt_log hta).comp a (Real.hasDerivAt_tan hca) using 1
    rw [Real.sin_two_mul, Real.tan_eq_sin_div_cos]
    field_simp [hsa, hca]
    <;> ring
  have hnum :
      Filter.Tendsto
        (fun x : ℝ =>
          (Real.log (Real.tan x) - Real.log (Real.tan a)) / (x - a))
        (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds D) := by
    have hraw := hlogtan.tendsto_slope
    change Filter.Tendsto
      (fun x : ℝ => (x - a)⁻¹ *
        (Real.log (Real.tan x) - Real.log (Real.tan a)))
      (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds D) at hraw
    simpa [div_eq_mul_inv, mul_comm] using hraw
  have hcosg : Real.cos (g a) ≠ 0 := by
    simp [g]
  have htanBase : HasDerivAt Real.tan 1 (g a) := by
    convert Real.hasDerivAt_tan hcosg using 1 <;> simp [g]
  have htanSub :
      HasDerivAt (fun x : ℝ => Real.tan (x - a)) 1 a := by
    have hc := htanBase.comp a hsub
    simpa [g] using hc
  have hden :
      Filter.Tendsto
        (fun x : ℝ => Real.tan (x - a) / (x - a))
        (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds 1) := by
    have hraw := htanSub.tendsto_slope
    change Filter.Tendsto
      (fun x : ℝ => (x - a)⁻¹ *
        (Real.tan (x - a) - Real.tan (a - a)))
      (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds 1) at hraw
    simpa [div_eq_mul_inv, mul_comm] using hraw
  have hquot :
      Filter.Tendsto
        (fun x : ℝ =>
          ((Real.log (Real.tan x) - Real.log (Real.tan a)) / (x - a)) /
            (Real.tan (x - a) / (x - a)))
        (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds D) := by
    simpa using hnum.div hden (by norm_num)
  have hev₁ :
      (fun x : ℝ =>
        ((Real.log (Real.tan x) - Real.log (Real.tan a)) / (x - a)) /
          (Real.tan (x - a) / (x - a))) =ᶠ[nhdsWithin a ({a} : Set ℝ)ᶜ]
        f₁ a := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxa : x ≠ a := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx
    by_cases ht : Real.tan (x - a) = 0
    · simp [f₁, ht]
    · dsimp [f₁]
      field_simp [sub_ne_zero.mpr hxa, ht]
      <;> ring
  have hf₁ : HasLimitAt a (f₁ a) D := hquot.congr' hev₁

  have hratioDeriv := (Real.hasDerivAt_tan hca).div_const (Real.tan a)
  have hratioAt : Real.tan a / Real.tan a ≠ 0 := div_ne_zero hta hta
  have hlogratio :
      HasDerivAt
        (fun x : ℝ => Real.log (Real.tan x / Real.tan a)) D a := by
    dsimp [D]
    convert (Real.hasDerivAt_log hratioAt).comp a hratioDeriv using 1
    rw [Real.sin_two_mul, Real.tan_eq_sin_div_cos]
    field_simp [hsa, hca]
    <;> ring
  have hlogslope :
      Filter.Tendsto
        (fun x : ℝ => Real.log (Real.tan x / Real.tan a) / (x - a))
        (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds D) := by
    have hraw := hlogratio.tendsto_slope
    change Filter.Tendsto
      (fun x : ℝ => (x - a)⁻¹ *
        (Real.log (Real.tan x / Real.tan a) -
          Real.log (Real.tan a / Real.tan a)))
      (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds D) at hraw
    simpa [hta, div_eq_mul_inv, mul_comm] using hraw
  have hsinBase : HasDerivAt Real.sin 1 (g a) := by
    convert Real.hasDerivAt_sin (g a) using 1 <;> simp [g]
  have hsinSub :
      HasDerivAt (fun x : ℝ => Real.sin (x - a)) 1 a := by
    have hc := hsinBase.comp a hsub
    simpa [g] using hc
  have hsinslope :
      Filter.Tendsto
        (fun x : ℝ => Real.sin (x - a) / (x - a))
        (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds 1) := by
    have hraw := hsinSub.tendsto_slope
    change Filter.Tendsto
      (fun x : ℝ => (x - a)⁻¹ *
        (Real.sin (x - a) - Real.sin (a - a)))
      (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds 1) at hraw
    simpa [div_eq_mul_inv, mul_comm] using hraw
  have hcoszero : Filter.Tendsto Real.cos (nhds 0) (nhds 1) := by
    have h := (Real.hasDerivAt_cos 0).continuousAt
    change Filter.Tendsto Real.cos (nhds 0) (nhds (Real.cos 0)) at h
    simpa using h
  have hsubzero :
      Filter.Tendsto (fun x : ℝ => x - a) (nhds a) (nhds 0) := by
    have h := hsub.continuousAt
    change Filter.Tendsto g (nhds a) (nhds (g a)) at h
    simpa [g] using h
  have hcosfull :
      Filter.Tendsto (fun x : ℝ => Real.cos (x - a)) (nhds a) (nhds 1) := by
    simpa only [Function.comp_apply] using hcoszero.comp hsubzero
  have hcospunct :
      Filter.Tendsto (fun x : ℝ => Real.cos (x - a))
        (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds 1) :=
    hcosfull.mono_left inf_le_left
  have hcotraw :
      Filter.Tendsto
        (fun x : ℝ => Real.cos (x - a) /
          (Real.sin (x - a) / (x - a)))
        (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds 1) := by
    simpa using hcospunct.div hsinslope (by norm_num)
  have hevcot :
      (fun x : ℝ => Real.cos (x - a) /
        (Real.sin (x - a) / (x - a))) =ᶠ[nhdsWithin a ({a} : Set ℝ)ᶜ]
        (fun x : ℝ => (x - a) * cot (x - a)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxa : x ≠ a := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx
    by_cases hs : Real.sin (x - a) = 0
    · simp [cot, hs]
    · dsimp [cot]
      field_simp [sub_ne_zero.mpr hxa, hs]
      <;> ring
  have hcotlim :
      Filter.Tendsto (fun x : ℝ => (x - a) * cot (x - a))
        (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds 1) :=
    hcotraw.congr' hevcot
  have hprod :
      Filter.Tendsto
        (fun x : ℝ =>
          (Real.log (Real.tan x / Real.tan a) / (x - a)) *
            ((x - a) * cot (x - a)))
        (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds D) := by
    simpa using hlogslope.mul hcotlim
  have hev₀ :
      (fun x : ℝ =>
        (Real.log (Real.tan x / Real.tan a) / (x - a)) *
          ((x - a) * cot (x - a))) =ᶠ[nhdsWithin a ({a} : Set ℝ)ᶜ]
        f₀ a := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxa : x ≠ a := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx
    dsimp [f₀]
    field_simp [sub_ne_zero.mpr hxa]
    <;> ring
  have hf₀ : HasLimitAt a (f₀ a) D := hprod.congr' hev₀

  have htanfull :
      Filter.Tendsto Real.tan (nhds a) (nhds (Real.tan a)) :=
    (Real.hasDerivAt_tan hca).continuousAt
  have hinvtan :
      Filter.Tendsto (fun x : ℝ => 1 / Real.tan x)
        (nhds a) (nhds (1 / Real.tan a)) :=
    tendsto_const_nhds.div htanfull hta
  have hcosa :
      Filter.Tendsto Real.cos (nhds a) (nhds (Real.cos a)) :=
    (Real.hasDerivAt_cos a).continuousAt
  have hseca :
      Filter.Tendsto (fun x : ℝ => 1 / Real.cos x)
        (nhds a) (nhds (1 / Real.cos a)) :=
    tendsto_const_nhds.div hcosa hca
  have hsecsub :
      Filter.Tendsto (fun x : ℝ => 1 / Real.cos (x - a))
        (nhds a) (nhds (1 / Real.cos 0)) := by
    simpa only [Real.cos_zero] using
      (tendsto_const_nhds.div hcosfull (show (1 : ℝ) ≠ 0 by norm_num))
  have hraw :
      Filter.Tendsto
        (fun x : ℝ =>
          ((1 / Real.tan x) * (1 / Real.cos x) ^ 2) /
            (1 / Real.cos (x - a)) ^ 2)
        (nhds a)
        (nhds (((1 / Real.tan a) * (1 / Real.cos a) ^ 2) /
          (1 / Real.cos 0) ^ 2)) := by
    exact (hinvtan.mul (hseca.pow 2)).div (hsecsub.pow 2) (by norm_num)
  have hvalue :
      ((1 / Real.tan a) * (1 / Real.cos a) ^ 2) /
          (1 / Real.cos 0) ^ 2 = D := by
    dsimp [D]
    rw [Real.cos_zero, Real.sin_two_mul, Real.tan_eq_sin_div_cos]
    field_simp [hsa, hca]
    <;> ring
  have hf₂full : Filter.Tendsto (f₂ a) (nhds a) (nhds D) := by
    change Filter.Tendsto
      (fun x : ℝ =>
        ((1 / Real.tan x) * (1 / Real.cos x) ^ 2) /
          (1 / Real.cos (x - a)) ^ 2)
      (nhds a) (nhds D)
    rw [← hvalue]
    exact hraw
  have hf₂ : HasLimitAt a (f₂ a) D := hf₂full.mono_left inf_le_left
  simpa [D] using And.intro hf₀ (And.intro hf₁ hf₂)

theorem gap1 (a : ℝ) (ha : Real.sin (2 * a) ≠ 0) :
    HasLimitAt a (f₀ a) (2 / Real.sin (2 * a)) ↔
      HasLimitAt a (f₁ a) (2 / Real.sin (2 * a)) := by
  have h := main_limits a ha
  constructor
  · intro _
    exact h.2.1
  · intro _
    exact h.1

theorem gap2 (a : ℝ) (ha : Real.sin (2 * a) ≠ 0) :
    HasLimitAt a (f₁ a) (2 / Real.sin (2 * a)) ↔
      HasLimitAt a (f₂ a) (2 / Real.sin (2 * a)) := by
  have h := main_limits a ha
  constructor
  · intro _
    exact h.2.2
  · intro _
    exact h.2.1

theorem gap3 (a : ℝ) (ha : Real.sin (2 * a) ≠ 0) :
    HasLimitAt a (f₂ a) (2 / Real.sin (2 * a)) := by
  exact (main_limits a ha).2.2

theorem gap4 (a : ℝ) (ha : Real.sin (2 * a) ≠ 0) :
    HasLimitAt a (f₀ a) (2 / Real.sin (2 * a)) := by
  exact (main_limits a ha).1

theorem gap5 (a : ℝ) (ha : Real.sin (2 * a) ≠ 0) :
    HasLimitAt a (powerForm a) (Real.exp (2 / Real.sin (2 * a))) := by
  let D : ℝ := 2 / Real.sin (2 * a)
  obtain ⟨hsa, hca, hta⟩ := trig_ne_zero a ha
  have hqfull :
      Filter.Tendsto (fun x : ℝ => Real.tan x / Real.tan a)
        (nhds a) (nhds 1) := by
    have hq := ((Real.hasDerivAt_tan hca).div_const (Real.tan a)).continuousAt
    change Filter.Tendsto (fun x : ℝ => Real.tan x / Real.tan a)
      (nhds a) (nhds (Real.tan a / Real.tan a)) at hq
    simpa [hta] using hq
  have hq :
      Filter.Tendsto (fun x : ℝ => Real.tan x / Real.tan a)
        (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds 1) :=
    hqfull.mono_left inf_le_left
  have hpos :
      ∀ᶠ x in nhdsWithin a ({a} : Set ℝ)ᶜ,
        0 < Real.tan x / Real.tan a :=
    (tendsto_order.1 hq).1 0 zero_lt_one
  have hf₀ : HasLimitAt a (f₀ a) D := by
    simpa [D] using (main_limits a ha).1
  have he : Filter.Tendsto Real.exp (nhds D) (nhds (Real.exp D)) :=
    Real.continuous_exp.continuousAt
  have hexp :
      Filter.Tendsto (fun x : ℝ => Real.exp (f₀ a x))
        (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds (Real.exp D)) := by
    simpa only [Function.comp_apply] using he.comp hf₀
  have hev :
      (fun x : ℝ => Real.exp (f₀ a x)) =ᶠ[nhdsWithin a ({a} : Set ℝ)ᶜ]
        powerForm a := by
    filter_upwards [hpos] with x hx
    dsimp [powerForm]
    calc
      Real.exp (f₀ a x) =
          Real.exp
            (Real.log (Real.tan x / Real.tan a) * cot (x - a)) := by
        congr 1
        dsimp [f₀]
        ring
      _ = Real.rpow (Real.tan x / Real.tan a) (cot (x - a)) := by
        exact (Real.rpow_def_of_pos hx (cot (x - a))).symm
  simpa [D] using hexp.congr' hev

end

end ProofGap.Exercise1352

import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.Tendsto
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise1347

noncomputable section

def HasLimitAtOne (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds L)

def cot (x : ℝ) : ℝ := Real.cos x / Real.sin x
def csc (x : ℝ) : ℝ := 1 / Real.sin x
def angle (x : ℝ) : ℝ := Real.pi * x / 2
def f₀ (x : ℝ) : ℝ := Real.tan (angle x) * Real.log (2 - x)
def f₁ (x : ℝ) : ℝ := Real.log (2 - x) / cot (angle x)
def f₂ (x : ℝ) : ℝ :=
  (1 / (x - 2)) / (-(Real.pi / 2) * csc (angle x) ^ 2)
def powerForm (x : ℝ) : ℝ := Real.rpow (2 - x) (Real.tan (angle x))

private theorem exercise1347_limits :
    HasLimitAtOne f₀ (2 / Real.pi) ∧
      HasLimitAtOne f₁ (2 / Real.pi) ∧
      HasLimitAtOne f₂ (2 / Real.pi) ∧
      HasLimitAtOne powerForm (Real.exp (2 / Real.pi)) := by
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hpi_ne : Real.pi ≠ 0 := ne_of_gt hpi_pos
  have hcoef_neg : -(Real.pi / 2) < 0 :=
    neg_lt_zero.mpr (div_pos hpi_pos (by norm_num))
  have hcoef_ne : -(Real.pi / 2) ≠ 0 := ne_of_lt hcoef_neg

  have hangle : HasDerivAt angle (Real.pi / 2) 1 := by
    simpa [angle] using
      (((hasDerivAt_id (1 : ℝ)).const_mul Real.pi).div_const 2)
  have hinner : HasDerivAt (fun x : ℝ => 2 - x) (-1) 1 := by
    simpa using
      ((hasDerivAt_const (x := (1 : ℝ)) (c := (2 : ℝ))).sub
        (hasDerivAt_id (1 : ℝ)))
  have hlog : HasDerivAt (fun x : ℝ => Real.log (2 - x)) (-1) 1 := by
    convert
      ((Real.hasDerivAt_log (by norm_num : (2 - (1 : ℝ)) ≠ 0)).comp 1 hinner)
      using 1 <;> norm_num
  have hcos :
      HasDerivAt (fun x : ℝ => Real.cos (angle x)) (-(Real.pi / 2)) 1 := by
    convert (Real.hasDerivAt_cos (angle 1)).comp 1 hangle using 1 <;>
      simp [angle] <;> ring
  have hsin : HasDerivAt (fun x : ℝ => Real.sin (angle x)) 0 1 := by
    convert (Real.hasDerivAt_sin (angle 1)).comp 1 hangle using 1 <;>
      simp [angle]
  have hcotangle :
      HasDerivAt (fun x : ℝ => cot (angle x)) (-(Real.pi / 2)) 1 := by
    have h := hcos.div hsin (by simp [angle] : Real.sin (angle 1) ≠ 0)
    convert h using 1 <;> simp [cot, angle] <;> ring

  have hlog_one : Real.log (2 - (1 : ℝ)) = 0 := by norm_num
  have hcot_one : cot (angle (1 : ℝ)) = 0 := by
    simp [cot, angle]
  have tlog :
      Filter.Tendsto
        (slope (fun x : ℝ => Real.log (2 - x)) 1)
        (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds (-1)) :=
    hasDerivAt_iff_tendsto_slope.mp hlog
  have tcot :
      Filter.Tendsto
        (slope (fun x : ℝ => cot (angle x)) 1)
        (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds (-(Real.pi / 2))) :=
    hasDerivAt_iff_tendsto_slope.mp hcotangle
  have hslopes_neg :
      ∀ᶠ x in nhdsWithin 1 ({1} : Set ℝ)ᶜ,
        slope (fun y : ℝ => cot (angle y)) 1 x < 0 :=
    tcot.eventually (eventually_lt_nhds hcoef_neg)
  have hquot_eq :
      (fun x : ℝ =>
          slope (fun y : ℝ => Real.log (2 - y)) 1 x /
            slope (fun y : ℝ => cot (angle y)) 1 x) =ᶠ[
        nhdsWithin 1 ({1} : Set ℝ)ᶜ] f₁ := by
    filter_upwards [self_mem_nhdsWithin, hslopes_neg] with x hx hslope
    have hx1 : x ≠ 1 := by simpa using hx
    have hslope_ne : slope (fun y : ℝ => cot (angle y)) 1 x ≠ 0 :=
      ne_of_lt hslope
    have hcotx : cot (angle x) ≠ 0 := by
      intro hz
      apply hslope_ne
      simp [slope, hcot_one, hz]
    simp only [slope, hlog_one, hcot_one, sub_zero, f₁]
    field_simp [sub_ne_zero.mpr hx1, hcotx]
    simp only [vsub_eq_sub, sub_zero, smul_eq_mul]
    ring
  have tf1raw :
      Filter.Tendsto f₁ (nhdsWithin 1 ({1} : Set ℝ)ᶜ)
        (nhds ((-1 : ℝ) / (-(Real.pi / 2)))) :=
    (tlog.div tcot hcoef_ne).congr' hquot_eq
  have hratio : (-1 : ℝ) / (-(Real.pi / 2)) = 2 / Real.pi := by
    field_simp [hpi_ne]
    <;> ring
  have hf1 : HasLimitAtOne f₁ (2 / Real.pi) := by
    unfold HasLimitAtOne
    rw [← hratio]
    exact tf1raw

  have hf1_f0 :
      f₁ =ᶠ[nhdsWithin 1 ({1} : Set ℝ)ᶜ] f₀ := by
    filter_upwards [self_mem_nhdsWithin, hslopes_neg] with x hx hslope
    have hx1 : x ≠ 1 := by simpa using hx
    have hslope_ne : slope (fun y : ℝ => cot (angle y)) 1 x ≠ 0 :=
      ne_of_lt hslope
    have hcotx : cot (angle x) ≠ 0 := by
      intro hz
      apply hslope_ne
      simp [slope, hcot_one, hz]
    have hcosx : Real.cos (angle x) ≠ 0 := by
      intro hz
      apply hcotx
      simp [cot, hz]
    have hsinx : Real.sin (angle x) ≠ 0 := by
      intro hz
      apply hcotx
      simp [cot, hz]
    simp only [f₀, f₁, cot, Real.tan_eq_sin_div_cos]
    field_simp [hcosx, hsinx]
    <;> ring
  have hf0 : HasLimitAtOne f₀ (2 / Real.pi) := by
    unfold HasLimitAtOne at hf1 ⊢
    exact hf1.congr' hf1_f0

  have tangle :
      Filter.Tendsto angle (nhdsWithin 1 ({1} : Set ℝ)ᶜ)
        (nhds (Real.pi / 2)) := by
    simpa [angle] using
      hangle.continuousAt.tendsto.mono_left inf_le_left
  have tsin :
      Filter.Tendsto (fun x : ℝ => Real.sin (angle x))
        (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds 1) := by
    simpa using (Real.continuous_sin.continuousAt.tendsto.comp tangle)
  have tbase :
      Filter.Tendsto (fun x : ℝ => 2 - x)
        (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds 1) := by
    convert hinner.continuousAt.tendsto.mono_left
      (show nhdsWithin (1 : ℝ) ({1} : Set ℝ)ᶜ ≤ nhds 1 from inf_le_left)
      using 1 <;> norm_num
  have txm2 :
      Filter.Tendsto (fun x : ℝ => x - 2)
        (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds (-1)) := by
    simpa using tbase.neg
  have tnum :
      Filter.Tendsto (fun x : ℝ => (x - 2)⁻¹)
        (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds (-1)) := by
    simpa using txm2.inv₀ (by norm_num : (-1 : ℝ) ≠ 0)
  have tcsc :
      Filter.Tendsto (fun x : ℝ => (Real.sin (angle x))⁻¹)
        (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds 1) := by
    simpa using tsin.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have tcoef :
      Filter.Tendsto (fun _ : ℝ => -(Real.pi / 2))
        (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds (-(Real.pi / 2))) :=
    tendsto_const_nhds
  have tden :
      Filter.Tendsto
        (fun x : ℝ => -(Real.pi / 2) * ((Real.sin (angle x))⁻¹) ^ 2)
        (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds (-(Real.pi / 2))) := by
    simpa using tcoef.mul (tcsc.pow 2)
  have hf2 : HasLimitAtOne f₂ (2 / Real.pi) := by
    unfold HasLimitAtOne
    rw [← hratio]
    unfold f₂ csc
    simpa [one_div] using tnum.div tden hcoef_ne
  have hbase_pos :
      ∀ᶠ x in nhdsWithin 1 ({1} : Set ℝ)ᶜ, 0 < 2 - x :=
    tbase.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))
  have hpower_eq :
      powerForm =ᶠ[nhdsWithin 1 ({1} : Set ℝ)ᶜ]
        (fun x : ℝ => Real.exp (f₀ x)) := by
    filter_upwards [hbase_pos] with x hx
    simpa [powerForm, f₀, Real.rpow_def_of_pos hx, mul_comm]
  have texp :
      Filter.Tendsto (fun x : ℝ => Real.exp (f₀ x))
        (nhdsWithin 1 ({1} : Set ℝ)ᶜ)
        (nhds (Real.exp (2 / Real.pi))) := by
    unfold HasLimitAtOne at hf0
    exact Real.continuous_exp.continuousAt.tendsto.comp hf0
  have hpower : HasLimitAtOne powerForm (Real.exp (2 / Real.pi)) := by
    unfold HasLimitAtOne
    exact texp.congr' hpower_eq.symm
  exact ⟨hf0, hf1, hf2, hpower⟩

theorem gap1 : HasLimitAtOne f₀ (2 / Real.pi) ↔
    HasLimitAtOne f₁ (2 / Real.pi) := by
  constructor
  · intro _
    exact exercise1347_limits.2.1
  · intro _
    exact exercise1347_limits.1

theorem gap2 : HasLimitAtOne f₁ (2 / Real.pi) ↔
    HasLimitAtOne f₂ (2 / Real.pi) := by
  constructor
  · intro _
    exact exercise1347_limits.2.2.1
  · intro _
    exact exercise1347_limits.2.1

theorem gap3 : HasLimitAtOne f₂ (2 / Real.pi) := by
  exact exercise1347_limits.2.2.1
theorem gap4 : HasLimitAtOne f₀ (2 / Real.pi) := by
  exact exercise1347_limits.1
theorem gap5 : HasLimitAtOne powerForm (Real.exp (2 / Real.pi)) := by
  exact exercise1347_limits.2.2.2

end

end ProofGap.Exercise1347

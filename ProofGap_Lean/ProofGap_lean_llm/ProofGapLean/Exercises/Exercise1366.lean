import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise1366

noncomputable section

def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

def sec (x : ℝ) : ℝ := 1 / Real.cos x
def f₀ (x : ℝ) : ℝ := (Real.log (Real.cos x) - Real.log (Real.cosh x)) / x ^ 2
def f₁ (x : ℝ) : ℝ := (-Real.tan x - Real.tanh x) / (2 * x)
def f₂ (x : ℝ) : ℝ := (-sec x ^ 2 - 1 / Real.cosh x ^ 2) / 2
def powerForm (x : ℝ) : ℝ :=
  Real.rpow (Real.cos x / Real.cosh x) (1 / x ^ 2)

private theorem continuousAt_hasLimitAtZero {f : ℝ → ℝ} (h : ContinuousAt f 0) :
    HasLimitAtZero f (f 0) := by
  unfold HasLimitAtZero
  exact h.tendsto.mono_left inf_le_left

private theorem limit_f2 : HasLimitAtZero f₂ (-1) := by
  have hsec : ContinuousAt sec 0 := by
    unfold sec
    exact continuousAt_const.div Real.continuous_cos.continuousAt (by norm_num)
  have hinvcosh : ContinuousAt (fun x : ℝ => 1 / Real.cosh x ^ 2) 0 :=
    continuousAt_const.div (Real.continuous_cosh.continuousAt.pow 2) (by norm_num)
  have hf : ContinuousAt f₂ 0 := by
    unfold f₂
    exact ((hsec.pow 2).neg.sub hinvcosh).div_const 2
  convert continuousAt_hasLimitAtZero hf using 1 <;> norm_num [f₂, sec]

private theorem limit_f1 : HasLimitAtZero f₁ (-1) := by
  let F : Filter ℝ := nhdsWithin 0 ({0} : Set ℝ)ᶜ
  have htan : Filter.Tendsto (fun x : ℝ => Real.tan x / x) F (nhds 1) := by
    have hd := Real.hasDerivAt_tan (x := (0 : ℝ)) (by norm_num)
    simpa [F, div_eq_mul_inv, mul_comm] using hd.tendsto_slope_zero
  have hsinh : Filter.Tendsto (fun x : ℝ => Real.sinh x / x) F (nhds 1) := by
    have hd := Real.hasDerivAt_sinh (0 : ℝ)
    simpa [F, div_eq_mul_inv, mul_comm] using hd.tendsto_slope_zero
  have hcosh : Filter.Tendsto Real.cosh F (nhds 1) := by
    have hc : ContinuousAt Real.cosh 0 := Real.continuous_cosh.continuousAt
    simpa [F] using hc.tendsto.mono_left inf_le_left
  have htanhModel : Filter.Tendsto
      (fun x : ℝ => (Real.sinh x / x) / Real.cosh x) F (nhds 1) := by
    simpa using hsinh.div hcosh (by norm_num)
  have htanh : Filter.Tendsto (fun x : ℝ => Real.tanh x / x) F (nhds 1) := by
    refine htanhModel.congr' (Filter.Eventually.of_forall ?_)
    intro x
    change (Real.sinh x / x) / Real.cosh x = Real.tanh x / x
    rw [Real.tanh_eq_sinh_div_cosh]
    simp only [div_eq_mul_inv]
    ring
  have hmodel : Filter.Tendsto
      (fun x : ℝ => ((-(Real.tan x / x)) - Real.tanh x / x) / 2)
      F (nhds (-1)) := by
    have h := (htan.neg.sub htanh).div_const 2
    norm_num at h
    exact h
  unfold HasLimitAtZero
  change Filter.Tendsto f₁ F (nhds (-1))
  refine hmodel.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa [F] using hx
  unfold f₁
  field_simp [hx0] <;> ring

private theorem limit_f0 : HasLimitAtZero f₀ (-1) := by
  let F : Filter ℝ := nhdsWithin 0 ({0} : Set ℝ)ᶜ
  have hsinhalf : Filter.Tendsto (fun x : ℝ => Real.sin (x / 2) / x) F (nhds (1 / 2 : ℝ)) := by
    have hi : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).div_const 2
    have ho : HasDerivAt Real.sin (Real.cos 0) ((fun x : ℝ => x / 2) 0) := by
      simpa using Real.hasDerivAt_sin (0 : ℝ)
    have hd := ho.comp 0 hi
    simpa [F, div_eq_mul_inv, mul_comm] using hd.tendsto_slope_zero
  have hsinhhalf : Filter.Tendsto (fun x : ℝ => Real.sinh (x / 2) / x) F (nhds (1 / 2 : ℝ)) := by
    have hi : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).div_const 2
    have ho : HasDerivAt Real.sinh (Real.cosh 0) ((fun x : ℝ => x / 2) 0) := by
      simpa using Real.hasDerivAt_sinh (0 : ℝ)
    have hd := ho.comp 0 hi
    simpa [F, div_eq_mul_inv, mul_comm] using hd.tendsto_slope_zero
  have hcosquad : Filter.Tendsto (fun x : ℝ => (Real.cos x - 1) / x ^ 2) F (nhds (-1 / 2 : ℝ)) := by
    have hm : Filter.Tendsto (fun x : ℝ => (-2 : ℝ) * (Real.sin (x / 2) / x) ^ 2)
        F (nhds ((-2 : ℝ) * (1 / 2 : ℝ) ^ 2)) :=
      tendsto_const_nhds.mul (hsinhalf.pow 2)
    have hm' : Filter.Tendsto (fun x : ℝ => (-2 : ℝ) * (Real.sin (x / 2) / x) ^ 2)
        F (nhds (-1 / 2 : ℝ)) := by
      norm_num at hm ⊢
      exact hm
    refine hm'.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by simpa [F] using hx
    have htwo : Real.cos x = 2 * Real.cos (x / 2) ^ 2 - 1 := by
      convert Real.cos_two_mul (x / 2) using 1 <;> ring
    have hsc := Real.sin_sq_add_cos_sq (x / 2)
    have hid : Real.cos x - 1 = -2 * Real.sin (x / 2) ^ 2 := by
      nlinarith
    rw [hid]
    field_simp [hx0] <;> ring
  have hcoshquad : Filter.Tendsto (fun x : ℝ => (Real.cosh x - 1) / x ^ 2) F (nhds (1 / 2 : ℝ)) := by
    have hm : Filter.Tendsto (fun x : ℝ => (2 : ℝ) * (Real.sinh (x / 2) / x) ^ 2)
        F (nhds ((2 : ℝ) * (1 / 2 : ℝ) ^ 2)) :=
      tendsto_const_nhds.mul (hsinhhalf.pow 2)
    have hm' : Filter.Tendsto (fun x : ℝ => (2 : ℝ) * (Real.sinh (x / 2) / x) ^ 2)
        F (nhds (1 / 2 : ℝ)) := by
      norm_num at hm ⊢
      exact hm
    refine hm'.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by simpa [F] using hx
    have hdouble : Real.cosh x = Real.cosh (x / 2) ^ 2 + Real.sinh (x / 2) ^ 2 := by
      convert Real.cosh_two_mul (x / 2) using 1 <;> ring
    have hsc := Real.cosh_sq_sub_sinh_sq (x / 2)
    have hid : Real.cosh x - 1 = 2 * Real.sinh (x / 2) ^ 2 := by
      nlinarith
    rw [hid]
    field_simp [hx0] <;> ring
  have hcosne : ∀ᶠ x in F, Real.cos x ≠ 1 := by
    have hneg : ∀ᶠ x in F, (Real.cos x - 1) / x ^ 2 < (-1 / 4 : ℝ) :=
      hcosquad.eventually ((isOpen_lt continuous_id continuous_const).mem_nhds (by norm_num))
    filter_upwards [hneg] with x hx hxeq
    rw [hxeq] at hx
    norm_num at hx
  have hcoshne : ∀ᶠ x in F, Real.cosh x ≠ 1 := by
    have hpos : ∀ᶠ x in F, (1 / 4 : ℝ) < (Real.cosh x - 1) / x ^ 2 :=
      hcoshquad.eventually ((isOpen_lt continuous_const continuous_id).mem_nhds (by norm_num))
    filter_upwards [hpos] with x hx hxeq
    rw [hxeq] at hx
    norm_num at hx
  have hlog0 : Filter.Tendsto (fun t : ℝ => t⁻¹ * Real.log (1 + t))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    have hd := Real.hasDerivAt_log (x := (1 : ℝ)) (by norm_num)
    simpa using hd.tendsto_slope_zero
  have hshift : Filter.Tendsto (fun y : ℝ => y - 1)
      (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc : ContinuousAt (fun y : ℝ => y - 1) 1 :=
        continuousAt_id.sub continuousAt_const
      simpa using hc.tendsto.mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with y hy
      have hy1 : y ≠ 1 := by simpa using hy
      simpa using sub_ne_zero.mpr hy1
  have hlog : Filter.Tendsto (fun y : ℝ => Real.log y / (y - 1))
      (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds 1) := by
    refine (hlog0.comp hshift).congr' (Filter.Eventually.of_forall ?_)
    intro y
    change (y - 1)⁻¹ * Real.log (1 + (y - 1)) = Real.log y / (y - 1)
    rw [show 1 + (y - 1) = y by ring]
    simp [div_eq_mul_inv, mul_comm]
  have hcosmap : Filter.Tendsto Real.cos F (nhdsWithin 1 ({1} : Set ℝ)ᶜ) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc0 : ContinuousAt Real.cos 0 := Real.continuous_cos.continuousAt
      simpa using hc0.tendsto.mono_left (show F ≤ nhds 0 by exact inf_le_left)
    · simpa using hcosne
  have hcoshmap : Filter.Tendsto Real.cosh F (nhdsWithin 1 ({1} : Set ℝ)ᶜ) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc0 : ContinuousAt Real.cosh 0 := Real.continuous_cosh.continuousAt
      simpa using hc0.tendsto.mono_left (show F ≤ nhds 0 by exact inf_le_left)
    · simpa using hcoshne
  have hlogcos := hlog.comp hcosmap
  have hlogcosh := hlog.comp hcoshmap
  have hlcprod : Filter.Tendsto
      (fun x : ℝ => (Real.log (Real.cos x) / (Real.cos x - 1)) * ((Real.cos x - 1) / x ^ 2))
      F (nhds (-1 / 2 : ℝ)) := by
    simpa [Function.comp_apply] using hlogcos.mul hcosquad
  have hlchprod : Filter.Tendsto
      (fun x : ℝ => (Real.log (Real.cosh x) / (Real.cosh x - 1)) * ((Real.cosh x - 1) / x ^ 2))
      F (nhds (1 / 2 : ℝ)) := by
    simpa [Function.comp_apply] using hlogcosh.mul hcoshquad
  have hlc : Filter.Tendsto (fun x : ℝ => Real.log (Real.cos x) / x ^ 2) F (nhds (-1 / 2 : ℝ)) := by
    refine hlcprod.congr' ?_
    filter_upwards [hcosne] with x hx
    have hden : Real.cos x - 1 ≠ 0 := sub_ne_zero.mpr hx
    field_simp [hden] <;> ring
  have hlch : Filter.Tendsto (fun x : ℝ => Real.log (Real.cosh x) / x ^ 2) F (nhds (1 / 2 : ℝ)) := by
    refine hlchprod.congr' ?_
    filter_upwards [hcoshne] with x hx
    have hden : Real.cosh x - 1 ≠ 0 := sub_ne_zero.mpr hx
    field_simp [hden] <;> ring
  have hsub : Filter.Tendsto
      (fun x : ℝ => Real.log (Real.cos x) / x ^ 2 - Real.log (Real.cosh x) / x ^ 2)
      F (nhds (-1)) := by
    convert hlc.sub hlch using 1 <;> norm_num
  unfold HasLimitAtZero
  change Filter.Tendsto f₀ F (nhds (-1))
  refine hsub.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa [F] using hx
  unfold f₀
  field_simp [hx0] <;> ring

private theorem limit_powerForm : HasLimitAtZero powerForm (Real.exp (-1)) := by
  have hf := limit_f0
  unfold HasLimitAtZero at hf ⊢
  have hexp : Filter.Tendsto (fun x : ℝ => Real.exp (f₀ x))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (Real.exp (-1))) :=
    Real.continuous_exp.continuousAt.tendsto.comp hf
  refine hexp.congr' ?_
  have hc0 : ContinuousAt Real.cos 0 := Real.continuous_cos.continuousAt
  have hcos : Filter.Tendsto Real.cos (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa using hc0.tendsto.mono_left inf_le_left
  have hcospos : ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ, 0 < Real.cos x :=
    hcos.eventually ((isOpen_lt continuous_const continuous_id).mem_nhds (by norm_num))
  filter_upwards [self_mem_nhdsWithin, hcospos] with x hx hxcos
  have hx0 : x ≠ 0 := by simpa using hx
  have hxcosh : 0 < Real.cosh x := Real.cosh_pos x
  have hbase : 0 < Real.cos x / Real.cosh x := div_pos hxcos hxcosh
  have hrpow := Real.rpow_def_of_pos hbase (1 / x ^ 2)
  unfold powerForm f₀
  calc
    Real.exp ((Real.log (Real.cos x) - Real.log (Real.cosh x)) / x ^ 2) =
        Real.exp (Real.log (Real.cos x / Real.cosh x) * (1 / x ^ 2)) := by
      congr 1
      rw [Real.log_div (ne_of_gt hxcos) (ne_of_gt hxcosh)]
      field_simp [hx0] <;> ring
    _ = Real.rpow (Real.cos x / Real.cosh x) (1 / x ^ 2) := hrpow.symm

theorem gap1 : HasLimitAtZero f₀ (-1) ↔ HasLimitAtZero f₁ (-1) := by
  constructor
  · intro _
    exact limit_f1
  · intro _
    exact limit_f0
theorem gap2 : HasLimitAtZero f₁ (-1) ↔ HasLimitAtZero f₂ (-1) := by
  constructor
  · intro _
    exact limit_f2
  · intro _
    exact limit_f1
theorem gap3 : HasLimitAtZero f₂ (-1) := by
  exact limit_f2
theorem gap4 : HasLimitAtZero f₀ (-1) := by
  exact limit_f0
theorem gap5 : HasLimitAtZero powerForm (Real.exp (-1)) := by
  exact limit_powerForm

end

end ProofGap.Exercise1366

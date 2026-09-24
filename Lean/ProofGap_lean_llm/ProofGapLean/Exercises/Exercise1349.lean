import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace ProofGap.Exercise1349

noncomputable section

def HasRightLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds L)

def cot (x : ℝ) : ℝ := Real.cos x / Real.sin x
def csc (x : ℝ) : ℝ := 1 / Real.sin x
def f₀ (x : ℝ) : ℝ := Real.sin x * Real.log (cot x)
def f₁ (x : ℝ) : ℝ := Real.log (cot x) / csc x
def f₂ (x : ℝ) : ℝ := (-(csc x ^ 2 / cot x)) / (-(csc x * cot x))
def f₃ (x : ℝ) : ℝ := Real.sin x / Real.cos x ^ 2
def powerForm (x : ℝ) : ℝ := Real.rpow (cot x) (Real.sin x)

private theorem eventually_small :
    ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0), x < Real.pi / 2 := by
  have h : ∀ᶠ x : ℝ in nhds 0, x < Real.pi / 2 :=
    eventually_lt_nhds (by positivity)
  exact h.filter_mono inf_le_left

private theorem eventually_sin_cos_pos :
    ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0),
      0 < Real.sin x ∧ 0 < Real.cos x := by
  filter_upwards [eventually_mem_nhdsWithin, eventually_small] with x hx hsmall
  have hsin := Real.sin_pos_of_pos_of_lt_pi hx (by linarith [Real.pi_pos])
  have hhalf : 0 < Real.pi / 2 := by positivity
  have hcos := Real.cos_pos_of_mem_Ioo ⟨(neg_lt_zero.mpr hhalf).trans hx, hsmall⟩
  exact ⟨hsin, hcos⟩

private theorem sin_to_right :
    Filter.Tendsto Real.sin (nhdsWithin 0 (Set.Ioi 0))
      (nhdsWithin 0 (Set.Ioi 0)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · simpa using
      ((Real.continuous_sin.continuousAt : ContinuousAt Real.sin 0).tendsto).mono_left
        inf_le_left
  · filter_upwards [eventually_sin_cos_pos] with x hx
    exact hx.1

private theorem f₃_limit : HasRightLimitAtZero f₃ 0 := by
  have hsin : Filter.Tendsto Real.sin (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using sin_to_right.mono_right inf_le_left
  have hcos : Filter.Tendsto Real.cos (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    simpa using
      ((Real.continuous_cos.continuousAt : ContinuousAt Real.cos 0).tendsto).mono_left
        inf_le_left
  unfold HasRightLimitAtZero
  convert hsin.div (hcos.pow 2) (by norm_num) using 1 <;> norm_num [f₃]

private theorem f₂_limit : HasRightLimitAtZero f₂ 0 := by
  apply f₃_limit.congr'
  filter_upwards [eventually_sin_cos_pos] with x hx
  have hs : Real.sin x ≠ 0 := hx.1.ne'
  have hc : Real.cos x ≠ 0 := hx.2.ne'
  simp only [f₂, f₃, csc, cot]
  field_simp [hs, hc]

private theorem f₀_limit : HasRightLimitAtZero f₀ 0 := by
  have hsin : Filter.Tendsto Real.sin (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using sin_to_right.mono_right inf_le_left
  have hcos : Filter.Tendsto Real.cos (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    simpa using
      ((Real.continuous_cos.continuousAt : ContinuousAt Real.cos 0).tendsto).mono_left
        inf_le_left
  have hlogcos : Filter.Tendsto (fun x : ℝ => Real.log (Real.cos x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hlog : Filter.Tendsto Real.log (nhds 1) (nhds 0) := by
      simpa using (Real.continuousAt_log one_ne_zero).tendsto
    exact hlog.comp hcos
  have hsinlogsin : Filter.Tendsto
      (fun x : ℝ => Real.sin x * Real.log (Real.sin x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hbase := tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one
    simp only [Real.rpow_one] at hbase
    have hc := hbase.comp sin_to_right
    convert hc using 1
    funext x
    simp only [Function.comp_apply]
    ring
  have hcalc : Filter.Tendsto
      (fun x : ℝ => Real.sin x * Real.log (Real.cos x) -
        Real.sin x * Real.log (Real.sin x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using (hsin.mul hlogcos).sub hsinlogsin
  unfold HasRightLimitAtZero
  apply hcalc.congr'
  filter_upwards [eventually_sin_cos_pos] with x hx
  have hs : Real.sin x ≠ 0 := hx.1.ne'
  have hc : Real.cos x ≠ 0 := hx.2.ne'
  rw [f₀, cot, Real.log_div hc hs]
  ring

private theorem f₁_limit : HasRightLimitAtZero f₁ 0 := by
  apply f₀_limit.congr'
  filter_upwards [eventually_sin_cos_pos] with x hx
  have hs : Real.sin x ≠ 0 := hx.1.ne'
  simp only [f₀, f₁, csc]
  field_simp [hs]

private theorem powerForm_limit :
    HasRightLimitAtZero powerForm (Real.exp 0) := by
  have hf := f₀_limit
  unfold HasRightLimitAtZero at hf ⊢
  have he : Filter.Tendsto (fun x : ℝ => Real.exp (f₀ x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.exp 0)) := by
    exact
      (Real.continuous_exp.continuousAt : ContinuousAt Real.exp 0).tendsto.comp hf
  apply he.congr'
  filter_upwards [eventually_sin_cos_pos] with x hx
  have hcot : 0 < cot x := div_pos hx.2 hx.1
  have hr : Real.rpow (cot x) (Real.sin x) =
      Real.exp (Real.log (cot x) * Real.sin x) :=
    Real.rpow_def_of_pos hcot (Real.sin x)
  rw [powerForm, hr]
  congr 1
  simp only [f₀]
  ring

theorem gap1 : HasRightLimitAtZero f₀ 0 ↔ HasRightLimitAtZero f₁ 0 := by
  constructor <;> intro _
  · exact f₁_limit
  · exact f₀_limit
theorem gap2 : HasRightLimitAtZero f₁ 0 ↔ HasRightLimitAtZero f₂ 0 := by
  constructor <;> intro _
  · exact f₂_limit
  · exact f₁_limit
theorem gap3 : HasRightLimitAtZero f₂ 0 ↔ HasRightLimitAtZero f₃ 0 := by
  constructor <;> intro _
  · exact f₃_limit
  · exact f₂_limit
theorem gap4 : HasRightLimitAtZero f₃ 0 := by exact f₃_limit
theorem gap5 : HasRightLimitAtZero f₀ 0 := by exact f₀_limit
theorem gap6 : HasRightLimitAtZero powerForm (Real.exp 0) := by exact powerForm_limit
theorem gap7 : Real.exp 0 = 1 := by norm_num
theorem gap8 : HasRightLimitAtZero powerForm 1 := by simpa using powerForm_limit

end

end ProofGap.Exercise1349

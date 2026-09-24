import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv

namespace ProofGap.Exercise1371

noncomputable section

def HasLimitAtZero (g : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto g (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

def quotient (f : ℝ → ℝ) (x : ℝ) : ℝ := f x / x
def differenceQuotient (f : ℝ → ℝ) (x : ℝ) : ℝ := (f x - f 0) / x

private theorem difference_limit (f : ℝ → ℝ) (hf : DifferentiableAt ℝ f 0) :
    HasLimitAtZero (differenceQuotient f) (deriv f 0) := by
  have hd : HasDerivAt f (deriv f 0) 0 := hf.hasDerivAt
  have hs := hasDerivAt_iff_tendsto_slope.mp hd
  unfold HasLimitAtZero
  apply hs.congr'
  filter_upwards with x
  simp [slope_def_field, differenceQuotient]

private theorem quotient_eq_difference (f : ℝ → ℝ) (hf0 : f 0 = 0) :
    quotient f = differenceQuotient f := by
  funext x
  simp [quotient, differenceQuotient, hf0]

private theorem deriv_limit (f : ℝ → ℝ) (hf : ContDiffAt ℝ 1 f 0) :
    HasLimitAtZero (fun x => deriv f x / 1) (deriv f 0) := by
  have hd : ContDiffAt ℝ 0 (deriv f) 0 :=
    hf.derivWithin (m := 0) (by norm_num)
  have hc : ContinuousAt (deriv f) 0 := hd.continuousAt
  unfold HasLimitAtZero
  simpa using hc.tendsto.mono_left inf_le_left

theorem gap1 (f : ℝ → ℝ) (hf0 : f 0 = 0) (L : ℝ) :
    HasLimitAtZero (quotient f) L ↔
      HasLimitAtZero (differenceQuotient f) L := by
  rw [quotient_eq_difference f hf0]

theorem gap2 (f : ℝ → ℝ) (hf : DifferentiableAt ℝ f 0) :
    HasLimitAtZero (differenceQuotient f) (deriv f 0) := by exact difference_limit f hf

theorem gap3 (f : ℝ → ℝ) (α : ℝ) (hα : deriv f 0 = Real.tan α) :
    deriv f 0 = Real.tan α := by exact hα

theorem gap4 (f : ℝ → ℝ) (α : ℝ) (hf0 : f 0 = 0)
    (hf : DifferentiableAt ℝ f 0) (hα : deriv f 0 = Real.tan α) :
    HasLimitAtZero (quotient f) (Real.tan α) := by
  have h := difference_limit f hf
  rw [hα] at h
  rw [quotient_eq_difference f hf0]
  exact h

theorem gap5 (f : ℝ → ℝ) (hf0 : f 0 = 0)
    (hf : ContDiffAt ℝ 1 f 0) :
    HasLimitAtZero (quotient f) (deriv f 0) ↔
      HasLimitAtZero (fun x => deriv f x / 1) (deriv f 0) := by
  constructor <;> intro _
  · exact deriv_limit f hf
  · have h := difference_limit f hf.differentiableAt_one
    rw [quotient_eq_difference f hf0]
    exact h

theorem gap6 (f : ℝ → ℝ) (hf : ContDiffAt ℝ 1 f 0) :
    HasLimitAtZero (fun x => deriv f x / 1) (deriv f 0) := by exact deriv_limit f hf

theorem gap7 (f : ℝ → ℝ) (α : ℝ) (hα : deriv f 0 = Real.tan α) :
    deriv f 0 = Real.tan α := by exact hα

theorem gap8 (f : ℝ → ℝ) (α : ℝ) (hf0 : f 0 = 0)
    (hf : ContDiffAt ℝ 1 f 0) (hα : deriv f 0 = Real.tan α) :
    HasLimitAtZero (quotient f) (Real.tan α) := by
  have h := difference_limit f hf.differentiableAt_one
  rw [hα] at h
  rw [quotient_eq_difference f hf0]
  exact h

end

end ProofGap.Exercise1371

import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

namespace ProofGap.Exercise1368

noncomputable section

def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

def sech (x : ℝ) : ℝ := 1 / Real.cosh x
def coth (x : ℝ) : ℝ := Real.cosh x / Real.sinh x
def f₀ (x : ℝ) : ℝ := (Real.log (1 + Real.exp x) - Real.log 2) / Real.tanh x
def f₁ (x : ℝ) : ℝ := (Real.exp x / (1 + Real.exp x)) / sech x ^ 2
def powerForm (x : ℝ) : ℝ :=
  Real.rpow ((1 + Real.exp x) / 2) (coth x)

private theorem f₁_limit : HasLimitAtZero f₁ (1 / 2) := by
  have he : Tendsto Real.exp (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa using
      ((Real.continuous_exp.continuousAt : ContinuousAt Real.exp 0).tendsto).mono_left
        inf_le_left
  have hc : Tendsto Real.cosh (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa using
      ((Real.continuous_cosh.continuousAt : ContinuousAt Real.cosh 0).tendsto).mono_left
        inf_le_left
  have hone :
      Tendsto (fun _ : ℝ => (1 : ℝ)) (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) :=
    tendsto_const_nhds
  have hfrac := he.div (hone.add he) (by norm_num)
  have hsech := hone.div hc (by norm_num)
  unfold HasLimitAtZero
  convert hfrac.div (hsech.pow 2) (by norm_num) using 1 <;> norm_num [f₁, sech]

private theorem f₀_limit : HasLimitAtZero f₀ (1 / 2) := by
  let N : ℝ → ℝ := fun x => Real.log (1 + Real.exp x) - Real.log 2
  let D : ℝ → ℝ := fun x => Real.tanh x
  have hN :
      ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
        HasDerivAt N (Real.exp x / (1 + Real.exp x)) x := by
    filter_upwards with x
    have he := Real.hasDerivAt_exp x
    have hinner := (hasDerivAt_const (x := x) (c := (1 : ℝ))).add he
    have hlog := (Real.hasDerivAt_log (by positivity : 1 + Real.exp x ≠ 0)).comp x hinner
    dsimp [N]
    convert hlog.sub_const (Real.log 2) using 1 <;>
      simp [Function.comp_def] <;> ring
  have hD :
      ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
        HasDerivAt D (sech x ^ 2) x := by
    filter_upwards with x
    have hs := Real.hasDerivAt_sinh x
    have hc := Real.hasDerivAt_cosh x
    have hraw := hs.div hc (Real.cosh_pos x).ne'
    convert hraw using 1
    · funext y
      dsimp [D]
      rw [Real.tanh_eq_sinh_div_cosh]
    · dsimp [sech]
      field_simp [(Real.cosh_pos x).ne']
      nlinarith [Real.cosh_sq_sub_sinh_sq x]
  have hD_ne : ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ, sech x ^ 2 ≠ 0 := by
    filter_upwards with x
    exact pow_ne_zero 2 (div_ne_zero one_ne_zero (Real.cosh_pos x).ne')
  have hzeroN : Tendsto N (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    have he : Tendsto Real.exp (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
      simpa using
        ((Real.continuous_exp.continuousAt : ContinuousAt Real.exp 0).tendsto).mono_left
          inf_le_left
    have hone :
        Tendsto (fun _ : ℝ => (1 : ℝ)) (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) :=
      tendsto_const_nhds
    have hlog : Tendsto (fun x : ℝ => Real.log (1 + Real.exp x))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (Real.log 2)) := by
      have hl : Tendsto Real.log (nhds 2) (nhds (Real.log 2)) :=
        (Real.continuousAt_log (by norm_num)).tendsto
      have hadd : Tendsto (fun x : ℝ => 1 + Real.exp x)
          (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 2) := by
        convert hone.add he using 1 <;> norm_num
      exact hl.comp hadd
    convert hlog.sub tendsto_const_nhds using 1 <;> norm_num [N]
  have hzeroD : Tendsto D (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    have hs : Tendsto Real.sinh (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
      simpa using
        ((Real.continuous_sinh.continuousAt : ContinuousAt Real.sinh 0).tendsto).mono_left
          inf_le_left
    have hc : Tendsto Real.cosh (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
      simpa using
        ((Real.continuous_cosh.continuousAt : ContinuousAt Real.cosh 0).tendsto).mono_left
          inf_le_left
    simpa [D, Real.tanh_eq_sinh_div_cosh] using hs.div hc (by norm_num)
  apply HasDerivAt.lhopital_zero_nhdsNE hN hD hD_ne hzeroN hzeroD
  change Tendsto f₁ (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (1 / 2))
  exact f₁_limit

private theorem powerForm_limit :
    HasLimitAtZero powerForm (Real.exp (1 / 2)) := by
  have hf := f₀_limit
  unfold HasLimitAtZero at hf ⊢
  have he : Tendsto (fun x : ℝ => Real.exp (f₀ x))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (Real.exp (1 / 2))) :=
    (Real.continuous_exp.continuousAt :
      ContinuousAt Real.exp (1 / 2)).tendsto.comp hf
  apply he.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  have hsinh : Real.sinh x ≠ 0 := Real.sinh_ne_zero.mpr hx0
  have hbase : 0 < (1 + Real.exp x) / 2 := by positivity
  have hr :
      Real.rpow ((1 + Real.exp x) / 2) (coth x) =
        Real.exp (Real.log ((1 + Real.exp x) / 2) * coth x) :=
    Real.rpow_def_of_pos hbase (coth x)
  have hlog :
      Real.log ((1 + Real.exp x) / 2) =
        Real.log (1 + Real.exp x) - Real.log 2 := by
    rw [Real.log_div (by positivity) (by norm_num)]
  rw [powerForm, hr, hlog]
  congr 1
  dsimp [f₀, coth]
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp [hsinh, (Real.cosh_pos x).ne']

theorem gap1 : HasLimitAtZero f₀ (1 / 2) ↔ HasLimitAtZero f₁ (1 / 2) := by
  constructor <;> intro _
  · exact f₁_limit
  · exact f₀_limit
theorem gap2 : HasLimitAtZero f₁ (1 / 2) := by exact f₁_limit
theorem gap3 : HasLimitAtZero f₀ (1 / 2) := by exact f₀_limit
theorem gap4 : HasLimitAtZero powerForm (Real.exp (1 / 2)) := by exact powerForm_limit
theorem gap5 : Real.exp (1 / 2) = Real.sqrt (Real.exp 1) := by
  simpa using Real.exp_half 1
theorem gap6 : HasLimitAtZero powerForm (Real.sqrt (Real.exp 1)) := by
  rw [← Real.exp_half 1]
  exact powerForm_limit

end

end ProofGap.Exercise1368

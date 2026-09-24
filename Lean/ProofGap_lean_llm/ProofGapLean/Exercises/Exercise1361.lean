import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise1361

noncomputable section

def HasLimitAtTop (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f Filter.atTop (nhds L)

def f₀ (x : ℝ) : ℝ :=
  x * Real.log ((2 / Real.pi) * Real.arctan x)
def f₁ (x : ℝ) : ℝ :=
  Real.log ((2 / Real.pi) * Real.arctan x) / (1 / x)
def f₂ (x : ℝ) : ℝ :=
  ((Real.pi / (2 * Real.arctan x)) *
      (2 / (Real.pi * (1 + x ^ 2)))) / (-1 / x ^ 2)
def f₃ (x : ℝ) : ℝ := -(x ^ 2 / ((1 + x ^ 2) * Real.arctan x))
def powerForm (x : ℝ) : ℝ :=
  Real.rpow ((2 / Real.pi) * Real.arctan x) x

private theorem fundamental_limits :
    HasLimitAtTop f₀ (-2 / Real.pi) ∧
      HasLimitAtTop f₂ (-2 / Real.pi) ∧
        HasLimitAtTop f₃ (-2 / Real.pi) := by
  unfold HasLimitAtTop
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hinv :
      Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hatan :
      Filter.Tendsto Real.arctan Filter.atTop (nhds (Real.pi / 2)) :=
    Real.tendsto_arctan_atTop.mono_right inf_le_left
  have hden :
      Filter.Tendsto
        (fun x : ℝ => (1 + (x⁻¹) ^ 2) * Real.arctan x)
        Filter.atTop (nhds (Real.pi / 2)) := by
    have hsquare := hinv.pow 2
    have hone :
        Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds (1 : ℝ)) :=
      tendsto_const_nhds
    simpa using (hone.add hsquare).mul hatan
  have hpihalf : Real.pi / 2 ≠ 0 := div_ne_zero hpi (by norm_num)
  have hg :
      Filter.Tendsto
        (fun x : ℝ => -(((1 + (x⁻¹) ^ 2) * Real.arctan x)⁻¹))
        Filter.atTop (nhds (-2 / Real.pi)) := by
    have ht := (hden.inv₀ hpihalf).neg
    convert ht using 1 <;> field_simp [hpi] <;> ring
  have hfg :
      f₃ =ᶠ[Filter.atTop]
        (fun x : ℝ => -(((1 + (x⁻¹) ^ 2) * Real.arctan x)⁻¹)) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    have ha : Real.arctan x ≠ 0 := ne_of_gt (Real.arctan_pos.2 hx)
    have hquad : 1 + x ^ 2 ≠ 0 := by
      nlinarith [sq_nonneg x]
    have hinvquad : 1 + (x⁻¹) ^ 2 ≠ 0 := by
      nlinarith [sq_nonneg (x⁻¹)]
    dsimp [f₃]
    field_simp [hx0, ha, hquad, hinvquad] <;> ring
  have hf3 :
      Filter.Tendsto f₃ Filter.atTop (nhds (-2 / Real.pi)) :=
    Filter.Tendsto.congr' hfg.symm hg
  have hf23 : f₂ =ᶠ[Filter.atTop] f₃ := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    have ha : Real.arctan x ≠ 0 := ne_of_gt (Real.arctan_pos.2 hx)
    have hquad : 1 + x ^ 2 ≠ 0 := by
      nlinarith [sq_nonneg x]
    dsimp [f₂, f₃]
    field_simp [hx0, hpi, ha, hquad] <;> ring
  have hf2 :
      Filter.Tendsto f₂ Filter.atTop (nhds (-2 / Real.pi)) :=
    Filter.Tendsto.congr' hf23.symm hf3
  let h : ℝ → ℝ :=
    fun t => Real.log (1 - (2 / Real.pi) * Real.arctan t)
  have hatanDeriv : HasDerivAt Real.arctan (1 : ℝ) (0 : ℝ) := by
    simpa using Real.hasDerivAt_arctan (0 : ℝ)
  have hscaled :
      HasDerivAt (fun t : ℝ => (2 / Real.pi) * Real.arctan t)
        (2 / Real.pi) 0 := by
    simpa using hatanDeriv.const_mul (2 / Real.pi)
  have hinner :
      HasDerivAt
        (fun t : ℝ => 1 - (2 / Real.pi) * Real.arctan t)
        (-2 / Real.pi) 0 := by
    simpa only [neg_div] using hscaled.const_sub (1 : ℝ)
  have hlog : HasDerivAt Real.log (1 : ℝ) (1 : ℝ) := by
    simpa using Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)
  have hinnerValue :
      1 - (2 / Real.pi) * Real.arctan (0 : ℝ) = (1 : ℝ) := by
    norm_num
  have hlogInner :
      HasDerivAt Real.log (1 : ℝ)
        (1 - (2 / Real.pi) * Real.arctan (0 : ℝ)) := by
    rw [hinnerValue]
    exact hlog
  have hh : HasDerivAt h (-2 / Real.pi) 0 := by
    simpa [h] using hlogInner.comp (0 : ℝ) hinner
  have hslope :
      Filter.Tendsto
        (fun t : ℝ => t⁻¹ * (h t - h 0))
        (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhds (-2 / Real.pi)) := by
    simpa using hh.tendsto_slope_zero
  have hinv_ne :
      ∀ᶠ x : ℝ in Filter.atTop, x⁻¹ ∈ ({0}ᶜ : Set ℝ) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    simp [hx0]
  have hinv_punctured :
      Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop
        (nhdsWithin 0 ({0}ᶜ : Set ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hinv, hinv_ne⟩
  have hslope_top := hslope.comp hinv_punctured
  have hf0eq :
      f₀ =ᶠ[Filter.atTop]
        (fun x : ℝ => (x⁻¹)⁻¹ * (h (x⁻¹) - h 0)) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    have hbase :
        (2 / Real.pi) * Real.arctan x =
          1 - (2 / Real.pi) * Real.arctan (x⁻¹) := by
      rw [Real.arctan_inv_of_pos hx]
      field_simp [hpi] <;> ring
    simp [f₀, h, hbase]
  have hf0 :
      Filter.Tendsto f₀ Filter.atTop (nhds (-2 / Real.pi)) :=
    Filter.Tendsto.congr' hf0eq.symm hslope_top
  exact ⟨hf0, hf2, hf3⟩

theorem gap1 : HasLimitAtTop f₀ (-2 / Real.pi) ↔
    HasLimitAtTop f₁ (-2 / Real.pi) := by
  unfold HasLimitAtTop
  have heq : f₀ =ᶠ[Filter.atTop] f₁ := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    dsimp [f₀, f₁]
    field_simp [hx0]
  constructor
  · intro hf
    exact Filter.Tendsto.congr' heq hf
  · intro hf
    exact Filter.Tendsto.congr' heq.symm hf
theorem gap2 : HasLimitAtTop f₁ (-2 / Real.pi) ↔
    HasLimitAtTop f₂ (-2 / Real.pi) := by
  constructor
  · intro _
    exact fundamental_limits.2.1
  · intro _
    exact gap1.mp fundamental_limits.1
theorem gap3 : HasLimitAtTop f₀ (-2 / Real.pi) ↔
    HasLimitAtTop f₂ (-2 / Real.pi) := by
  exact iff_of_true fundamental_limits.1 fundamental_limits.2.1
theorem gap4 : HasLimitAtTop f₀ (-2 / Real.pi) ↔
    HasLimitAtTop f₃ (-2 / Real.pi) := by
  exact iff_of_true fundamental_limits.1 fundamental_limits.2.2
theorem gap5 : HasLimitAtTop f₃ (-2 / Real.pi) := by
  exact fundamental_limits.2.2
theorem gap6 : HasLimitAtTop f₀ (-2 / Real.pi) := by
  exact fundamental_limits.1
theorem gap7 : HasLimitAtTop powerForm (Real.exp (-2 / Real.pi)) := by
  unfold HasLimitAtTop
  have hf : Filter.Tendsto f₀ Filter.atTop (nhds (-2 / Real.pi)) := gap6
  have hexp :
      Filter.Tendsto (fun x : ℝ => Real.exp (f₀ x)) Filter.atTop
        (nhds (Real.exp (-2 / Real.pi))) :=
    Real.continuous_exp.continuousAt.tendsto.comp hf
  have heq :
      powerForm =ᶠ[Filter.atTop] (fun x : ℝ => Real.exp (f₀ x)) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    have hb : 0 < (2 / Real.pi) * Real.arctan x :=
      mul_pos (div_pos (by norm_num) Real.pi_pos) (Real.arctan_pos.2 hx)
    dsimp [powerForm]
    calc
      Real.rpow ((2 / Real.pi) * Real.arctan x) x =
          Real.exp (Real.log ((2 / Real.pi) * Real.arctan x) * x) :=
        Real.rpow_def_of_pos hb x
      _ = Real.exp (f₀ x) := by
        rw [f₀]
        congr 1
        ring
  exact Filter.Tendsto.congr' heq.symm hexp

end

end ProofGap.Exercise1361

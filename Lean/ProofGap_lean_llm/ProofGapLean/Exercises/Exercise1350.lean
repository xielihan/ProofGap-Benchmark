import ProofGapLean.Prelude.Analysis
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.Tendsto

namespace ProofGap.Exercise1350

noncomputable section

def HasRightLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds L)
def HasLimitAtTop (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f Filter.atTop (nhds L)

def f₀ (x : ℝ) : ℝ := x * Real.log (Real.log (1 / x))
def f₁ (y : ℝ) : ℝ := Real.log (Real.log y) / y
def f₂ (y : ℝ) : ℝ := 1 / (y * Real.log y)
def powerForm (x : ℝ) : ℝ := Real.rpow (Real.log (1 / x)) x

private theorem coreLimits1350 :
    HasLimitAtTop f₁ 0 ∧ HasLimitAtTop f₂ 0 := by
  constructor
  · change Filter.Tendsto (fun y : ℝ => Real.log (Real.log y) / y)
      Filter.atTop (nhds 0)
    have hloglog :
        (fun y : ℝ => Real.log (Real.log y)) =o[Filter.atTop]
          (fun y : ℝ => y) := by
      simpa [Function.comp_def] using
        ((Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop).trans
          Real.isLittleO_log_id_atTop)
    exact hloglog.tendsto_div_nhds_zero
  · change Filter.Tendsto (fun y : ℝ => 1 / (y * Real.log y))
      Filter.atTop (nhds 0)
    have hInv :
        Filter.Tendsto (fun y : ℝ => y⁻¹) Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero
    have hLogInv :
        Filter.Tendsto (fun y : ℝ => (Real.log y)⁻¹)
          Filter.atTop (nhds 0) :=
      hInv.comp Real.tendsto_log_atTop
    simpa [one_div, mul_comm] using hInv.mul hLogInv

theorem gap1 : HasRightLimitAtZero f₀ 0 ↔ HasLimitAtTop f₁ 0 := by
  constructor
  · intro _
    exact coreLimits1350.1
  · intro h
    change Filter.Tendsto f₁ Filter.atTop (nhds 0) at h
    have hInv :
        Filter.Tendsto (fun x : ℝ => 1 / x)
          (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
      simpa [one_div] using
        (tendsto_inv_nhdsGT_zero :
          Filter.Tendsto (fun x : ℝ => x⁻¹)
            (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop)
    have hc :
        Filter.Tendsto (fun x : ℝ => f₁ (1 / x))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      h.comp hInv
    have hcomp : (fun x : ℝ => f₁ (1 / x)) = f₀ := by
      funext x
      change Real.log (Real.log (1 / x)) / (1 / x) =
        x * Real.log (Real.log (1 / x))
      calc
        Real.log (Real.log (1 / x)) / (1 / x) =
            Real.log (Real.log (1 / x)) * x := by
              rw [div_eq_mul_inv]
              simp
        _ = x * Real.log (Real.log (1 / x)) :=
          mul_comm (Real.log (Real.log (1 / x))) x
    rw [hcomp] at hc
    exact hc
theorem gap2 : HasLimitAtTop f₁ 0 ↔ HasLimitAtTop f₂ 0 := by
  constructor
  · intro _
    exact coreLimits1350.2
  · intro _
    exact coreLimits1350.1
theorem gap3 : HasLimitAtTop f₂ 0 := by
  exact coreLimits1350.2
theorem gap4 : HasRightLimitAtZero f₀ 0 := by
  exact gap1.mpr coreLimits1350.1
theorem gap5 : HasRightLimitAtZero powerForm (Real.exp 0) := by
  have hf :
      Filter.Tendsto f₀ (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := gap4
  have hExp :
      Filter.Tendsto (fun x : ℝ => Real.exp (f₀ x))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.exp 0)) :=
    Real.continuous_exp.continuousAt.tendsto.comp hf
  have hInv :
      Filter.Tendsto (fun x : ℝ => 1 / x)
        (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
    simpa [one_div] using
      (tendsto_inv_nhdsGT_zero :
        Filter.Tendsto (fun x : ℝ => x⁻¹)
          (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop)
  have hLog :
      Filter.Tendsto (fun x : ℝ => Real.log (1 / x))
        (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop :=
    Real.tendsto_log_atTop.comp hInv
  have hEventuallyPos : ∀ᶠ y : ℝ in Filter.atTop, 0 < y := by
    refine Filter.eventually_atTop.2 ?_
    exact ⟨1, fun y hy => lt_of_lt_of_le zero_lt_one hy⟩
  have hPos :
      ∀ᶠ x in nhdsWithin 0 (Set.Ioi 0), 0 < Real.log (1 / x) :=
    hLog.eventually hEventuallyPos
  have heq :
      (fun x : ℝ => powerForm x) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        (fun x : ℝ => Real.exp (f₀ x)) := by
    filter_upwards [hPos] with x hx
    calc
      powerForm x =
          Real.exp (Real.log (Real.log (1 / x)) * x) := by
            simpa only [powerForm] using (Real.rpow_def_of_pos hx x)
      _ = Real.exp (f₀ x) := by
            rw [f₀, mul_comm]
  change Filter.Tendsto powerForm (nhdsWithin 0 (Set.Ioi 0))
    (nhds (Real.exp 0))
  exact hExp.congr' heq.symm
theorem gap6 : Real.exp 0 = 1 := by
  exact Real.exp_zero
theorem gap7 : HasRightLimitAtZero powerForm 1 := by
  simpa only [gap6] using gap5

end

end ProofGap.Exercise1350

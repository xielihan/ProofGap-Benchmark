import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise961

noncomputable section

def selfPow (x : ℝ) : ℝ := Real.rpow x x

def tower (x : ℝ) : ℝ := Real.rpow x (selfPow x)

def y (x : ℝ) : ℝ := x + selfPow x + tower x

def expandedDerivative (x : ℝ) : ℝ :=
  1 + selfPow x * (1 + Real.log x) +
    tower x * deriv (fun z : ℝ => selfPow z * Real.log z) x

def finalDerivative (x : ℝ) : ℝ :=
  1 + selfPow x * (1 + Real.log x) +
    selfPow x * tower x *
      (1 / x + Real.log x + Real.log x ^ 2)

private theorem derivativeFacts_of_pos (x : ℝ) (hx : 0 < x) :
    HasDerivAt selfPow (selfPow x * (1 + Real.log x)) x ∧
      HasDerivAt (fun z : ℝ => selfPow z * Real.log z)
        (selfPow x * (1 + Real.log x) * Real.log x +
          selfPow x * (1 / x)) x := by
  have hinner :
      HasDerivAt (fun z : ℝ => Real.log z * z) (1 + Real.log x) x := by
    simpa [one_div, hx.ne'] using
      (Real.hasDerivAt_log hx.ne').mul (hasDerivAt_id x)
  have hraw :
      HasDerivAt (fun z : ℝ => Real.exp (Real.log z * z))
        (selfPow x * (1 + Real.log x)) x := by
    simpa [selfPow, Real.rpow_def_of_pos hx, mul_comm] using hinner.exp
  have hself :
      HasDerivAt selfPow (selfPow x * (1 + Real.log x)) x := by
    refine hraw.congr_of_eventuallyEq ?_
    filter_upwards [eventually_gt_nhds hx] with z hz
    simp [selfPow, Real.rpow_def_of_pos hz]
  have hlog : HasDerivAt Real.log (1 / x) x := by
    simpa [one_div] using Real.hasDerivAt_log hx.ne'
  exact ⟨hself, hself.mul hlog⟩

theorem gap1 (x : ℝ) (hx : 0 < x) :
    HasDerivAt y (expandedDerivative x) x := by
  rcases derivativeFacts_of_pos x hx with ⟨hself, hproduct⟩
  have hraw :
      HasDerivAt (fun z : ℝ => Real.exp (selfPow z * Real.log z))
        (tower x * deriv (fun z : ℝ => selfPow z * Real.log z) x) x := by
    rw [hproduct.deriv]
    simpa [tower, Real.rpow_def_of_pos hx, mul_comm] using hproduct.exp
  have htower :
      HasDerivAt tower
        (tower x * deriv (fun z : ℝ => selfPow z * Real.log z) x) x := by
    refine hraw.congr_of_eventuallyEq ?_
    filter_upwards [eventually_gt_nhds hx] with z hz
    simp [tower, Real.rpow_def_of_pos hz, mul_comm]
  simpa [y, expandedDerivative] using
    ((hasDerivAt_id x).add hself).add htower

theorem gap2 (x : ℝ) (hx : 0 < x) :
    expandedDerivative x = finalDerivative x := by
  have hproduct := (derivativeFacts_of_pos x hx).2
  unfold expandedDerivative finalDerivative
  rw [hproduct.deriv]
  ring

theorem gap3 (x : ℝ) (hx : 0 < x) :
    HasDerivAt y (finalDerivative x) x := by
  rw [← gap2 x hx]
  exact gap1 x hx

end

end ProofGap.Exercise961

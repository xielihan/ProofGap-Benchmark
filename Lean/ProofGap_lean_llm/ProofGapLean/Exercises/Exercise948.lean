import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise948

noncomputable section

def sec (x : ℝ) : ℝ := 1 / Real.cos x
def y (x : ℝ) : ℝ := Real.arctan (Real.tan x ^ 2)

def expandedDerivative (x : ℝ) : ℝ :=
  1 / (1 + Real.tan x ^ 4) * 2 * Real.tan x * sec x ^ 2

def finalDerivative (x : ℝ) : ℝ :=
  Real.sin (2 * x) / (Real.sin x ^ 4 + Real.cos x ^ 4)

theorem gap1 (x : ℝ) (hx : Real.cos x ≠ 0) :
    HasDerivAt y (expandedDerivative x) x := by
  have hpow : (Real.tan x ^ 2) ^ 2 = Real.tan x ^ 4 := by
    ring
  have hsec : 1 / Real.cos x ^ 2 = (1 / Real.cos x) ^ 2 := by
    simp [one_div]
  have hArctan :
      HasDerivAt Real.arctan (1 / (1 + (Real.tan x ^ 2) ^ 2))
        (Real.tan x ^ 2) :=
    Real.hasDerivAt_arctan (Real.tan x ^ 2)
  unfold y expandedDerivative sec
  convert hArctan.comp x ((Real.hasDerivAt_tan hx).pow 2) using 1 <;>
    simp [Function.comp_def, hpow, hsec, mul_assoc]

theorem gap2 (x : ℝ) (hx : Real.cos x ≠ 0) :
    expandedDerivative x = finalDerivative x := by
  have htanDen : 1 + (Real.sin x / Real.cos x) ^ 4 ≠ 0 := by
    positivity
  have hden : Real.sin x ^ 4 + Real.cos x ^ 4 ≠ 0 := by
    positivity
  unfold expandedDerivative finalDerivative sec
  rw [Real.tan_eq_sin_div_cos, Real.sin_two_mul]
  field_simp [hx, htanDen, hden] <;> ring

theorem gap3 (x : ℝ) (hx : Real.cos x ≠ 0) :
    HasDerivAt y (finalDerivative x) x := by
  simpa only [gap2 x hx] using gap1 x hx

end

end ProofGap.Exercise948

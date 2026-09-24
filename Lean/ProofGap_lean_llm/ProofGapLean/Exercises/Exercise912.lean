import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise912

noncomputable section

def sec (x : ℝ) : ℝ := 1 / Real.cos x

def y (x : ℝ) : ℝ :=
  Real.log (Real.tan (x / 2)) -
    Real.cos x * Real.log (Real.tan x)

def expandedDerivative (x : ℝ) : ℝ :=
  1 / Real.tan (x / 2) * sec (x / 2) ^ 2 * (1 / 2) +
    Real.sin x * Real.log (Real.tan x) -
    Real.cos x * (1 / Real.tan x) * sec x ^ 2

def finalDerivative (x : ℝ) : ℝ :=
  Real.sin x * Real.log (Real.tan x)

/-- Source: `proof_gap/exercise_912/1.txt`; positivity of both tangent
arguments gives the logarithm domain and excludes the relevant tangent
poles and zeros. -/
private theorem tan_pos_sin_cos_ne (x : ℝ) (h : 0 < Real.tan x) :
    Real.sin x ≠ 0 ∧ Real.cos x ≠ 0 := by
  constructor
  · intro hs
    have hzero : Real.tan x = 0 := by
      simp [Real.tan_eq_sin_div_cos, hs]
    exact (ne_of_gt h) hzero
  · intro hc
    have hzero : Real.tan x = 0 := by
      simp [Real.tan_eq_sin_div_cos, hc]
    exact (ne_of_gt h) hzero

private theorem hasDerivAt_tan_via_div (x : ℝ) (hcos : Real.cos x ≠ 0) :
    HasDerivAt Real.tan (sec x ^ 2) x := by
  have hquot :
      HasDerivAt (fun t : ℝ => Real.sin t / Real.cos t)
        ((Real.cos x * Real.cos x - Real.sin x * (-Real.sin x)) /
          Real.cos x ^ 2) x :=
    (Real.hasDerivAt_sin x).div (Real.hasDerivAt_cos x) hcos
  have hnum :
      Real.cos x * Real.cos x - Real.sin x * (-Real.sin x) = 1 := by
    calc
      Real.cos x * Real.cos x - Real.sin x * (-Real.sin x) =
          Real.sin x ^ 2 + Real.cos x ^ 2 := by ring
      _ = 1 := Real.sin_sq_add_cos_sq x
  have hcoeff :
      (Real.cos x * Real.cos x - Real.sin x * (-Real.sin x)) /
          Real.cos x ^ 2 = sec x ^ 2 := by
    rw [hnum]
    simp [sec]
  rw [hcoeff] at hquot
  have hfun : Real.tan = (fun t : ℝ => Real.sin t / Real.cos t) := by
    funext t
    rw [Real.tan_eq_sin_div_cos]
  rw [hfun]
  exact hquot

theorem gap1 (x : ℝ) (hhalf : 0 < Real.tan (x / 2))
    (hfull : 0 < Real.tan x) :
    HasDerivAt y (expandedDerivative x) x := by
  have hcoshalf := (tan_pos_sin_cos_ne (x / 2) hhalf).2
  have hcosfull := (tan_pos_sin_cos_ne x hfull).2
  have htanhalf :
      HasDerivAt (fun t : ℝ => Real.tan (t / 2))
        (sec (x / 2) ^ 2 * (1 / 2)) x := by
    simpa [Function.comp_def, one_div, mul_assoc] using
      (hasDerivAt_tan_via_div (x / 2) hcoshalf).comp x
        ((hasDerivAt_id x).div_const 2)
  have htanfull : HasDerivAt Real.tan (sec x ^ 2) x :=
    hasDerivAt_tan_via_div x hcosfull
  have hloghalf :
      HasDerivAt (fun t : ℝ => Real.log (Real.tan (t / 2)))
        (1 / Real.tan (x / 2) * sec (x / 2) ^ 2 * (1 / 2)) x := by
    simpa [Function.comp_def, one_div, mul_assoc] using
      (Real.hasDerivAt_log (ne_of_gt hhalf)).comp x htanhalf
  have hlogfull :
      HasDerivAt (fun t : ℝ => Real.log (Real.tan t))
        (1 / Real.tan x * sec x ^ 2) x := by
    simpa [Function.comp_def, one_div] using
      (Real.hasDerivAt_log (ne_of_gt hfull)).comp x htanfull
  have hproduct :
      HasDerivAt (fun t : ℝ => Real.cos t * Real.log (Real.tan t))
        ((-Real.sin x) * Real.log (Real.tan x) +
          Real.cos x * (1 / Real.tan x * sec x ^ 2)) x :=
    (Real.hasDerivAt_cos x).mul hlogfull
  convert hloghalf.sub hproduct using 1 <;>
    simp [y, expandedDerivative] <;> ring

/-- Source: `proof_gap/exercise_912/2.txt`; the trigonometric cancellation is
restricted to the domain of both logarithms. -/
theorem gap2 (x : ℝ) (hhalf : 0 < Real.tan (x / 2))
    (hfull : 0 < Real.tan x) :
    expandedDerivative x = finalDerivative x := by
  have hsinhalf := (tan_pos_sin_cos_ne (x / 2) hhalf).1
  have hcoshalf := (tan_pos_sin_cos_ne (x / 2) hhalf).2
  have hcosfull := (tan_pos_sin_cos_ne x hfull).2
  have hsin_double :
      Real.sin x = 2 * Real.sin (x / 2) * Real.cos (x / 2) := by
    calc
      Real.sin x = Real.sin (2 * (x / 2)) := by
        apply congrArg Real.sin
        ring
      _ = 2 * Real.sin (x / 2) * Real.cos (x / 2) := by
        rw [Real.sin_two_mul]
  have hcancel :
      1 / Real.tan (x / 2) * sec (x / 2) ^ 2 * (1 / 2) =
        Real.cos x * (1 / Real.tan x) * sec x ^ 2 := by
    simp only [Real.tan_eq_sin_div_cos, sec]
    rw [hsin_double]
    field_simp [hcoshalf, hcosfull, hsinhalf] <;> ring
  unfold expandedDerivative finalDerivative
  rw [hcancel]
  ring

/-- Source: `proof_gap/exercise_912/3.txt`; retain the domain of both
logarithmic tangent terms. -/
theorem gap3 (x : ℝ) (hhalf : 0 < Real.tan (x / 2))
    (hfull : 0 < Real.tan x) :
    HasDerivAt y (finalDerivative x) x := by
  rw [← gap2 x hhalf hfull]
  exact gap1 x hhalf hfull

end

end ProofGap.Exercise912

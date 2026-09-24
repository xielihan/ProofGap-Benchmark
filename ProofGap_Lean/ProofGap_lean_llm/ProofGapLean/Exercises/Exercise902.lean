import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise902

noncomputable section

def angle (x : ℝ) : ℝ := x / 2 + Real.pi / 4
def sec (x : ℝ) : ℝ := 1 / Real.cos x
def y (x : ℝ) : ℝ := Real.log (Real.tan (angle x))

def expandedDerivative (x : ℝ) : ℝ :=
  (1 / Real.tan (angle x)) * sec (angle x) ^ 2 * (1 / 2 : ℝ)

def productDerivative (x : ℝ) : ℝ :=
  1 / (2 * Real.sin (angle x) * Real.cos (angle x))

def shiftedDerivative (x : ℝ) : ℝ :=
  1 / Real.sin (x + Real.pi / 2)

def finalDerivative (x : ℝ) : ℝ := 1 / Real.cos x

theorem gap1 (x : ℝ) (htan : 0 < Real.tan (angle x))
    (hsin : Real.sin (angle x) ≠ 0) (hcos : Real.cos (angle x) ≠ 0) :
    deriv y x = expandedDerivative x := by
  have hangle : HasDerivAt angle (1 / 2 : ℝ) x := by
    simpa [angle, div_eq_mul_inv] using
      (((hasDerivAt_id x).mul_const (2 : ℝ)⁻¹).add
        (hasDerivAt_const x (Real.pi / 4)))
  have hsin' : HasDerivAt (fun z : ℝ => Real.sin (angle z))
      (Real.cos (angle x) * (1 / 2 : ℝ)) x :=
    (Real.hasDerivAt_sin (angle x)).comp x hangle
  have hcos' : HasDerivAt (fun z : ℝ => Real.cos (angle z))
      ((-Real.sin (angle x)) * (1 / 2 : ℝ)) x :=
    (Real.hasDerivAt_cos (angle x)).comp x hangle
  have hquot : HasDerivAt
      (fun z : ℝ => Real.sin (angle z) / Real.cos (angle z))
      (((Real.cos (angle x) * (1 / 2 : ℝ)) * Real.cos (angle x) -
          Real.sin (angle x) * ((-Real.sin (angle x)) * (1 / 2 : ℝ))) /
        Real.cos (angle x) ^ 2) x :=
    hsin'.div hcos' hcos
  have hcoeff :
      (((Real.cos (angle x) * (1 / 2 : ℝ)) * Real.cos (angle x) -
          Real.sin (angle x) * ((-Real.sin (angle x)) * (1 / 2 : ℝ))) /
        Real.cos (angle x) ^ 2) =
      (1 / Real.cos (angle x) ^ 2) * (1 / 2 : ℝ) := by
    field_simp [hcos]
    nlinarith [Real.sin_sq_add_cos_sq (angle x)]
  rw [hcoeff] at hquot
  have htan' : HasDerivAt (fun z : ℝ => Real.tan (angle z))
      ((1 / Real.cos (angle x) ^ 2) * (1 / 2 : ℝ)) x := by
    simpa only [Real.tan_eq_sin_div_cos] using hquot
  have hlogOuter : HasDerivAt Real.log (Real.tan (angle x))⁻¹
      (Real.tan (angle x)) :=
    Real.hasDerivAt_log (ne_of_gt htan)
  have hlog' : HasDerivAt
      (fun z : ℝ => Real.log (Real.tan (angle z)))
      ((Real.tan (angle x))⁻¹ *
        ((1 / Real.cos (angle x) ^ 2) * (1 / 2 : ℝ))) x := by
    simpa only [Function.comp_apply] using hlogOuter.comp x htan'
  change deriv (fun z : ℝ => Real.log (Real.tan (angle z))) x = expandedDerivative x
  simpa [expandedDerivative, sec, one_div, inv_pow, mul_assoc] using hlog'.deriv

theorem gap2 (x : ℝ) (htan : 0 < Real.tan (angle x))
    (hsin : Real.sin (angle x) ≠ 0) (hcos : Real.cos (angle x) ≠ 0) :
    expandedDerivative x = productDerivative x := by
  unfold expandedDerivative productDerivative sec
  rw [Real.tan_eq_sin_div_cos]
  field_simp [hsin, hcos] <;> ring

theorem gap3 (x : ℝ) (htan : 0 < Real.tan (angle x))
    (hsin : Real.sin (angle x) ≠ 0) (hcos : Real.cos (angle x) ≠ 0) :
    productDerivative x = shiftedDerivative x := by
  have hangle : 2 * angle x = x + Real.pi / 2 := by
    unfold angle
    ring
  unfold productDerivative shiftedDerivative
  rw [← Real.sin_two_mul, hangle]

theorem gap4 (x : ℝ) (htan : 0 < Real.tan (angle x))
    (hsin : Real.sin (angle x) ≠ 0) (hcos : Real.cos (angle x) ≠ 0) :
    deriv y x = shiftedDerivative x := by
  calc
    deriv y x = expandedDerivative x := gap1 x htan hsin hcos
    _ = productDerivative x := gap2 x htan hsin hcos
    _ = shiftedDerivative x := gap3 x htan hsin hcos

theorem gap5 (x : ℝ) (htan : 0 < Real.tan (angle x))
    (hsin : Real.sin (angle x) ≠ 0) (hcos : Real.cos (angle x) ≠ 0) :
    deriv y x = finalDerivative x := by
  calc
    deriv y x = shiftedDerivative x := gap4 x htan hsin hcos
    _ = finalDerivative x := by
      unfold shiftedDerivative finalDerivative
      rw [Real.sin_add_pi_div_two]

end

end ProofGap.Exercise902

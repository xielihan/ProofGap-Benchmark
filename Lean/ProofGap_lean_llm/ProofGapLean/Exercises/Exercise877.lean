import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise877

noncomputable section

def sec (x : ℝ) : ℝ := 1 / Real.cos x
def y (x : ℝ) : ℝ := Real.rpow 2 (Real.tan (1 / x))

theorem gap1 (x : ℝ) (hx : x ≠ 0) (hcos : Real.cos (1 / x) ≠ 0) :
    deriv y x =
      -(1 / x ^ 2) * sec (1 / x) ^ 2 *
        Real.rpow 2 (Real.tan (1 / x)) * Real.log 2 := by
  unfold y sec
  have htwo : (0 : ℝ) < 2 := by norm_num
  have hrecip :
      HasDerivAt (fun z : ℝ => 1 / z) (-(1 / x ^ 2)) x := by
    convert
      (hasDerivAt_const x (1 : ℝ)).div (hasDerivAt_id x) hx using 1 <;>
      simp only [id_eq] <;>
      ring
  have htan_base :
      HasDerivAt Real.tan (1 / Real.cos (1 / x) ^ 2) (1 / x) := by
    have hs :
        HasDerivAt (fun z : ℝ => Real.sin z / Real.cos z)
          ((Real.cos (1 / x) * Real.cos (1 / x) -
              Real.sin (1 / x) * (-Real.sin (1 / x))) /
            Real.cos (1 / x) ^ 2) (1 / x) :=
      (Real.hasDerivAt_sin (1 / x)).div
        (Real.hasDerivAt_cos (1 / x)) hcos
    have htrig :
        Real.cos (1 / x) * Real.cos (1 / x) -
            Real.sin (1 / x) * (-Real.sin (1 / x)) = 1 := by
      calc
        Real.cos (1 / x) * Real.cos (1 / x) -
              Real.sin (1 / x) * (-Real.sin (1 / x)) =
            Real.sin (1 / x) ^ 2 + Real.cos (1 / x) ^ 2 := by ring
        _ = 1 := Real.sin_sq_add_cos_sq (1 / x)
    rw [htrig] at hs
    convert hs using 1
    funext z
    exact Real.tan_eq_sin_div_cos z
  have htan :
      HasDerivAt (fun z : ℝ => Real.tan (1 / z))
        ((1 / Real.cos (1 / x) ^ 2) * (-(1 / x ^ 2))) x := by
    simpa only [Function.comp_apply] using htan_base.comp x hrecip
  have hmul :
      HasDerivAt (fun z : ℝ => Real.log 2 * Real.tan (1 / z))
        (Real.log 2 * ((1 / Real.cos (1 / x) ^ 2) * (-(1 / x ^ 2)))) x := by
    simpa only [zero_mul, zero_add] using
      (hasDerivAt_const x (Real.log 2)).mul htan
  have hexp :
      HasDerivAt
        (fun z : ℝ => Real.exp (Real.log 2 * Real.tan (1 / z)))
        (Real.exp (Real.log 2 * Real.tan (1 / x)) *
          (Real.log 2 * ((1 / Real.cos (1 / x) ^ 2) * (-(1 / x ^ 2))))) x := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_exp (Real.log 2 * Real.tan (1 / x))).comp x hmul
  have hfun :
      (fun z : ℝ => Real.rpow 2 (Real.tan (1 / z))) =
        fun z : ℝ => Real.exp (Real.log 2 * Real.tan (1 / z)) := by
    funext z
    exact Real.rpow_def_of_pos htwo (Real.tan (1 / z))
  have hrpow :
      Real.rpow (2 : ℝ) (Real.tan (1 / x)) =
        Real.exp (Real.log 2 * Real.tan (1 / x)) :=
    Real.rpow_def_of_pos htwo (Real.tan (1 / x))
  rw [hfun, hexp.deriv, hrpow]
  field_simp [hx, hcos] <;> ring

end

end ProofGap.Exercise877

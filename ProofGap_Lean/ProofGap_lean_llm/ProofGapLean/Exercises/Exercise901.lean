import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise901

noncomputable section

def half (x : ℝ) : ℝ := x / 2
def sec (x : ℝ) : ℝ := 1 / Real.cos x
def y (x : ℝ) : ℝ := Real.log (Real.tan (half x))

def expandedDerivative (x : ℝ) : ℝ :=
  (1 / Real.tan (half x)) * sec (half x) ^ 2 * (1 / 2 : ℝ)

def productDerivative (x : ℝ) : ℝ :=
  1 / (2 * Real.sin (half x) * Real.cos (half x))

def finalDerivative (x : ℝ) : ℝ := 1 / Real.sin x

theorem gap1 (x : ℝ) (htan : 0 < Real.tan (half x))
    (hsin : Real.sin (half x) ≠ 0) (hcos : Real.cos (half x) ≠ 0) :
    deriv y x = expandedDerivative x := by
  have hhalf : HasDerivAt half (1 / 2 : ℝ) x := by
    simpa [half, div_eq_mul_inv] using
      (hasDerivAt_id x).mul_const (1 / 2 : ℝ)
  have hnum :
      Real.cos (half x) * Real.cos (half x) -
          Real.sin (half x) * (-Real.sin (half x)) = 1 := by
    calc
      Real.cos (half x) * Real.cos (half x) -
          Real.sin (half x) * (-Real.sin (half x)) =
          Real.sin (half x) ^ 2 + Real.cos (half x) ^ 2 := by ring
      _ = 1 := Real.sin_sq_add_cos_sq (half x)
  have htan_base :
      HasDerivAt Real.tan (1 / Real.cos (half x) ^ 2) (half x) := by
    have hquot :=
      (Real.hasDerivAt_sin (half x)).div
        (Real.hasDerivAt_cos (half x)) hcos
    have htan_fun : Real.tan = Real.sin / Real.cos := by
      funext z
      exact Real.tan_eq_sin_div_cos z
    rw [htan_fun]
    simpa only [hnum] using hquot
  have htan_comp :
      HasDerivAt (fun z : ℝ => Real.tan (half z))
        ((1 / Real.cos (half x) ^ 2) * (1 / 2 : ℝ)) x :=
    htan_base.comp x hhalf
  have hlog_comp :
      HasDerivAt y
        ((1 / Real.tan (half x)) *
          ((1 / Real.cos (half x) ^ 2) * (1 / 2 : ℝ))) x := by
    simpa [y] using
      (Real.hasDerivAt_log (x := Real.tan (half x)) (ne_of_gt htan)).comp x htan_comp
  simpa [expandedDerivative, sec, one_div, mul_assoc] using hlog_comp.deriv

theorem gap2 (x : ℝ) (htan : 0 < Real.tan (half x))
    (hsin : Real.sin (half x) ≠ 0) (hcos : Real.cos (half x) ≠ 0) :
    expandedDerivative x = productDerivative x := by
  unfold expandedDerivative productDerivative sec
  rw [Real.tan_eq_sin_div_cos]
  field_simp [hsin, hcos]

theorem gap3 (x : ℝ) (htan : 0 < Real.tan (half x))
    (hsin : Real.sin (half x) ≠ 0) (hcos : Real.cos (half x) ≠ 0) :
    productDerivative x = finalDerivative x := by
  have hdouble :
      Real.sin x = 2 * Real.sin (half x) * Real.cos (half x) := by
    calc
      Real.sin x = Real.sin (2 * half x) := by
        congr 1
        unfold half
        ring
      _ = 2 * Real.sin (half x) * Real.cos (half x) :=
        Real.sin_two_mul (half x)
  unfold productDerivative finalDerivative
  rw [hdouble]

theorem gap4 (x : ℝ) (htan : 0 < Real.tan (half x))
    (hsin : Real.sin (half x) ≠ 0) (hcos : Real.cos (half x) ≠ 0) :
    deriv y x = finalDerivative x := by
  calc
    deriv y x = expandedDerivative x := gap1 x htan hsin hcos
    _ = productDerivative x := gap2 x htan hsin hcos
    _ = finalDerivative x := gap3 x htan hsin hcos

end

end ProofGap.Exercise901

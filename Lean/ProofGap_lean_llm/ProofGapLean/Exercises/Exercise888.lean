import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise888

noncomputable section

def inner (x : ℝ) : ℝ := Real.log ((Real.log x) ^ 3)
def y (x : ℝ) : ℝ := Real.log (inner x ^ 2)

def expandedDerivative (x : ℝ) : ℝ :=
  (1 / inner x ^ 2) * 2 * inner x *
    (1 / Real.log x ^ 3) * 3 * Real.log x ^ 2 * (1 / x)

def finalDerivative (x : ℝ) : ℝ :=
  6 / (x * Real.log x * inner x)

theorem gap1 (x : ℝ) (hx : 0 < x) (hlogx : 0 < Real.log x)
    (hinner : inner x ≠ 0) :
    deriv y x = expandedDerivative x := by
  have hinnerDeriv :
      HasDerivAt inner
        ((1 / Real.log x ^ 3) *
          (3 * Real.log x ^ 2 * (1 / x))) x := by
    simpa only [inner, one_div, Function.comp_apply] using
      (Real.hasDerivAt_log
        (pow_ne_zero 3 (ne_of_gt hlogx))).comp x
          ((Real.hasDerivAt_log (ne_of_gt hx)).pow 3)
  have hyDeriv :
      HasDerivAt y
        ((1 / inner x ^ 2) *
          (2 * inner x *
            ((1 / Real.log x ^ 3) *
              (3 * Real.log x ^ 2 * (1 / x))))) x := by
    simpa only [y, one_div, Function.comp_apply, Nat.reduceSub, pow_one] using
      (Real.hasDerivAt_log (pow_ne_zero 2 hinner)).comp x
        (hinnerDeriv.pow 2)
  calc
    deriv y x =
        (1 / inner x ^ 2) *
          (2 * inner x *
            ((1 / Real.log x ^ 3) *
              (3 * Real.log x ^ 2 * (1 / x)))) := hyDeriv.deriv
    _ = expandedDerivative x := by
      unfold expandedDerivative
      ring

theorem gap2 (x : ℝ) (hx : 0 < x) (hlogx : 0 < Real.log x)
    (hinner : inner x ≠ 0) :
    expandedDerivative x = finalDerivative x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hlogx0 : Real.log x ≠ 0 := ne_of_gt hlogx
  unfold expandedDerivative finalDerivative
  field_simp [hx0, hlogx0, hinner] <;> ring

theorem gap3 (x : ℝ) (hx : 0 < x) (hlogx : 0 < Real.log x)
    (hinner : inner x ≠ 0) :
    deriv y x = finalDerivative x := by
  calc
    deriv y x = expandedDerivative x := gap1 x hx hlogx hinner
    _ = finalDerivative x := gap2 x hx hlogx hinner

end

end ProofGap.Exercise888

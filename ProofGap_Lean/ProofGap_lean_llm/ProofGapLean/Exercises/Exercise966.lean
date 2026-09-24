import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise966

noncomputable section

def y (x : ℝ) : ℝ := Real.logb x (Real.exp 1)
def reciprocalLog (x : ℝ) : ℝ := 1 / Real.log x
def expandedDerivative (x : ℝ) : ℝ := -(1 / (x * Real.log x ^ 2))
def finalDerivative (x : ℝ) : ℝ := -(1 / x) * y x ^ 2

theorem gap1 (x : ℝ) (hx : 0 < x) (hx1 : x ≠ 1) :
    y x = reciprocalLog x := by
  rw [y, reciprocalLog, Real.logb]
  norm_num

theorem gap2 (x : ℝ) (hx : 0 < x) (hx1 : x ≠ 1) :
    HasDerivAt y (expandedDerivative x) x := by
  have hlog : Real.log x ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hx hx1
  have hy : y = fun z => (Real.log z)⁻¹ := by
    funext z
    simp [y, Real.logb]
  rw [hy]
  unfold expandedDerivative
  convert (Real.hasDerivAt_log hx.ne').inv hlog using 1
  field_simp [hx.ne', hlog]

theorem gap3 (x : ℝ) (hx : 0 < x) (hx1 : x ≠ 1) :
    expandedDerivative x = finalDerivative x := by
  rw [expandedDerivative, finalDerivative, gap1 x hx hx1]
  unfold reciprocalLog
  field_simp

theorem gap4 (x : ℝ) (hx : 0 < x) (hx1 : x ≠ 1) :
    HasDerivAt y (finalDerivative x) x := by
  rw [← gap3 x hx hx1]
  exact gap2 x hx hx1

end

end ProofGap.Exercise966

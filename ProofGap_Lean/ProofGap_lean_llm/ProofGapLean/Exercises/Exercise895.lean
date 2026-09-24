import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise895

noncomputable section

def y (x : ℝ) : ℝ := Real.log (x + Real.sqrt (x ^ 2 + 1))

def expandedDerivative (x : ℝ) : ℝ :=
  (1 / (x + Real.sqrt (1 + x ^ 2))) *
    (1 + x / Real.sqrt (x ^ 2 + 1))

def finalDerivative (x : ℝ) : ℝ := 1 / Real.sqrt (x ^ 2 + 1)

private theorem radicandPositive (x : ℝ) : 0 < x ^ 2 + 1 := by
  nlinarith [sq_nonneg x]

private theorem sqrtPositive (x : ℝ) : 0 < Real.sqrt (x ^ 2 + 1) := by
  exact Real.sqrt_pos.2 (radicandPositive x)

private theorem innerPositive (x : ℝ) :
    0 < x + Real.sqrt (x ^ 2 + 1) := by
  have hspos : 0 < Real.sqrt (x ^ 2 + 1) := sqrtPositive x
  have hs_sq : (Real.sqrt (x ^ 2 + 1)) ^ 2 = x ^ 2 + 1 :=
    Real.sq_sqrt (le_of_lt (radicandPositive x))
  by_contra h
  have hsum : x + Real.sqrt (x ^ 2 + 1) ≤ 0 := le_of_not_gt h
  have hleft : 0 ≤ -x - Real.sqrt (x ^ 2 + 1) := by
    linarith
  have hright : 0 ≤ Real.sqrt (x ^ 2 + 1) - x := by
    linarith
  have hmul :
      0 ≤ (-x - Real.sqrt (x ^ 2 + 1)) *
        (Real.sqrt (x ^ 2 + 1) - x) :=
    mul_nonneg hleft hright
  nlinarith

private theorem hasDerivAtSqrtRadicand (x : ℝ) :
    HasDerivAt (fun t : ℝ => Real.sqrt (t ^ 2 + 1))
      (x / Real.sqrt (x ^ 2 + 1)) x := by
  have hrad : HasDerivAt (fun t : ℝ => t ^ 2 + 1) (2 * x) x := by
    simpa [mul_comm, two_mul] using
      ((hasDerivAt_id x).pow 2).add_const 1
  have hcoef :
      (1 / (2 * Real.sqrt (x ^ 2 + 1))) * (2 * x) =
        x / Real.sqrt (x ^ 2 + 1) := by
    field_simp [ne_of_gt (sqrtPositive x)] <;> ring
  simpa only [Function.comp_apply, hcoef] using
    ((Real.hasDerivAt_sqrt (ne_of_gt (radicandPositive x))).comp x hrad)

private theorem hasDerivAtExpanded (x : ℝ) :
    HasDerivAt y (expandedDerivative x) x := by
  have hinner :
      HasDerivAt (fun t : ℝ => t + Real.sqrt (t ^ 2 + 1))
        (1 + x / Real.sqrt (x ^ 2 + 1)) x := by
    simpa using (hasDerivAt_id x).add (hasDerivAtSqrtRadicand x)
  have hlog :=
    (Real.hasDerivAt_log (ne_of_gt (innerPositive x))).comp x hinner
  unfold y expandedDerivative
  rw [show 1 + x ^ 2 = x ^ 2 + 1 by ring]
  simpa [one_div, Function.comp_apply] using hlog

private theorem expandedEqualsFinal (x : ℝ) :
    expandedDerivative x = finalDerivative x := by
  unfold expandedDerivative finalDerivative
  rw [show 1 + x ^ 2 = x ^ 2 + 1 by ring]
  field_simp [ne_of_gt (sqrtPositive x), ne_of_gt (innerPositive x)]
  ring

theorem gap1 (x : ℝ) : deriv y x = expandedDerivative x := by
  exact (hasDerivAtExpanded x).deriv
theorem gap2 (x : ℝ) : expandedDerivative x = finalDerivative x := by
  exact expandedEqualsFinal x
theorem gap3 (x : ℝ) : deriv y x = finalDerivative x := by
  calc
    deriv y x = expandedDerivative x := gap1 x
    _ = finalDerivative x := gap2 x

end

end ProofGap.Exercise895

import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise910

noncomputable section

def inner (x : ℝ) : ℝ :=
  1 / x + Real.log (1 / x)

def outer (x : ℝ) : ℝ :=
  1 / x + Real.log (inner x)

def y (x : ℝ) : ℝ :=
  Real.log (outer x)

def expandedDerivative (x : ℝ) : ℝ :=
  1 / outer x *
    (-1 / x ^ 2 + 1 / inner x * (-1 / x ^ 2 - 1 / x))

def finalDerivative (x : ℝ) : ℝ :=
  -(1 + x + 1 / x + Real.log (1 / x)) /
    ((1 + x * Real.log (1 / x)) * (1 + x * Real.log (inner x)))

/-- Exercise 910, gap 1; all three nested logarithms are
restricted to positive arguments. -/
theorem gap1 (x : ℝ) (hx : 0 < x)
    (hinner : 0 < inner x) (houter : 0 < outer x) :
    HasDerivAt y (expandedDerivative x) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hrecip0 : (1 / x : ℝ) ≠ 0 := div_ne_zero one_ne_zero hx0
  have hRecip :
      HasDerivAt (fun z : ℝ => 1 / z) (-1 / x ^ 2) x := by
    simpa [one_div] using (hasDerivAt_id x).inv hx0
  have hLogRecip :
      HasDerivAt (fun z : ℝ => Real.log (1 / z)) (-1 / x) x := by
    convert (Real.hasDerivAt_log hrecip0).comp x hRecip using 1 <;>
      field_simp [hx0] <;> ring
  have hInner :
      HasDerivAt inner (-1 / x ^ 2 - 1 / x) x := by
    change HasDerivAt
      (fun z : ℝ => 1 / z + Real.log (1 / z))
      (-1 / x ^ 2 - 1 / x) x
    simpa only [sub_eq_add_neg, neg_div] using hRecip.add hLogRecip
  have hLogInner :
      HasDerivAt (fun z : ℝ => Real.log (inner z))
        (1 / inner x * (-1 / x ^ 2 - 1 / x)) x := by
    simpa [one_div] using
      (Real.hasDerivAt_log (ne_of_gt hinner)).comp x hInner
  have hOuter :
      HasDerivAt outer
        (-1 / x ^ 2 + 1 / inner x * (-1 / x ^ 2 - 1 / x)) x := by
    change HasDerivAt
      (fun z : ℝ => 1 / z + Real.log (inner z))
      (-1 / x ^ 2 + 1 / inner x * (-1 / x ^ 2 - 1 / x)) x
    exact hRecip.add hLogInner
  simpa [y, expandedDerivative, one_div] using
    (Real.hasDerivAt_log (ne_of_gt houter)).comp x hOuter

/-- Exercise 910, gap 2; retain the full nested-logarithm
domain while simplifying the derivative. -/
theorem gap2 (x : ℝ) (hx : 0 < x)
    (hinner : 0 < inner x) (houter : 0 < outer x) :
    HasDerivAt y (finalDerivative x) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hi0 : inner x ≠ 0 := ne_of_gt hinner
  have ho0 : outer x ≠ 0 := ne_of_gt houter
  have hinnerFactor :
      1 + x * Real.log (1 / x) = x * inner x := by
    rw [inner]
    field_simp [hx0]
  have houterFactor :
      1 + x * Real.log (inner x) = x * outer x := by
    rw [outer]
    field_simp [hx0]
  have hnumerator :
      1 + x + 1 / x + Real.log (1 / x) = 1 + x + inner x := by
    rw [inner]
    ring
  have hDerivative : expandedDerivative x = finalDerivative x := by
    rw [expandedDerivative, finalDerivative, hinnerFactor, houterFactor,
      hnumerator]
    field_simp [hx0, hi0, ho0] <;> ring
  rw [← hDerivative]
  exact gap1 x hx hinner houter

end

end ProofGap.Exercise910

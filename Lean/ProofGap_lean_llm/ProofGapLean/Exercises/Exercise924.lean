import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise924

noncomputable section

def y (x : ℝ) : ℝ :=
  Real.arccos (Real.sqrt (1 - x ^ 2))

def expandedDerivative (x : ℝ) : ℝ :=
  (-1 / Real.sqrt (1 - (1 - x ^ 2))) *
    (-x / Real.sqrt (1 - x ^ 2))

def finalDerivative (x : ℝ) : ℝ :=
  Real.sign x / Real.sqrt (1 - x ^ 2)

/-- Exercise 924, gap 1; require `|x| < 1` for the inner
square root and `x ≠ 0` to avoid the outer arccosine endpoint. -/
theorem gap1 (x : ℝ) (hinside : x ^ 2 < 1) (hx : x ≠ 0) :
    HasDerivAt y (expandedDerivative x) x := by
  have hu : 0 < 1 - x ^ 2 := sub_pos.mpr hinside
  have hu0 : 1 - x ^ 2 ≠ 0 := ne_of_gt hu
  have hs0 : Real.sqrt (1 - x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hu)
  have hs_sq : (Real.sqrt (1 - x ^ 2)) ^ 2 = 1 - x ^ 2 :=
    Real.sq_sqrt (le_of_lt hu)
  have hzneg : Real.sqrt (1 - x ^ 2) ≠ -1 := by
    intro h
    nlinarith [Real.sqrt_nonneg (1 - x ^ 2)]
  have hx2pos : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  have hzone : Real.sqrt (1 - x ^ 2) ≠ 1 := by
    intro h
    nlinarith [hs_sq, hx2pos]
  have hone : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 x :=
    hasDerivAt_const x 1
  have hsquare : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
    simpa [pow_two, two_mul] using
      (hasDerivAt_id x).mul (hasDerivAt_id x)
  have hpoly :
      HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-2 * x) x := by
    simpa only [zero_sub, neg_mul] using hone.sub hsquare
  have hinnerRaw :
      HasDerivAt (Real.sqrt ∘ fun t : ℝ => 1 - t ^ 2)
        ((1 / (2 * Real.sqrt (1 - x ^ 2))) * (-2 * x)) x :=
    (Real.hasDerivAt_sqrt hu0).comp x hpoly
  have hcoeff :
      (1 / (2 * Real.sqrt (1 - x ^ 2))) * (-2 * x) =
        -x / Real.sqrt (1 - x ^ 2) := by
    field_simp [hs0]
  rw [hcoeff] at hinnerRaw
  have hinner :
      HasDerivAt (fun t : ℝ => Real.sqrt (1 - t ^ 2))
        (-x / Real.sqrt (1 - x ^ 2)) x := by
    simpa only [Function.comp_apply] using hinnerRaw
  have houter :
      HasDerivAt Real.arccos
        (-(1 / Real.sqrt (1 - (Real.sqrt (1 - x ^ 2)) ^ 2)))
        (Real.sqrt (1 - x ^ 2)) :=
    Real.hasDerivAt_arccos hzneg hzone
  simpa only [y, expandedDerivative, Function.comp_apply, hs_sq, neg_div] using
    houter.comp x hinner

/-- Exercise 924, gap 2; the nonzero hypothesis justifies
replacing `x / sqrt (x²)` by `sign x`. -/
theorem gap2 (x : ℝ) (hinside : x ^ 2 < 1) (hx : x ≠ 0) :
    expandedDerivative x = finalDerivative x := by
  have hs0 : Real.sqrt (1 - x ^ 2) ≠ 0 := by
    apply ne_of_gt
    exact Real.sqrt_pos.2 (sub_pos.mpr hinside)
  have hrad : 1 - (1 - x ^ 2) = x ^ 2 := by
    ring
  unfold expandedDerivative finalDerivative
  rw [hrad, Real.sqrt_sq_eq_abs]
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · rw [abs_of_neg hxneg, Real.sign_of_neg hxneg]
    field_simp [hx, hs0]
  · rw [abs_of_pos hxpos, Real.sign_of_pos hxpos]
    field_simp [hx, hs0]

/-- Exercise 924, gap 3; the composition has a cusp at
zero and singular square-root derivatives at the endpoints. -/
theorem gap3 (x : ℝ) (hinside : x ^ 2 < 1) (hx : x ≠ 0) :
    HasDerivAt y (finalDerivative x) x := by
  rw [← gap2 x hinside hx]
  exact gap1 x hinside hx

end

end ProofGap.Exercise924

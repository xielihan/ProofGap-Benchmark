import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise917

noncomputable section

def y (x : ℝ) : ℝ :=
  Real.sqrt x - Real.arctan (Real.sqrt x)

def expandedDerivative (x : ℝ) : ℝ :=
  1 / (2 * Real.sqrt x) - 1 / (2 * Real.sqrt x * (1 + x))

def finalDerivative (x : ℝ) : ℝ :=
  Real.sqrt x / (2 * (1 + x))

/-- Exercise 917, gap 1; the displayed square-root
derivative is valid for `x > 0`. -/
theorem gap1 (x : ℝ) (hx : 0 < x) :
    HasDerivAt y (expandedDerivative x) x := by
  have hsqrt_ne : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hx).ne'
  have hone : 1 + x ≠ 0 := by
    linarith
  have hsqrtDeriv :
      HasDerivAt Real.sqrt (1 / (2 * Real.sqrt x)) x :=
    Real.hasDerivAt_sqrt hx.ne'
  have hcoef :
      (1 / (1 + (Real.sqrt x) ^ 2)) * (1 / (2 * Real.sqrt x)) =
        1 / (2 * Real.sqrt x * (1 + x)) := by
    rw [Real.sq_sqrt hx.le]
    field_simp [hsqrt_ne, hone]
  have hatanDeriv :
      HasDerivAt (fun z : ℝ => Real.arctan (Real.sqrt z))
        (1 / (2 * Real.sqrt x * (1 + x))) x := by
    have h := (Real.hasDerivAt_arctan (Real.sqrt x)).comp x hsqrtDeriv
    simpa only [Function.comp_apply, hcoef] using h
  simpa only [y, expandedDerivative] using hsqrtDeriv.sub hatanDeriv

/-- Exercise 917, gap 2; positivity makes every square-root
denominator nonzero. -/
theorem gap2 (x : ℝ) (hx : 0 < x) :
    expandedDerivative x = finalDerivative x := by
  unfold expandedDerivative finalDerivative
  have hsqrt_ne : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hx).ne'
  have hone : 1 + x ≠ 0 := by
    linarith
  have hsquare : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx.le
  field_simp [hsqrt_ne, hone] <;> nlinarith [hsquare]

/-- Exercise 917, gap 3; retain the open square-root domain
used by the staged derivation. -/
theorem gap3 (x : ℝ) (hx : 0 < x) :
    HasDerivAt y (finalDerivative x) x := by
  simpa only [gap2 x hx] using gap1 x hx

end

end ProofGap.Exercise917

import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise925

noncomputable section

def y (x : ℝ) : ℝ :=
  Real.arctan ((1 + x) / (1 - x))

def expandedDerivative (x : ℝ) : ℝ :=
  1 / (1 + ((1 + x) / (1 - x)) ^ 2) *
    ((1 - x + 1 + x) / (1 - x) ^ 2)

def finalDerivative (x : ℝ) : ℝ :=
  1 / (1 + x ^ 2)

/-- Exercise 925, gap 1; exclude the pole `x = 1` in the
rational arctangent argument. -/
theorem gap1 (x : ℝ) (hx : x ≠ 1) :
    HasDerivAt y (expandedDerivative x) x := by
  unfold y expandedDerivative
  have hden : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hnum : HasDerivAt (fun t : ℝ => 1 + t) 1 x := by
    simpa using
      (hasDerivAt_const (x : ℝ) (1 : ℝ)).add (hasDerivAt_id x)
  have hdenDeriv : HasDerivAt (fun t : ℝ => 1 - t) (-1) x := by
    simpa using
      (hasDerivAt_const (x : ℝ) (1 : ℝ)).sub (hasDerivAt_id x)
  have hinnerRaw := hnum.div hdenDeriv hden
  have hinner :
      HasDerivAt (fun t : ℝ => (1 + t) / (1 - t))
        ((1 - x + 1 + x) / (1 - x) ^ 2) x := by
    convert hinnerRaw using 1 <;> ring
  exact
    (Real.hasDerivAt_arctan ((1 + x) / (1 - x))).comp x hinner

/-- Exercise 925, gap 2; the algebraic simplification uses
the nonzero denominator `1 - x`. -/
theorem gap2 (x : ℝ) (hx : x ≠ 1) :
    expandedDerivative x = finalDerivative x := by
  unfold expandedDerivative finalDerivative
  have hden : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hsum1 : 1 + x ^ 2 ≠ 0 := by positivity
  have hsum2 : 1 + ((1 + x) / (1 - x)) ^ 2 ≠ 0 := by positivity
  field_simp [hden, hsum1, hsum2] <;> ring

/-- Exercise 925, gap 3; the source expression remains
undefined and discontinuous across its rational pole. -/
theorem gap3 (x : ℝ) (hx : x ≠ 1) :
    HasDerivAt y (finalDerivative x) x := by
  simpa only [gap2 x hx] using (gap1 x hx)

end

end ProofGap.Exercise925

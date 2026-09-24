import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise916

noncomputable section

def arccot (x : ℝ) : ℝ :=
  Real.pi / 2 - Real.arctan x

def y (x : ℝ) : ℝ :=
  1 / Real.sqrt 2 * arccot (Real.sqrt 2 / x)

def expandedDerivative (x : ℝ) : ℝ :=
  (-1 / Real.sqrt 2) * (1 / (1 + (Real.sqrt 2 / x) ^ 2)) *
    (-Real.sqrt 2 / x ^ 2)

def finalDerivative (x : ℝ) : ℝ :=
  1 / (x ^ 2 + 2)

/-- Exercise 916, gap 1; exclude the pole in the
arccotangent argument. -/
theorem gap1 (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt y (expandedDerivative x) x := by
  have hg : HasDerivAt (fun z : ℝ => Real.sqrt 2 / z)
      (-Real.sqrt 2 / x ^ 2) x := by
    convert (hasDerivAt_const x (Real.sqrt 2)).div
      (hasDerivAt_id x) hx using 1 <;> simp <;> ring
  have ha : HasDerivAt arccot
      (-(1 / (1 + (Real.sqrt 2 / x) ^ 2))) (Real.sqrt 2 / x) := by
    simpa [arccot, pow_two] using
      (hasDerivAt_const (Real.sqrt 2 / x) (Real.pi / 2)).sub
        (Real.hasDerivAt_arctan (Real.sqrt 2 / x))
  have hcomp : HasDerivAt
      (fun z : ℝ => arccot (Real.sqrt 2 / z))
      (-(1 / (1 + (Real.sqrt 2 / x) ^ 2)) *
        (-Real.sqrt 2 / x ^ 2)) x :=
    ha.comp x hg
  unfold y expandedDerivative
  convert hcomp.const_mul (1 / Real.sqrt 2) using 1 <;> simp <;> ring

/-- Exercise 916, gap 2; the simplification divides by
the original nonzero `x`. -/
theorem gap2 (x : ℝ) (hx : x ≠ 0) :
    expandedDerivative x = finalDerivative x := by
  unfold expandedDerivative finalDerivative
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
  have hsum : x ^ 2 + 2 ≠ 0 := by positivity
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hrewrite : 1 + 2 / x ^ 2 = (x ^ 2 + 2) / x ^ 2 := by
    field_simp [hx2]
  rw [hrewrite]
  field_simp [hsqrt, hx2, hsum]

/-- Exercise 916, gap 3; the chosen source expression is
not differentiable through its reciprocal pole. -/
theorem gap3 (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt y (finalDerivative x) x := by
  rw [← gap2 x hx]
  exact gap1 x hx

end

end ProofGap.Exercise916

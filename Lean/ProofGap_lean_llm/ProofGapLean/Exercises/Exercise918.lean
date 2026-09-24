import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise918

noncomputable section

def y (x : ℝ) : ℝ :=
  x + Real.sqrt (1 - x ^ 2) * Real.arccos x

def expandedDerivative (x : ℝ) : ℝ :=
  1 - x / Real.sqrt (1 - x ^ 2) * Real.arccos x -
    1 / Real.sqrt (1 - x ^ 2) * Real.sqrt (1 - x ^ 2)

def finalDerivative (x : ℝ) : ℝ :=
  -x / Real.sqrt (1 - x ^ 2) * Real.arccos x

/-- Exercise 918, gap 1; both square root and arccosine
are differentiated strictly inside `(-1,1)`. -/
private lemma sqrtArg_pos (x : ℝ) (hx : |x| < 1) : 0 < 1 - x ^ 2 := by
  have hbounds : -1 < x ∧ x < 1 := abs_lt.mp hx
  nlinarith [mul_pos (sub_pos.mpr hbounds.2) (sub_pos.mpr hbounds.1)]

theorem gap1 (x : ℝ) (hx : |x| < 1) :
    HasDerivAt y (expandedDerivative x) x := by
  have harg : 0 < 1 - x ^ 2 := sqrtArg_pos x hx
  have hsqrt_ne : Real.sqrt (1 - x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 harg)
  have hinner :
      HasDerivAt (fun z : ℝ => 1 - z ^ 2) (-2 * x) x := by
    convert
      (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2) using 1 <;>
      simp only [id_eq] <;>
      ring_nf
  have hsqrt_deriv :
      HasDerivAt (fun z : ℝ => Real.sqrt (1 - z ^ 2))
        (-x / Real.sqrt (1 - x ^ 2)) x := by
    have hbase :=
      (Real.hasDerivAt_sqrt (ne_of_gt harg)).comp x hinner
    convert hbase using 1 <;>
      field_simp [hsqrt_ne] <;>
      ring
  have hbounds : -1 < x ∧ x < 1 := abs_lt.mp hx
  have harccos :
      HasDerivAt Real.arccos (-1 / Real.sqrt (1 - x ^ 2)) x := by
    simpa only [neg_div] using
      (Real.hasDerivAt_arccos (x := x)
        (ne_of_gt hbounds.1) (ne_of_lt hbounds.2))
  have hderiv :
      HasDerivAt y
        (1 + ((-x / Real.sqrt (1 - x ^ 2)) * Real.arccos x +
          Real.sqrt (1 - x ^ 2) * (-1 / Real.sqrt (1 - x ^ 2)))) x := by
    simpa only [y, id_eq] using
      (hasDerivAt_id x).add (hsqrt_deriv.mul harccos)
  have hcoeff :
      1 + ((-x / Real.sqrt (1 - x ^ 2)) * Real.arccos x +
        Real.sqrt (1 - x ^ 2) * (-1 / Real.sqrt (1 - x ^ 2))) =
        expandedDerivative x := by
    unfold expandedDerivative
    ring
  rw [hcoeff] at hderiv
  exact hderiv

/-- Exercise 918, gap 2; the strict-domain hypothesis
makes the square-root quotient equal to one. -/
theorem gap2 (x : ℝ) (hx : |x| < 1) :
    expandedDerivative x = finalDerivative x := by
  have harg : 0 < 1 - x ^ 2 := sqrtArg_pos x hx
  have hsqrt_ne : Real.sqrt (1 - x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 harg)
  unfold expandedDerivative finalDerivative
  field_simp [hsqrt_ne]
  ring

/-- Exercise 918, gap 3; retain the common open domain of
the square root and inverse cosine. -/
theorem gap3 (x : ℝ) (hx : |x| < 1) :
    HasDerivAt y (finalDerivative x) x := by
  rw [← gap2 x hx]
  exact gap1 x hx

end

end ProofGap.Exercise918

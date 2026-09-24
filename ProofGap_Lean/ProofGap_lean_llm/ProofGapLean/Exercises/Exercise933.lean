import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise933

noncomputable section

def y (a b x : ℝ) : ℝ :=
  Real.log ((x + a) / Real.sqrt (x ^ 2 + b ^ 2)) +
    a / b * Real.arctan (x / b)

def expandedDerivative (a b x : ℝ) : ℝ :=
  1 / (x + a) - x / (x ^ 2 + b ^ 2) +
    a / b * (1 / (b * (1 + x ^ 2 / b ^ 2)))

def finalDerivative (a b x : ℝ) : ℝ :=
  (a ^ 2 + b ^ 2) / ((x + a) * (b ^ 2 + x ^ 2))

/-- Exercise 933, gap 1; require `b ≠ 0` and `x+a > 0`
so the square-root quotient is positive and every parameter division is
defined. -/
theorem gap1 (a b x : ℝ) (hb : b ≠ 0) (hxa : 0 < x + a) :
    HasDerivAt (y a b) (expandedDerivative a b x) x := by
  have hquad : 0 < x ^ 2 + b ^ 2 := by positivity
  have hsqrt : 0 < Real.sqrt (x ^ 2 + b ^ 2) := Real.sqrt_pos.2 hquad
  have hpoly : HasDerivAt (fun z : ℝ => z ^ 2 + b ^ 2) (2 * x) x := by
    convert (((hasDerivAt_id x).pow 2).add_const (b ^ 2)) using 1 <;>
      simp [mul_comm]
  have hsqrtDeriv :
      HasDerivAt (fun z : ℝ => Real.sqrt (z ^ 2 + b ^ 2))
        (x / Real.sqrt (x ^ 2 + b ^ 2)) x := by
    convert hpoly.sqrt (ne_of_gt hquad) using 1
    field_simp [ne_of_gt hsqrt] <;> ring
  have hnum : HasDerivAt (fun z : ℝ => z + a) 1 x := by
    simpa using (hasDerivAt_id x).add_const a
  have hratio := hnum.div hsqrtDeriv (ne_of_gt hsqrt)
  have hquot : (x + a) / Real.sqrt (x ^ 2 + b ^ 2) ≠ 0 :=
    ne_of_gt (div_pos hxa hsqrt)
  have hlog := hratio.log hquot
  change HasDerivAt
    (fun z : ℝ => Real.log ((z + a) / Real.sqrt (z ^ 2 + b ^ 2))) _ x at hlog
  have hlog' :
      HasDerivAt
        (fun z : ℝ => Real.log ((z + a) / Real.sqrt (z ^ 2 + b ^ 2)))
        (1 / (x + a) - x / (x ^ 2 + b ^ 2)) x := by
    convert hlog using 1
    simp only [Pi.div_apply]
    field_simp [ne_of_gt hxa, ne_of_gt hquad, ne_of_gt hsqrt]
    rw [Real.sq_sqrt (le_of_lt hquad)] <;> ring
  have hatanInner : HasDerivAt (fun z : ℝ => z / b) (1 / b) x := by
    simpa [div_eq_mul_inv] using (hasDerivAt_id x).mul_const (b⁻¹)
  have hatan := (Real.hasDerivAt_arctan (x / b)).comp x hatanInner
  have hatanScaled := hatan.const_mul (a / b)
  change HasDerivAt
    (fun z : ℝ => a / b * Real.arctan (z / b)) _ x at hatanScaled
  have hden1 : 1 + (x / b) ^ 2 ≠ 0 := by positivity
  have hden2 : 1 + x ^ 2 / b ^ 2 ≠ 0 := by positivity
  have hatan' :
      HasDerivAt (fun z : ℝ => a / b * Real.arctan (z / b))
        (a / b * (1 / (b * (1 + x ^ 2 / b ^ 2)))) x := by
    convert hatanScaled using 1
    field_simp [hb, hden1, hden2] <;> ring
  simpa [y, expandedDerivative] using hlog'.add hatan'

/-- Exercise 933, gap 2; the same hypotheses make all
denominators in the rational simplification nonzero. -/
theorem gap2 (a b x : ℝ) (hb : b ≠ 0) (hxa : 0 < x + a) :
    expandedDerivative a b x = finalDerivative a b x := by
  have hxa0 : x + a ≠ 0 := ne_of_gt hxa
  have hb2 : b ^ 2 ≠ 0 := pow_ne_zero 2 hb
  have hquad : x ^ 2 + b ^ 2 ≠ 0 := by
    have : 0 < x ^ 2 + b ^ 2 := by positivity
    exact ne_of_gt this
  unfold expandedDerivative finalDerivative
  field_simp [hb, hxa0, hb2, hquad]
  ring

/-- Exercise 933, gap 3; make the source's free parameters
explicit and retain the logarithm and quotient domains. -/
theorem gap3 (a b x : ℝ) (hb : b ≠ 0) (hxa : 0 < x + a) :
    HasDerivAt (y a b) (finalDerivative a b x) x := by
  rw [← gap2 a b x hb hxa]
  exact gap1 a b x hb hxa

end

end ProofGap.Exercise933

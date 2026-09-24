import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace ProofGap.Exercise874

noncomputable section

def sec (x : ℝ) : ℝ := 1 / Real.cos x
def csc (x : ℝ) : ℝ := 1 / Real.sin x
def cot (x : ℝ) : ℝ := Real.cos x / Real.sin x
def u (a x : ℝ) : ℝ := x / a

def y (a x : ℝ) : ℝ := sec (u a x) ^ 2 + csc (u a x) ^ 2

def expandedDerivative (a x : ℝ) : ℝ :=
  (2 / a) * sec (u a x) ^ 2 * Real.tan (u a x) -
    (2 / a) * csc (u a x) ^ 2 * cot (u a x)

def reciprocalDerivative (a x : ℝ) : ℝ :=
  (2 / a) *
    (Real.sin (u a x) / Real.cos (u a x) ^ 3 -
      Real.cos (u a x) / Real.sin (u a x) ^ 3)

def combinedDerivative (a x : ℝ) : ℝ :=
  (2 / a) *
    ((Real.sin (u a x) ^ 4 - Real.cos (u a x) ^ 4) /
      (Real.sin (u a x) ^ 3 * Real.cos (u a x) ^ 3))

def doubleAngleDerivative (a x : ℝ) : ℝ :=
  (16 * (Real.sin (u a x) ^ 2 - Real.cos (u a x) ^ 2)) /
    (a * (2 * Real.sin (u a x) * Real.cos (u a x)) ^ 3)

def finalDerivative (a x : ℝ) : ℝ :=
  (-16 * Real.cos (2 * x / a)) / (a * Real.sin (2 * x / a) ^ 3)

/-- Exercise 874, gap 1; require a nonzero scale and both
reciprocal-trigonometric denominators to be nonzero. -/
theorem gap1 (a x : ℝ) (ha : a ≠ 0)
    (hcos : Real.cos (u a x) ≠ 0) (hsin : Real.sin (u a x) ≠ 0) :
    deriv (y a) x = expandedDerivative a x := by
  have hu : HasDerivAt (u a) (1 / a) x := by
    simpa [u] using (hasDerivAt_id x).div_const a
  have hsec :=
    (hasDerivAt_const x (1 : ℝ)).div
      ((Real.hasDerivAt_cos (u a x)).comp x hu) hcos
  have hcsc :=
    (hasDerivAt_const x (1 : ℝ)).div
      ((Real.hasDerivAt_sin (u a x)).comp x hu) hsin
  convert ((hsec.pow 2).add (hcsc.pow 2)).deriv using 1
  unfold expandedDerivative sec csc cot
  rw [Real.tan_eq_sin_div_cos]
  simp only [Function.comp_apply, Pi.div_apply, Pi.one_apply]
  field_simp [ha, hcos, hsin]
  field_simp [ha, hcos, hsin]
  ring_nf
  have hcancel :
      Real.sin (u a x) * Real.cos (u a x) ^ 4 *
          (Real.sin (u a x))⁻¹ =
        Real.cos (u a x) ^ 4 := by
    calc
      _ = Real.cos (u a x) ^ 4 *
          (Real.sin (u a x) * (Real.sin (u a x))⁻¹) := by ring
      _ = Real.cos (u a x) ^ 4 := by simp [hsin]
  rw [hcancel]
  have hcancelCos :
      Real.sin (u a x) ^ 4 * Real.cos (u a x) *
          (Real.cos (u a x))⁻¹ =
        Real.sin (u a x) ^ 4 := by
    calc
      _ = Real.sin (u a x) ^ 4 *
          (Real.cos (u a x) * (Real.cos (u a x))⁻¹) := by ring
      _ = Real.sin (u a x) ^ 4 := by simp [hcos]
  rw [hcancelCos]
  ring

/-- Exercise 874, gap 2; retain the source function's full
domain while rewriting secant, cosecant, tangent, and cotangent. -/
theorem gap2 (a x : ℝ) (ha : a ≠ 0)
    (hcos : Real.cos (u a x) ≠ 0) (hsin : Real.sin (u a x) ≠ 0) :
    deriv (y a) x = reciprocalDerivative a x := by
  rw [gap1 a x ha hcos hsin]
  unfold expandedDerivative reciprocalDerivative sec csc cot
  rw [Real.tan_eq_sin_div_cos]
  field_simp [ha, hcos, hsin]
  <;> ring

/-- Exercise 874, gap 3; retain all nonzero denominators
while combining the two fractions. -/
theorem gap3 (a x : ℝ) (ha : a ≠ 0)
    (hcos : Real.cos (u a x) ≠ 0) (hsin : Real.sin (u a x) ≠ 0) :
    reciprocalDerivative a x = combinedDerivative a x := by
  unfold reciprocalDerivative combinedDerivative
  field_simp [ha, hcos, hsin]
  <;> ring

/-- Exercise 874, gap 4; restrict to the source function's
domain. -/
theorem gap4 (a x : ℝ) (ha : a ≠ 0)
    (hcos : Real.cos (u a x) ≠ 0) (hsin : Real.sin (u a x) ≠ 0) :
    deriv (y a) x = combinedDerivative a x := by
  rw [gap2 a x ha hcos hsin, gap3 a x ha hcos hsin]

/-- Exercise 874, gap 5; retain the scale and
reciprocal-trigonometric domain restrictions. -/
theorem gap5 (a x : ℝ) (ha : a ≠ 0)
    (hcos : Real.cos (u a x) ≠ 0) (hsin : Real.sin (u a x) ≠ 0) :
    deriv (y a) x = doubleAngleDerivative a x := by
  rw [gap4 a x ha hcos hsin]
  have htrig :
      Real.sin (u a x) ^ 4 - Real.cos (u a x) ^ 4 =
        Real.sin (u a x) ^ 2 - Real.cos (u a x) ^ 2 := by
    calc
      Real.sin (u a x) ^ 4 - Real.cos (u a x) ^ 4 =
          (Real.sin (u a x) ^ 2 - Real.cos (u a x) ^ 2) *
            (Real.sin (u a x) ^ 2 + Real.cos (u a x) ^ 2) := by ring
      _ = Real.sin (u a x) ^ 2 - Real.cos (u a x) ^ 2 := by
        rw [Real.sin_sq_add_cos_sq]
        ring
  unfold combinedDerivative doubleAngleDerivative
  rw [htrig]
  field_simp [ha, hcos, hsin]
  <;> ring

/-- Exercise 874, gap 6; retain all denominator conditions
when applying the double-angle identities. -/
theorem gap6 (a x : ℝ) (ha : a ≠ 0)
    (hcos : Real.cos (u a x) ≠ 0) (hsin : Real.sin (u a x) ≠ 0) :
    doubleAngleDerivative a x = finalDerivative a x := by
  have harg : 2 * x / a = 2 * u a x := by
    unfold u
    field_simp [ha]
  unfold doubleAngleDerivative finalDerivative
  rw [harg, Real.sin_two_mul, Real.cos_two_mul]
  field_simp [ha, hcos, hsin]
  nlinarith [Real.sin_sq_add_cos_sq (u a x)]

/-- Exercise 874, gap 7; restrict the final derivative
formula to the source function's domain. -/
theorem gap7 (a x : ℝ) (ha : a ≠ 0)
    (hcos : Real.cos (u a x) ≠ 0) (hsin : Real.sin (u a x) ≠ 0) :
    deriv (y a) x = finalDerivative a x := by
  rw [gap5 a x ha hcos hsin, gap6 a x ha hcos hsin]

end

end ProofGap.Exercise874

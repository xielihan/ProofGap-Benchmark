import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise922

noncomputable section

def y (x : ℝ) : ℝ :=
  Real.arccos (Real.cos x ^ 2)

def expandedDerivative (x : ℝ) : ℝ :=
  Real.sin (2 * x) / Real.sqrt (1 - Real.cos x ^ 4)

def factoredDerivative (x : ℝ) : ℝ :=
  Real.sin (2 * x) /
    Real.sqrt (Real.sin x ^ 2 * (1 + Real.cos x ^ 2))

def finalDerivative (x : ℝ) : ℝ :=
  2 * Real.sign (Real.sin x) * Real.cos x /
    Real.sqrt (1 + Real.cos x ^ 2)

/-- Exercise 922, gap 1; exclude `sin x = 0`, where the
arccosine input reaches its endpoint and the composition has a cusp. -/
theorem gap1 (x : ℝ) (hx : Real.sin x ≠ 0) :
    HasDerivAt y (expandedDerivative x) x := by
  have hspos : 0 < Real.sin x ^ 2 := sq_pos_of_ne_zero hx
  have hc_lt : Real.cos x ^ 2 < 1 := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hu_neg_one : Real.cos x ^ 2 ≠ (-1 : ℝ) := by
    nlinarith [sq_nonneg (Real.cos x)]
  have hu_one : Real.cos x ^ 2 ≠ (1 : ℝ) := ne_of_lt hc_lt
  have hcos2 :
      HasDerivAt (fun t : ℝ => Real.cos t ^ 2) (-Real.sin (2 * x)) x := by
    convert (Real.hasDerivAt_cos x).pow 2 using 1 <;>
      simp [Real.sin_two_mul] <;> ring
  have hcomp :=
    (Real.hasDerivAt_arccos hu_neg_one hu_one).comp x hcos2
  have hrad :
      1 - (Real.cos x ^ 2) ^ 2 = 1 - Real.cos x ^ 4 := by
    ring
  have hden_pos : 0 < 1 - Real.cos x ^ 4 := by
    calc
      1 - Real.cos x ^ 4 =
          (1 - Real.cos x ^ 2) * (1 + Real.cos x ^ 2) := by ring
      _ > 0 := mul_pos (sub_pos.mpr hc_lt) (by positivity)
  have hsqrt_ne : Real.sqrt (1 - Real.cos x ^ 4) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hden_pos)
  unfold y expandedDerivative
  convert hcomp using 1
  rw [hrad]
  field_simp [hsqrt_ne] <;> ring

/-- Exercise 922, gap 2; the square-root denominator is
positive away from zeros of sine. -/
theorem gap2 (x : ℝ) (hx : Real.sin x ≠ 0) :
    expandedDerivative x = factoredDerivative x := by
  have hsin : 1 - Real.cos x ^ 2 = Real.sin x ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hrad :
      1 - Real.cos x ^ 4 =
        Real.sin x ^ 2 * (1 + Real.cos x ^ 2) := by
    calc
      1 - Real.cos x ^ 4 =
          (1 - Real.cos x ^ 2) * (1 + Real.cos x ^ 2) := by ring
      _ = Real.sin x ^ 2 * (1 + Real.cos x ^ 2) := by rw [hsin]
  simp [expandedDerivative, factoredDerivative, hrad]

/-- Exercise 922, gap 3; retain the sign of sine when
extracting `sqrt (sin² x)`. -/
theorem gap3 (x : ℝ) (hx : Real.sin x ≠ 0) :
    factoredDerivative x = finalDerivative x := by
  have hs2 : 0 ≤ Real.sin x ^ 2 := sq_nonneg (Real.sin x)
  have haux_pos : 0 < 1 + Real.cos x ^ 2 := by positivity
  have hsqrt_ne : Real.sqrt (1 + Real.cos x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 haux_pos)
  unfold factoredDerivative finalDerivative
  rw [Real.sqrt_mul hs2, Real.sqrt_sq_eq_abs, Real.sin_two_mul]
  by_cases hs : 0 < Real.sin x
  · rw [abs_of_pos hs, Real.sign_of_pos hs]
    field_simp [hx, hsqrt_ne] <;> ring
  · have hsneg : Real.sin x < 0 :=
      lt_of_le_of_ne (le_of_not_gt hs) hx
    rw [abs_of_neg hsneg, Real.sign_of_neg hsneg]
    field_simp [hx, hsqrt_ne] <;> ring

/-- Exercise 922, gap 4; retain the nonsingular domain in
the final derivative statement. -/
theorem gap4 (x : ℝ) (hx : Real.sin x ≠ 0) :
    HasDerivAt y (finalDerivative x) x := by
  have h := gap1 x hx
  rw [gap2 x hx, gap3 x hx] at h
  exact h

end

end ProofGap.Exercise922

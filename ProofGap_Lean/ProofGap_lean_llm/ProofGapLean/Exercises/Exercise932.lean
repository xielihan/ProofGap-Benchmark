import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise932

noncomputable section

def y (x : ℝ) : ℝ :=
  Real.log (Real.arccos (1 / Real.sqrt x))

def expandedDerivative (x : ℝ) : ℝ :=
  1 / Real.arccos (1 / Real.sqrt x) *
    (-1 / Real.sqrt (1 - x⁻¹)) *
    (-1 / (2 * x * Real.sqrt x))

def finalDerivative (x : ℝ) : ℝ :=
  1 / (2 * x * Real.sqrt (x - 1) * Real.arccos (1 / Real.sqrt x))

/-- Exercise 932, gap 1; `x > 1` makes the reciprocal
square root lie strictly between zero and one and makes the outer logarithm
positive. -/
theorem gap1 (x : ℝ) (hx : 1 < x) :
    HasDerivAt y (expandedDerivative x) x := by
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  have hxne : x ≠ 0 := ne_of_gt hxpos
  have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.2 hxpos
  have hsqrt_ne : Real.sqrt x ≠ 0 := ne_of_gt hsqrt_pos
  have hsqrt_sq : (Real.sqrt x) ^ 2 = x :=
    Real.sq_sqrt (le_of_lt hxpos)
  have hsqrt_deriv :
      HasDerivAt (fun t : ℝ => Real.sqrt t)
        (1 / (2 * Real.sqrt x)) x := by
    simpa only [one_div] using Real.hasDerivAt_sqrt hxne
  have hinv_raw :
      HasDerivAt (fun t : ℝ => (Real.sqrt t)⁻¹)
        (-(1 / (2 * Real.sqrt x)) / (Real.sqrt x) ^ 2) x :=
    hsqrt_deriv.inv hsqrt_ne
  have hcoeff :
      -(1 / (2 * Real.sqrt x)) / (Real.sqrt x) ^ 2 =
        -1 / (2 * x * Real.sqrt x) := by
    rw [hsqrt_sq]
    field_simp [hxne, hsqrt_ne]
  rw [hcoeff] at hinv_raw
  have hinv :
      HasDerivAt (fun t : ℝ => 1 / Real.sqrt t)
        (-1 / (2 * x * Real.sqrt x)) x := by
    simpa only [one_div] using hinv_raw
  have hsqrt_gt_one : 1 < Real.sqrt x := by
    nlinarith [hsqrt_sq, Real.sqrt_nonneg x]
  have hu_pos : 0 < 1 / Real.sqrt x := one_div_pos.mpr hsqrt_pos
  have hu_lt_one : 1 / Real.sqrt x < 1 :=
    (div_lt_one hsqrt_pos).2 hsqrt_gt_one
  have hu_ne_neg_one : 1 / Real.sqrt x ≠ (-1 : ℝ) := by
    linarith
  have hu_ne_one : 1 / Real.sqrt x ≠ (1 : ℝ) := ne_of_lt hu_lt_one
  have hu_sq : (1 / Real.sqrt x) ^ 2 = x⁻¹ := by
    rw [one_div, inv_pow, hsqrt_sq]
  have hacos_comp :=
    (Real.hasDerivAt_arccos hu_ne_neg_one hu_ne_one).comp x hinv
  have hacos :
      HasDerivAt
        (Real.arccos ∘ (fun t : ℝ => 1 / Real.sqrt t))
        (-(1 / Real.sqrt (1 - x⁻¹)) *
          (-1 / (2 * x * Real.sqrt x))) x := by
    simpa only [hu_sq] using hacos_comp
  have hacos_ne : Real.arccos (1 / Real.sqrt x) ≠ 0 :=
    ne_of_gt (Real.arccos_pos.2 hu_lt_one)
  change HasDerivAt
    (fun t : ℝ => Real.log (Real.arccos (1 / Real.sqrt t)))
    (expandedDerivative x) x
  rw [show (fun t : ℝ => Real.log (Real.arccos (1 / Real.sqrt t))) =
      Real.log ∘ (Real.arccos ∘ (fun t : ℝ => 1 / Real.sqrt t)) from rfl]
  simpa only [expandedDerivative, one_div, neg_div, mul_assoc] using
    (Real.hasDerivAt_log hacos_ne).comp x hacos

/-- Exercise 932, gap 2; the positive-domain hypothesis
justifies combining the two square roots without a sign ambiguity. -/
theorem gap2 (x : ℝ) (hx : 1 < x) :
    expandedDerivative x = finalDerivative x := by
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  have hxne : x ≠ 0 := ne_of_gt hxpos
  have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.2 hxpos
  have hsqrt_ne : Real.sqrt x ≠ 0 := ne_of_gt hsqrt_pos
  have hsqrt_sq : (Real.sqrt x) ^ 2 = x :=
    Real.sq_sqrt (le_of_lt hxpos)
  have hsqrt_gt_one : 1 < Real.sqrt x := by
    nlinarith [hsqrt_sq, Real.sqrt_nonneg x]
  have hu_lt_one : 1 / Real.sqrt x < 1 :=
    (div_lt_one hsqrt_pos).2 hsqrt_gt_one
  have hacos_ne : Real.arccos (1 / Real.sqrt x) ≠ 0 :=
    ne_of_gt (Real.arccos_pos.2 hu_lt_one)
  have hinv_lt_one : x⁻¹ < 1 := by
    simpa only [one_div] using (div_lt_one hxpos).2 hx
  have hsub_pos : 0 < 1 - x⁻¹ := sub_pos.mpr hinv_lt_one
  have hsqrt_sub_ne : Real.sqrt (1 - x⁻¹) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hsub_pos)
  have hmul : (1 - x⁻¹) * x = x - 1 := by
    field_simp [hxne]
  have hsqrt_mul :
      Real.sqrt (1 - x⁻¹) * Real.sqrt x = Real.sqrt (x - 1) := by
    rw [← Real.sqrt_mul (le_of_lt hsub_pos), hmul]
  unfold expandedDerivative finalDerivative
  rw [← hsqrt_mul]
  field_simp [hxne, hsqrt_ne, hsqrt_sub_ne, hacos_ne]

/-- Exercise 932, gap 3; retain the nested square-root,
arccosine, and logarithm domain. -/
theorem gap3 (x : ℝ) (hx : 1 < x) :
    HasDerivAt y (finalDerivative x) x := by
  rw [← gap2 x hx]
  exact gap1 x hx

end

end ProofGap.Exercise932

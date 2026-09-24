import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise899

noncomputable section

def numerator (a b x : ℝ) : ℝ := Real.sqrt a + x * Real.sqrt b
def denominator (a b x : ℝ) : ℝ := Real.sqrt a - x * Real.sqrt b

def y (a b x : ℝ) : ℝ :=
  (1 / (2 * Real.sqrt (a * b))) *
    Real.log (numerator a b x / denominator a b x)

def expandedDerivative (a b x : ℝ) : ℝ :=
  (1 / (2 * Real.sqrt (a * b))) *
    (Real.sqrt b / numerator a b x +
      Real.sqrt b / denominator a b x)

def finalDerivative (a b x : ℝ) : ℝ := 1 / (a - b * x ^ 2)

private theorem numerator_denominator_product (a b x : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    numerator a b x * denominator a b x = a - b * x ^ 2 := by
  unfold numerator denominator
  calc
    (Real.sqrt a + x * Real.sqrt b) *
          (Real.sqrt a - x * Real.sqrt b) =
        (Real.sqrt a) ^ 2 - x ^ 2 * (Real.sqrt b) ^ 2 := by
          ring
    _ = a - b * x ^ 2 := by
      rw [Real.sq_sqrt ha, Real.sq_sqrt hb]
      ring

theorem gap1 (a b x : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hx : b * x ^ 2 < a) :
    deriv (y a b) x = expandedDerivative a b x := by
  have hmul_ne : numerator a b x * denominator a b x ≠ 0 := by
    rw [numerator_denominator_product a b x ha.le hb.le]
    exact ne_of_gt (sub_pos.mpr hx)
  have hnum_ne : numerator a b x ≠ 0 := by
    intro h
    apply hmul_ne
    rw [h, zero_mul]
  have hden_ne : denominator a b x ≠ 0 := by
    intro h
    apply hmul_ne
    rw [h, mul_zero]
  have hquot_ne : numerator a b x / denominator a b x ≠ 0 :=
    div_ne_zero hnum_ne hden_ne
  have hsqrt_ab_ne : Real.sqrt (a * b) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (mul_pos ha hb))
  have hnum_deriv :
      HasDerivAt (numerator a b) (Real.sqrt b) x := by
    simpa [numerator] using
      (hasDerivAt_const (x := x) (c := Real.sqrt a)).add
        ((hasDerivAt_id x).mul_const (Real.sqrt b))
  have hden_deriv :
      HasDerivAt (denominator a b) (-Real.sqrt b) x := by
    simpa [denominator] using
      (hasDerivAt_const (x := x) (c := Real.sqrt a)).sub
        ((hasDerivAt_id x).mul_const (Real.sqrt b))
  have hquot_deriv :
      HasDerivAt
        (fun z : ℝ => numerator a b z / denominator a b z)
        ((Real.sqrt b * denominator a b x -
            numerator a b x * (-Real.sqrt b)) /
          denominator a b x ^ 2)
        x := by
    simpa using hnum_deriv.div hden_deriv hden_ne
  have hlog_deriv :
      HasDerivAt
        (fun z : ℝ => Real.log (numerator a b z / denominator a b z))
        (((Real.sqrt b * denominator a b x -
            numerator a b x * (-Real.sqrt b)) /
          denominator a b x ^ 2) /
          (numerator a b x / denominator a b x))
        x := by
    simpa [Function.comp_def, div_eq_mul_inv, mul_comm] using
      (Real.hasDerivAt_log hquot_ne).comp x hquot_deriv
  have hy_deriv :=
    hlog_deriv.const_mul (1 / (2 * Real.sqrt (a * b)))
  change
    deriv
        (fun z : ℝ =>
          (1 / (2 * Real.sqrt (a * b))) *
            Real.log (numerator a b z / denominator a b z))
        x = expandedDerivative a b x
  rw [hy_deriv.deriv]
  unfold expandedDerivative
  field_simp [hnum_ne, hden_ne, hquot_ne, hsqrt_ab_ne] <;> ring

theorem gap2 (a b x : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hx : b * x ^ 2 < a) :
    expandedDerivative a b x = finalDerivative a b x := by
  have hmul_ne : numerator a b x * denominator a b x ≠ 0 := by
    rw [numerator_denominator_product a b x ha.le hb.le]
    exact ne_of_gt (sub_pos.mpr hx)
  have hnum_ne : numerator a b x ≠ 0 := by
    intro h
    apply hmul_ne
    rw [h, zero_mul]
  have hden_ne : denominator a b x ≠ 0 := by
    intro h
    apply hmul_ne
    rw [h, mul_zero]
  have hdiff_ne : a - b * x ^ 2 ≠ 0 :=
    ne_of_gt (sub_pos.mpr hx)
  have hsqrta_ne : Real.sqrt a ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 ha)
  have hsqrtb_ne : Real.sqrt b ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hb)
  have hsqrt_mul :
      Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b := by
    rw [Real.sqrt_mul ha.le]
  have hsum :
      Real.sqrt b / numerator a b x +
          Real.sqrt b / denominator a b x =
        (2 * Real.sqrt a * Real.sqrt b) / (a - b * x ^ 2) := by
    calc
      Real.sqrt b / numerator a b x +
            Real.sqrt b / denominator a b x =
          (Real.sqrt b * denominator a b x +
            Real.sqrt b * numerator a b x) /
            (numerator a b x * denominator a b x) := by
              field_simp [hnum_ne, hden_ne] <;> ring
      _ = (2 * Real.sqrt a * Real.sqrt b) / (a - b * x ^ 2) := by
        rw [numerator_denominator_product a b x ha.le hb.le]
        unfold numerator denominator
        ring
  unfold expandedDerivative finalDerivative
  rw [hsum, hsqrt_mul]
  field_simp [hsqrta_ne, hsqrtb_ne, hdiff_ne] <;> ring

theorem gap3 (a b x : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hx : b * x ^ 2 < a) :
    deriv (y a b) x = finalDerivative a b x := by
  exact (gap1 a b x ha hb hx).trans (gap2 a b x ha hb hx)

end

end ProofGap.Exercise899

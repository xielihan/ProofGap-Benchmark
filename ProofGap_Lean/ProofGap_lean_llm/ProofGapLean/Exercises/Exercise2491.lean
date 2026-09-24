import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality

open scoped Interval
open MeasureTheory

namespace ProofGap.Exercise2491

noncomputable section

def OnCircle (a b x y : ℝ) : Prop :=
  x ^ 2 + (y - b) ^ 2 = a ^ 2

def upper (a b x : ℝ) : ℝ := b + Real.sqrt (a ^ 2 - x ^ 2)

def lower (a b x : ℝ) : ℝ := b - Real.sqrt (a ^ 2 - x ^ 2)

def surfaceArea (a b : ℝ) : ℝ :=
  2 * Real.pi * (∫ x in -a..a,
      upper a b x * (a / Real.sqrt (a ^ 2 - x ^ 2))) +
    2 * Real.pi * (∫ x in -a..a,
      lower a b x * (a / Real.sqrt (a ^ 2 - x ^ 2)))

private theorem integral_inv_sqrt_one_sub_sq :
    (∫ x in (-1 : ℝ)..1, (Real.sqrt (1 - x ^ 2))⁻¹) = Real.pi := by
  have h :=
    Polynomial.Chebyshev.integral_measureT_eq_integral_cos_of_continuous
      (f := fun _ : ℝ => (1 : ℝ)) (by fun_prop)
  rw [Polynomial.Chebyshev.integral_measureT] at h
  simpa [intervalIntegral.integral_const, smul_eq_mul] using h

private theorem scaled_weight_eq (a u : ℝ) (ha : 0 < a) :
    a / Real.sqrt (a ^ 2 - (a * u) ^ 2) =
      (Real.sqrt (1 - u ^ 2))⁻¹ := by
  rw [show a ^ 2 - (a * u) ^ 2 = a ^ 2 * (1 - u ^ 2) by ring]
  rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs, abs_of_pos ha]
  rw [div_eq_mul_inv, mul_inv_rev]
  calc
    a * ((Real.sqrt (1 - u ^ 2))⁻¹ * a⁻¹) =
        (a * a⁻¹) * (Real.sqrt (1 - u ^ 2))⁻¹ := by ring
    _ = (Real.sqrt (1 - u ^ 2))⁻¹ := by rw [mul_inv_cancel₀ ha.ne', one_mul]

private theorem integral_weight (a : ℝ) (ha : 0 < a) :
    (∫ x in -a..a, a / Real.sqrt (a ^ 2 - x ^ 2)) = a * Real.pi := by
  calc
    (∫ x in -a..a, a / Real.sqrt (a ^ 2 - x ^ 2)) =
        a • ∫ u in (-1 : ℝ)..1,
          a / Real.sqrt (a ^ 2 - (a * u) ^ 2) := by
      simpa using
        (intervalIntegral.smul_integral_comp_mul_left
          (f := fun x : ℝ => a / Real.sqrt (a ^ 2 - x ^ 2))
          (a := (-1 : ℝ)) (b := 1) a).symm
    _ = a • ∫ u in (-1 : ℝ)..1, (Real.sqrt (1 - u ^ 2))⁻¹ := by
      apply congrArg (fun z : ℝ => a • z)
      apply intervalIntegral.integral_congr
      intro u hu
      exact scaled_weight_eq a u ha
    _ = a * Real.pi := by
      rw [integral_inv_sqrt_one_sub_sq]
      simp only [smul_eq_mul]

private theorem intervalIntegrable_weight (a : ℝ) (ha : 0 < a) :
    IntervalIntegrable (fun x : ℝ => a / Real.sqrt (a ^ 2 - x ^ 2))
      volume (-a) a := by
  have hcomp : IntervalIntegrable
      (fun u : ℝ => a / Real.sqrt (a ^ 2 - (a * u) ^ 2))
      volume (-1) 1 := by
    have hbase : IntervalIntegrable
        (fun u : ℝ => (Real.sqrt (1 - u ^ 2))⁻¹) volume (-1) 1 := by
      simpa only [Real.sqrt_inv] using
        Polynomial.Chebyshev.intervalIntegrable_sqrt_one_sub_sq_inv
    exact hbase.congr
      (fun u hu => (scaled_weight_eq a u ha).symm)
  apply (IntervalIntegrable.comp_mul_left_iff
    (f := fun x : ℝ => a / Real.sqrt (a ^ 2 - x ^ 2))
    (a := -a) (b := a) ha.ne').mp
  simpa [ha.ne'] using hcomp

theorem gap1 (a b x y : ℝ) (ha : 0 ≤ a) (hx : |x| ≤ a) :
    OnCircle a b x y ↔
      y = upper a b x ∨ y = lower a b x := by
  unfold OnCircle upper lower
  rcases abs_le.mp hx with ⟨hxa, hax⟩
  have hrad : 0 ≤ a ^ 2 - x ^ 2 := by
    nlinarith
  constructor
  · intro h
    have hsq : (y - b) ^ 2 = (Real.sqrt (a ^ 2 - x ^ 2)) ^ 2 := by
      rw [Real.sq_sqrt hrad]
      linarith
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsq) with h | h
    · left
      linarith
    · right
      linarith
  · rintro (rfl | rfl) <;> nlinarith [Real.sq_sqrt hrad]

theorem gap2 (a b Pₓ : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hP : Pₓ = surfaceArea a b) :
    Pₓ =
      2 * Real.pi * (∫ x in -a..a,
          (b + Real.sqrt (a ^ 2 - x ^ 2)) *
            (a / Real.sqrt (a ^ 2 - x ^ 2))) +
        2 * Real.pi * (∫ x in -a..a,
          (b - Real.sqrt (a ^ 2 - x ^ 2)) *
            (a / Real.sqrt (a ^ 2 - x ^ 2))) := by
  simpa [surfaceArea, upper, lower] using hP

theorem gap3 (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    2 * Real.pi * (∫ x in -a..a,
        (b + Real.sqrt (a ^ 2 - x ^ 2)) *
          (a / Real.sqrt (a ^ 2 - x ^ 2))) +
      2 * Real.pi * (∫ x in -a..a,
        (b - Real.sqrt (a ^ 2 - x ^ 2)) *
          (a / Real.sqrt (a ^ 2 - x ^ 2))) =
        4 * Real.pi ^ 2 * a * b := by
  change
    2 * Real.pi * (∫ x in -a..a,
      upper a b x * (a / Real.sqrt (a ^ 2 - x ^ 2))) +
    2 * Real.pi * (∫ x in -a..a,
      lower a b x * (a / Real.sqrt (a ^ 2 - x ^ 2))) =
      4 * Real.pi ^ 2 * a * b
  have hw := intervalIntegrable_weight a ha
  have hucont : ContinuousOn (upper a b) [[-a, a]] := by
    unfold upper
    fun_prop
  have hlcont : ContinuousOn (lower a b) [[-a, a]] := by
    unfold lower
    fun_prop
  have hu : IntervalIntegrable
      (fun x : ℝ => upper a b x * (a / Real.sqrt (a ^ 2 - x ^ 2)))
      volume (-a) a :=
    hw.continuousOn_mul hucont
  have hl : IntervalIntegrable
      (fun x : ℝ => lower a b x * (a / Real.sqrt (a ^ 2 - x ^ 2)))
      volume (-a) a :=
    hw.continuousOn_mul hlcont
  rw [← mul_add, ← intervalIntegral.integral_add hu hl]
  have heq :
      (∫ x in -a..a,
        upper a b x * (a / Real.sqrt (a ^ 2 - x ^ 2)) +
          lower a b x * (a / Real.sqrt (a ^ 2 - x ^ 2))) =
        ∫ x in -a..a,
          (2 * b) * (a / Real.sqrt (a ^ 2 - x ^ 2)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    unfold upper lower
    ring
  rw [heq, intervalIntegral.integral_const_mul, integral_weight a ha]
  ring

theorem gap4 (a b Pₓ : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hP : Pₓ = surfaceArea a b) :
    Pₓ = 4 * Real.pi ^ 2 * a * b := by
  exact (gap2 a b Pₓ ha hab hP).trans (gap3 a b ha hab)

end

end ProofGap.Exercise2491

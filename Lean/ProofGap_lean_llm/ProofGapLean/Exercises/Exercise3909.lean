import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod

namespace ProofGap.Exercise3909

noncomputable section

open MeasureTheory
open scoped Interval

def rectangle (a A b B : ℝ) : Set (ℝ × ℝ) :=
  Set.Icc a A ×ˢ Set.Icc b B

def rectangleIntegral (a A b B : ℝ) (X Y : ℝ → ℝ) : ℝ :=
  ∫ p in rectangle a A b B, X p.1 * Y p.2

private theorem setIntegral_Icc_eq_interval
    {a A : ℝ} (haA : a ≤ A) (g : ℝ → ℝ) :
    (∫ x in Set.Icc a A, g x) = ∫ x in a..A, g x := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le haA]

theorem gap1 (a A b B : ℝ) (X Y : ℝ → ℝ)
    (haA : a ≤ A) (hbB : b ≤ B)
    (hX : ContinuousOn X (Set.Icc a A))
    (hY : ContinuousOn Y (Set.Icc b B)) :
    rectangleIntegral a A b B X Y =
      ∫ x in a..A, ∫ y in b..B, X x * Y y := by
  unfold rectangleIntegral rectangle
  rw [Measure.volume_eq_prod]
  rw [MeasureTheory.setIntegral_prod_mul]
  rw [setIntegral_Icc_eq_interval haA,
    setIntegral_Icc_eq_interval hbB]
  simp_rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_mul_const]

theorem gap2 (a A b B : ℝ) (X Y : ℝ → ℝ)
    (haA : a ≤ A) (hbB : b ≤ B)
    (hX : ContinuousOn X (Set.Icc a A))
    (hY : ContinuousOn Y (Set.Icc b B)) :
    (∫ x in a..A, ∫ y in b..B, X x * Y y) =
      (∫ x in a..A, X x) * ∫ y in b..B, Y y := by
  simp_rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_mul_const]

theorem gap3 (a A b B : ℝ) (X Y : ℝ → ℝ)
    (haA : a ≤ A) (hbB : b ≤ B)
    (hX : ContinuousOn X (Set.Icc a A))
    (hY : ContinuousOn Y (Set.Icc b B)) :
    rectangleIntegral a A b B X Y =
      (∫ x in a..A, X x) * ∫ y in b..B, Y y := by
  exact (gap1 a A b B X Y haA hbB hX hY).trans
    (gap2 a A b B X Y haA hbB hX hY)

theorem gap4 (a A b B : ℝ) (X Y : ℝ → ℝ)
    (haA : a ≤ A) (hbB : b ≤ B)
    (hX : ContinuousOn X (Set.Icc a A))
    (hY : ContinuousOn Y (Set.Icc b B)) :
    rectangleIntegral a A b B X Y =
      (∫ x in a..A, X x) * ∫ y in b..B, Y y := by
  exact gap3 a A b B X Y haA hbB hX hY

end

end ProofGap.Exercise3909

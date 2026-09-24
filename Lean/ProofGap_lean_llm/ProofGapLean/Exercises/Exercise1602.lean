import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1602

noncomputable section

def xCoord (a t : ℝ) := a * (Real.cos t + t * Real.sin t)
def yCoord (a t : ℝ) := a * (Real.sin t - t * Real.cos t)
def slope (a t : ℝ) := deriv (yCoord a) t / deriv (xCoord a) t
def secondSlope (a t : ℝ) := deriv (slope a) t / deriv (xCoord a) t
def powThreeHalves (u : ℝ) := u * Real.sqrt u
def curvatureRadius (a t : ℝ) :=
  powThreeHalves (1 + (slope a t) ^ 2) / |secondSlope a t|

private theorem coordDeriv (a t : ℝ) :
    deriv (xCoord a) t = a * (t * Real.cos t) ∧
      deriv (yCoord a) t = a * (t * Real.sin t) := by
  constructor
  · apply HasDerivAt.deriv
    unfold xCoord
    convert (hasDerivAt_const t a).mul
      ((Real.hasDerivAt_cos t).add
        ((hasDerivAt_id t).mul (Real.hasDerivAt_sin t))) using 1 <;>
      simp only [id] <;> ring
  · apply HasDerivAt.deriv
    unfold yCoord
    convert (hasDerivAt_const t a).mul
      ((Real.hasDerivAt_sin t).sub
        ((hasDerivAt_id t).mul (Real.hasDerivAt_cos t))) using 1 <;>
      simp only [id] <;> ring

theorem gap1 (a t : ℝ) (ha : 0 < a) (ht : t ≠ 0) (hc : Real.cos t ≠ 0) :
    slope a t = Real.tan t := by
  unfold slope
  rw [(coordDeriv a t).2, (coordDeriv a t).1,
    Real.tan_eq_sin_div_cos]
  field_simp [ne_of_gt ha, ht, hc] <;> ring
theorem gap2 (a t : ℝ) (ha : 0 < a) (ht : t ≠ 0) (hc : Real.cos t ≠ 0) :
    secondSlope a t = 1 / (a * t * (Real.cos t) ^ 3) := by
  have hslope :
      slope a = fun s : ℝ =>
        a * (s * Real.sin s) / (a * (s * Real.cos s)) := by
    funext s
    unfold slope
    rw [(coordDeriv a s).2, (coordDeriv a s).1]
  have hn :
      HasDerivAt (fun s : ℝ => a * (s * Real.sin s))
        (a * (Real.sin t + t * Real.cos t)) t := by
    convert (hasDerivAt_const t a).mul
      ((hasDerivAt_id t).mul (Real.hasDerivAt_sin t)) using 1 <;>
      simp only [id] <;> ring
  have hd :
      HasDerivAt (fun s : ℝ => a * (s * Real.cos s))
        (a * (Real.cos t - t * Real.sin t)) t := by
    convert (hasDerivAt_const t a).mul
      ((hasDerivAt_id t).mul (Real.hasDerivAt_cos t)) using 1 <;>
      simp only [id] <;> ring
  have hden : a * (t * Real.cos t) ≠ 0 :=
    mul_ne_zero (ne_of_gt ha) (mul_ne_zero ht hc)
  have hderiv :
      deriv (fun s : ℝ =>
        a * (s * Real.sin s) / (a * (s * Real.cos s))) t =
        ((a * (Real.sin t + t * Real.cos t)) *
            (a * (t * Real.cos t)) -
          (a * (t * Real.sin t)) *
            (a * (Real.cos t - t * Real.sin t))) /
          (a * (t * Real.cos t)) ^ 2 :=
    (hn.div hd hden).deriv
  have hnum :
      (a * (Real.sin t + t * Real.cos t)) *
          (a * (t * Real.cos t)) -
        (a * (t * Real.sin t)) *
          (a * (Real.cos t - t * Real.sin t)) =
        (a * t) ^ 2 := by
    calc
      _ = (a * t) ^ 2 *
          ((Real.sin t) ^ 2 + (Real.cos t) ^ 2) := by ring
      _ = (a * t) ^ 2 := by
        simp only [Real.sin_sq_add_cos_sq, mul_one]
  unfold secondSlope
  rw [hslope, (coordDeriv a t).1, hderiv, hnum]
  field_simp [ne_of_gt ha, ht, hc] <;> ring
theorem gap3 (a t : ℝ) (ha : 0 < a) (ht : t ≠ 0) (hc : Real.cos t ≠ 0) :
    curvatureRadius a t =
      powThreeHalves (1 + (Real.tan t) ^ 2) /
        (1 / (a * |t * (Real.cos t) ^ 3|)) := by
  unfold curvatureRadius
  rw [gap1 a t ha ht hc, gap2 a t ha ht hc]
  have habs :
      |1 / (a * t * (Real.cos t) ^ 3)| =
        1 / (a * |t * (Real.cos t) ^ 3|) := by
    simp [abs_div, abs_mul, abs_of_pos ha, mul_assoc]
  rw [habs]
theorem gap4 (a t : ℝ) (ha : 0 < a) (ht : t ≠ 0) (hc : Real.cos t ≠ 0) :
    curvatureRadius a t = a * |t| := by
  rw [gap3 a t ha ht hc]
  have hsec :
      1 + (Real.tan t) ^ 2 = 1 / (Real.cos t) ^ 2 := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hc] <;> nlinarith [Real.sin_sq_add_cos_sq t]
  have hsqrt :
      Real.sqrt (1 / (Real.cos t) ^ 2) =
        1 / |Real.cos t| := by
    calc
      Real.sqrt (1 / (Real.cos t) ^ 2) =
          Real.sqrt (((Real.cos t)⁻¹) ^ 2) := by
            simp [one_div]
      _ = |(Real.cos t)⁻¹| :=
        Real.sqrt_sq_eq_abs ((Real.cos t)⁻¹)
      _ = 1 / |Real.cos t| := by simp [one_div]
  have habssq :
      |Real.cos t| ^ 2 = (Real.cos t) ^ 2 := by
    calc
      |Real.cos t| ^ 2 = |Real.cos t * Real.cos t| := by
        rw [pow_two, abs_mul]
      _ = (Real.cos t) ^ 2 := by
        rw [abs_of_nonneg (mul_self_nonneg (Real.cos t)), pow_two]
  have habscube :
      |t * (Real.cos t) ^ 3| =
        |t| * ((Real.cos t) ^ 2 * |Real.cos t|) := by
    calc
      |t * (Real.cos t) ^ 3| =
          |t| * |Real.cos t| ^ 3 := by rw [abs_mul, abs_pow]
      _ = |t| * (|Real.cos t| ^ 2 * |Real.cos t|) := by ring
      _ = |t| * ((Real.cos t) ^ 2 * |Real.cos t|) := by
        rw [habssq]
  have hat : |t| ≠ 0 := abs_ne_zero.mpr ht
  have hac : |Real.cos t| ≠ 0 := abs_ne_zero.mpr hc
  rw [hsec]
  unfold powThreeHalves
  rw [hsqrt, habscube]
  field_simp [ne_of_gt ha, ht, hc, hat, hac] <;> ring

end
end ProofGap.Exercise1602

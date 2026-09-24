import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace ProofGap.Exercise4237

noncomputable section

open scoped Interval

abbrev Vec3 := ℝ × ℝ × ℝ

def curveMap (a b t : ℝ) : Vec3 :=
  (a * Real.cos t, a * Real.sin t, b * t)

def speed (a b : ℝ) : ℝ :=
  Real.sqrt (a ^ 2 + b ^ 2)

def weight (p : Vec3) : ℝ :=
  p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2

def weightedLength (a b : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..2 * Real.pi,
    weight (curveMap a b t) * speed a b

theorem gap1 (a b t : ℝ) :
    speed a b = Real.sqrt (a ^ 2 + b ^ 2) := by
  rfl

theorem gap2 (a b : ℝ) :
    weightedLength a b =
      Real.sqrt (a ^ 2 + b ^ 2) *
        ∫ t in (0 : ℝ)..2 * Real.pi, a ^ 2 + b ^ 2 * t ^ 2 := by
  calc
    weightedLength a b =
        (∫ t in (0 : ℝ)..2 * Real.pi, weight (curveMap a b t)) *
          Real.sqrt (a ^ 2 + b ^ 2) := by
      rw [weightedLength, speed, intervalIntegral.integral_mul_const]
    _ = Real.sqrt (a ^ 2 + b ^ 2) *
        ∫ t in (0 : ℝ)..2 * Real.pi, a ^ 2 + b ^ 2 * t ^ 2 := by
      rw [mul_comm]
      congr 1
      apply intervalIntegral.integral_congr
      intro t _
      have htrig :
          Real.cos t ^ 2 + Real.sin t ^ 2 = 1 := by
        simpa [add_comm] using Real.sin_sq_add_cos_sq t
      simp only [weight, curveMap]
      calc
        (a * Real.cos t) ^ 2 + (a * Real.sin t) ^ 2 +
            (b * t) ^ 2 =
            a ^ 2 * (Real.cos t ^ 2 + Real.sin t ^ 2) +
              b ^ 2 * t ^ 2 := by ring
        _ = a ^ 2 + b ^ 2 * t ^ 2 := by rw [htrig]; ring

theorem gap3 (a b : ℝ) :
    Real.sqrt (a ^ 2 + b ^ 2) *
        (∫ t in (0 : ℝ)..2 * Real.pi, a ^ 2 + b ^ 2 * t ^ 2) =
      2 * Real.pi / 3 *
        (3 * a ^ 2 + 4 * Real.pi ^ 2 * b ^ 2) *
          Real.sqrt (a ^ 2 + b ^ 2) := by
  have hconst :
      IntervalIntegrable (fun _t : ℝ => a ^ 2) MeasureTheory.volume
        0 (2 * Real.pi) :=
    intervalIntegrable_const
  have hquad :
      IntervalIntegrable (fun t : ℝ => b ^ 2 * t ^ 2) MeasureTheory.volume
        0 (2 * Real.pi) :=
    (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable
      0 (2 * Real.pi)
  rw [intervalIntegral.integral_add hconst hquad,
    intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul,
    integral_pow]
  simp only [smul_eq_mul]
  ring

theorem gap4 (a b : ℝ) :
    weightedLength a b =
      2 * Real.pi / 3 *
        (3 * a ^ 2 + 4 * Real.pi ^ 2 * b ^ 2) *
          Real.sqrt (a ^ 2 + b ^ 2) := by
  exact (gap2 a b).trans (gap3 a b)

end

end ProofGap.Exercise4237

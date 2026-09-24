import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace ProofGap.Exercise4231

noncomputable section

open scoped Interval

abbrev Vec3 := ℝ × ℝ × ℝ

def curveMap (t : ℝ) : Vec3 :=
  (3 * t, 3 * t ^ 2, 2 * t ^ 3)

def derivativeVector (t : ℝ) : Vec3 :=
  (3, 6 * t, 6 * t ^ 2)

def sqNorm (v : Vec3) : ℝ :=
  v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2

def rawSpeed (t : ℝ) : ℝ :=
  Real.sqrt (sqNorm (derivativeVector t))

def speed (t : ℝ) : ℝ :=
  3 * (2 * t ^ 2 + 1)

def curveLength : ℝ :=
  ∫ t in (0 : ℝ)..1, rawSpeed t

theorem gap1 (t : ℝ) :
    rawSpeed t =
      Real.sqrt
        ((derivativeVector t).1 ^ 2 +
          (derivativeVector t).2.1 ^ 2 +
          (derivativeVector t).2.2 ^ 2) := by
  rfl

theorem gap2 (t : ℝ) :
    rawSpeed t = speed t := by
  unfold rawSpeed sqNorm derivativeVector speed
  rw [show 3 ^ 2 + (6 * t) ^ 2 + (6 * t ^ 2) ^ 2 =
      (3 * (2 * t ^ 2 + 1)) ^ 2 by ring]
  rw [Real.sqrt_sq]
  positivity

theorem gap3 (t : ℝ) :
    rawSpeed t = 3 * (2 * t ^ 2 + 1) := by
  simpa [speed] using gap2 t

theorem gap4 :
    curveLength =
      ∫ t in (0 : ℝ)..1, 3 * (2 * t ^ 2 + 1) := by
  unfold curveLength
  apply intervalIntegral.integral_congr
  intro t _
  exact gap3 t

theorem gap5 :
    (∫ t in (0 : ℝ)..1, 3 * (2 * t ^ 2 + 1)) = 5 := by
  have hquad :
      IntervalIntegrable (fun t : ℝ => 6 * t ^ 2)
        MeasureTheory.volume 0 1 :=
    (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable 0 1
  have hconst :
      IntervalIntegrable (fun _t : ℝ => (3 : ℝ))
        MeasureTheory.volume 0 1 :=
    intervalIntegrable_const
  calc
    (∫ t in (0 : ℝ)..1, 3 * (2 * t ^ 2 + 1)) =
        ∫ t in (0 : ℝ)..1, 6 * t ^ 2 + 3 := by
      congr 1
      funext t
      ring
    _ = (∫ t in (0 : ℝ)..1, 6 * t ^ 2) +
        ∫ _t in (0 : ℝ)..1, (3 : ℝ) :=
      intervalIntegral.integral_add hquad hconst
    _ = 5 := by
      rw [intervalIntegral.integral_const_mul, integral_pow,
        intervalIntegral.integral_const]
      norm_num

theorem gap6 :
    curveLength = 5 := by
  exact gap4.trans gap5

end

end ProofGap.Exercise4231

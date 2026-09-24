import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4232

noncomputable section

open MeasureTheory

abbrev Vec3 := ℝ × ℝ × ℝ

def curveMap (t : ℝ) : Vec3 :=
  (Real.exp (-t) * Real.cos t,
    Real.exp (-t) * Real.sin t, Real.exp (-t))

def curve : Set Vec3 :=
  curveMap '' Set.Ioi 0

def rawSpeed (t : ℝ) : ℝ :=
  Real.sqrt
    (Real.exp (-2 * t) * (Real.cos t - Real.sin t) ^ 2 +
      Real.exp (-2 * t) * (Real.cos t + Real.sin t) ^ 2 +
      Real.exp (-2 * t))

def speed (t : ℝ) : ℝ :=
  Real.sqrt 3 * Real.exp (-t)

def curveLength : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), rawSpeed t

theorem gap1 (t : ℝ) :
    rawSpeed t =
      Real.sqrt
        (Real.exp (-2 * t) * (Real.cos t - Real.sin t) ^ 2 +
          Real.exp (-2 * t) * (Real.cos t + Real.sin t) ^ 2 +
          Real.exp (-2 * t)) := by
  rfl

theorem gap2 (t : ℝ) :
    rawSpeed t = speed t := by
  unfold rawSpeed speed
  have hexp : Real.exp (-2 * t) = Real.exp (-t) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1 <;> ring
  have hrad :
      Real.exp (-2 * t) * (Real.cos t - Real.sin t) ^ 2 +
          Real.exp (-2 * t) * (Real.cos t + Real.sin t) ^ 2 +
          Real.exp (-2 * t) =
        (Real.sqrt 3 * Real.exp (-t)) ^ 2 := by
    calc
      Real.exp (-2 * t) * (Real.cos t - Real.sin t) ^ 2 +
            Real.exp (-2 * t) * (Real.cos t + Real.sin t) ^ 2 +
            Real.exp (-2 * t) =
          Real.exp (-2 * t) *
            (2 * (Real.sin t ^ 2 + Real.cos t ^ 2) + 1) := by ring
      _ = Real.exp (-2 * t) * 3 := by
        rw [Real.sin_sq_add_cos_sq]
        ring
      _ = (Real.sqrt 3 * Real.exp (-t)) ^ 2 := by
        rw [hexp, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
        ring
  have hpos : 0 < Real.sqrt 3 * Real.exp (-t) :=
    mul_pos (Real.sqrt_pos.2 (by norm_num)) (Real.exp_pos _)
  rw [hrad, Real.sqrt_sq_eq_abs, abs_of_pos hpos]

theorem gap3 (t : ℝ) :
    rawSpeed t = Real.sqrt 3 * Real.exp (-t) := by
  simpa [speed] using gap2 t

theorem gap4 :
    curveLength =
      Real.sqrt 3 * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) := by
  unfold curveLength
  calc
    (∫ t in Set.Ioi (0 : ℝ), rawSpeed t) =
        ∫ t in Set.Ioi (0 : ℝ), Real.sqrt 3 * Real.exp (-t) := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall (fun t => gap3 t)
    _ = Real.sqrt 3 * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) := by
      rw [MeasureTheory.integral_const_mul]

theorem gap5 :
    Real.sqrt 3 * (∫ t in Set.Ioi (0 : ℝ), Real.exp (-t)) =
      Real.sqrt 3 := by
  have hone : Real.Gamma (1 : ℝ) = 1 := Real.Gamma_one
  rw [Real.Gamma_eq_integral (s := (1 : ℝ)) (by norm_num)] at hone
  have hint :
      (∫ t in Set.Ioi (0 : ℝ), Real.exp (-t)) = 1 := by
    simpa using hone
  simpa [hint]

theorem gap6 :
    curveLength = Real.sqrt 3 := by
  exact gap4.trans gap5

end

end ProofGap.Exercise4232

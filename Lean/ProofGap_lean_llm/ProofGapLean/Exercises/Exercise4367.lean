import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4367

noncomputable section

open scoped Interval

abbrev Vec3 := ℝ × ℝ × ℝ

def normalCosines : Vec3 :=
  (1 / Real.sqrt 3, 1 / Real.sqrt 3, 1 / Real.sqrt 3)

def xCoord (a t : ℝ) : ℝ :=
  a / Real.sqrt 2 * (Real.cos t / Real.sqrt 3 - Real.sin t)

def yCoord (a t : ℝ) : ℝ :=
  a / Real.sqrt 2 * (Real.cos t / Real.sqrt 3 + Real.sin t)

def zCoord (a t : ℝ) : ℝ :=
  a / Real.sqrt 2 * (-2 / Real.sqrt 3) * Real.cos t

def xDeriv (a t : ℝ) : ℝ :=
  a / Real.sqrt 2 * (-Real.sin t / Real.sqrt 3 - Real.cos t)

def yDeriv (a t : ℝ) : ℝ :=
  a / Real.sqrt 2 * (-Real.sin t / Real.sqrt 3 + Real.cos t)

def zDeriv (a t : ℝ) : ℝ :=
  a / Real.sqrt 2 * (2 / Real.sqrt 3) * Real.sin t

def lineIntegral (a : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..2 * Real.pi,
    yCoord a t * xDeriv a t +
      zCoord a t * yDeriv a t +
      xCoord a t * zDeriv a t

def stokesSurfaceFlux (a : ℝ) : ℝ :=
  -((normalCosines).1 + (normalCosines).2.1 +
      (normalCosines).2.2) * Real.pi * a ^ 2

def parameterReducedIntegral (a : ℝ) : ℝ :=
  a ^ 2 / 2 *
    ∫ t in (0 : ℝ)..2 * Real.pi,
      (-1 / Real.sqrt 3 - 2 / Real.sqrt 3)

private theorem three_div_sqrt_three :
    (3 : ℝ) / Real.sqrt 3 = Real.sqrt 3 := by
  have hs3 : Real.sqrt (3 : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hs3sq : Real.sqrt (3 : ℝ) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  calc
    (3 : ℝ) / Real.sqrt 3 = Real.sqrt 3 ^ 2 / Real.sqrt 3 := by
      rw [hs3sq]
    _ = Real.sqrt 3 := by
      field_simp [hs3] <;> ring

private theorem lineIntegrandValue (a t : ℝ) :
    yCoord a t * xDeriv a t +
        zCoord a t * yDeriv a t +
        xCoord a t * zDeriv a t =
      -Real.sqrt 3 * a ^ 2 / 2 := by
  have hs2 : Real.sqrt (2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hs3 : Real.sqrt (3 : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hs2sq : Real.sqrt (2 : ℝ) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hs3sq : Real.sqrt (3 : ℝ) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  have hq :
      (a / Real.sqrt 2) * (a / Real.sqrt 2) = a ^ 2 / 2 := by
    calc
      (a / Real.sqrt 2) * (a / Real.sqrt 2) =
          a ^ 2 / Real.sqrt 2 ^ 2 := by
            field_simp [hs2] <;> ring
      _ = a ^ 2 / 2 := by rw [hs2sq]
  have hthree : 3 / Real.sqrt 3 ^ 2 = (1 : ℝ) := by
    rw [hs3sq]
    norm_num
  have htrig :
      (Real.cos t / Real.sqrt 3 + Real.sin t) *
          (-Real.sin t / Real.sqrt 3 - Real.cos t) +
        ((-2 / Real.sqrt 3) * Real.cos t) *
          (-Real.sin t / Real.sqrt 3 + Real.cos t) +
        (Real.cos t / Real.sqrt 3 - Real.sin t) *
          ((2 / Real.sqrt 3) * Real.sin t) =
        -Real.sqrt 3 := by
    calc
      (Real.cos t / Real.sqrt 3 + Real.sin t) *
            (-Real.sin t / Real.sqrt 3 - Real.cos t) +
          ((-2 / Real.sqrt 3) * Real.cos t) *
            (-Real.sin t / Real.sqrt 3 + Real.cos t) +
          (Real.cos t / Real.sqrt 3 - Real.sin t) *
            ((2 / Real.sqrt 3) * Real.sin t) =
          Real.cos t * Real.sin t *
              (3 / Real.sqrt 3 ^ 2 - 1) -
            (3 / Real.sqrt 3) *
              (Real.sin t ^ 2 + Real.cos t ^ 2) := by
                field_simp [hs3] <;> ring
      _ = -Real.sqrt 3 := by
        rw [hthree, three_div_sqrt_three, Real.sin_sq_add_cos_sq]
        ring
  unfold yCoord xDeriv zCoord yDeriv xCoord zDeriv
  calc
    _ =
        (a / Real.sqrt 2) * (a / Real.sqrt 2) *
          ((Real.cos t / Real.sqrt 3 + Real.sin t) *
              (-Real.sin t / Real.sqrt 3 - Real.cos t) +
            ((-2 / Real.sqrt 3) * Real.cos t) *
              (-Real.sin t / Real.sqrt 3 + Real.cos t) +
            (Real.cos t / Real.sqrt 3 - Real.sin t) *
              ((2 / Real.sqrt 3) * Real.sin t)) := by ring
    _ =
        (a ^ 2 / 2) *
          ((Real.cos t / Real.sqrt 3 + Real.sin t) *
              (-Real.sin t / Real.sqrt 3 - Real.cos t) +
            ((-2 / Real.sqrt 3) * Real.cos t) *
              (-Real.sin t / Real.sqrt 3 + Real.cos t) +
            (Real.cos t / Real.sqrt 3 - Real.sin t) *
              ((2 / Real.sqrt 3) * Real.sin t)) := by rw [hq]
    _ = (a ^ 2 / 2) * (-Real.sqrt 3) := by rw [htrig]
    _ = -Real.sqrt 3 * a ^ 2 / 2 := by ring

private theorem lineIntegralValue (a : ℝ) :
    lineIntegral a = -Real.sqrt 3 * Real.pi * a ^ 2 := by
  unfold lineIntegral
  simp_rw [lineIntegrandValue]
  simp [intervalIntegral.integral_const] <;> ring

private theorem reducedIntegrandValue :
    (-1 / Real.sqrt 3 - 2 / Real.sqrt 3 : ℝ) = -Real.sqrt 3 := by
  calc
    (-1 / Real.sqrt 3 - 2 / Real.sqrt 3 : ℝ) =
        -(3 / Real.sqrt 3) := by ring
    _ = -Real.sqrt 3 := by rw [three_div_sqrt_three]

private theorem parameterIntegralValue (a : ℝ) :
    parameterReducedIntegral a =
      -Real.sqrt 3 * Real.pi * a ^ 2 := by
  unfold parameterReducedIntegral
  simp_rw [reducedIntegrandValue]
  simp [intervalIntegral.integral_const] <;> ring

theorem gap1 :
    (normalCosines).1 = 1 / Real.sqrt 3 := by
  rfl

theorem gap2 :
    (normalCosines).2.1 = 1 / Real.sqrt 3 := by
  rfl

theorem gap3 :
    (normalCosines).2.2 = 1 / Real.sqrt 3 := by
  rfl

theorem gap4 (a : ℝ) (ha : 0 < a) :
    lineIntegral a = stokesSurfaceFlux a := by
  rw [lineIntegralValue]
  change
    -Real.sqrt 3 * Real.pi * a ^ 2 =
      -(1 / Real.sqrt 3 + 1 / Real.sqrt 3 + 1 / Real.sqrt 3) *
        Real.pi * a ^ 2
  calc
    -Real.sqrt 3 * Real.pi * a ^ 2 =
        -(3 / Real.sqrt 3) * Real.pi * a ^ 2 := by
          rw [three_div_sqrt_three]
    _ =
        -(1 / Real.sqrt 3 + 1 / Real.sqrt 3 + 1 / Real.sqrt 3) *
          Real.pi * a ^ 2 := by ring

theorem gap5 (a : ℝ) (ha : 0 < a) :
    lineIntegral a = -Real.sqrt 3 * Real.pi * a ^ 2 := by
  exact lineIntegralValue a

theorem gap6 (a t : ℝ) :
    xCoord a t =
      a / Real.sqrt 2 *
        (Real.cos t / Real.sqrt 3 - Real.sin t) := by
  rfl

theorem gap7 (a t : ℝ) :
    yCoord a t =
      a / Real.sqrt 2 *
        (Real.cos t / Real.sqrt 3 + Real.sin t) := by
  rfl

theorem gap8 (a t : ℝ) :
    zCoord a t =
      a / Real.sqrt 2 * (-2 / Real.sqrt 3) * Real.cos t := by
  rfl

theorem gap9 (a : ℝ) (ha : 0 < a) :
    lineIntegral a = parameterReducedIntegral a := by
  calc
    lineIntegral a = -Real.sqrt 3 * Real.pi * a ^ 2 := lineIntegralValue a
    _ = parameterReducedIntegral a := (parameterIntegralValue a).symm

theorem gap10 (a : ℝ) (ha : 0 < a) :
    parameterReducedIntegral a =
      -Real.sqrt 3 * Real.pi * a ^ 2 := by
  exact parameterIntegralValue a

theorem gap11 (a : ℝ) (ha : 0 < a) :
    lineIntegral a = -Real.sqrt 3 * Real.pi * a ^ 2 := by
  exact lineIntegralValue a

end

end ProofGap.Exercise4367

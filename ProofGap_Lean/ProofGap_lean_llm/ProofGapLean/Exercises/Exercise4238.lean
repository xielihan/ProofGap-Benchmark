import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise4238

noncomputable section

open scoped Interval

abbrev Vec3 := ℝ × ℝ × ℝ

def originalCircle (a : ℝ) : Set Vec3 :=
  {p |
    p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 = a ^ 2 ∧
      p.1 + p.2.1 + p.2.2 = 0}

def rotatedCircle (a : ℝ) : Set Vec3 :=
  {p | p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 = a ^ 2 ∧ p.2.2 = 0}

def toOriginal (p : Vec3) : Vec3 :=
  (p.1 / Real.sqrt 2 + p.2.1 / Real.sqrt 6 + p.2.2 / Real.sqrt 3,
    -p.1 / Real.sqrt 2 + p.2.1 / Real.sqrt 6 + p.2.2 / Real.sqrt 3,
    -2 * p.2.1 / Real.sqrt 6 + p.2.2 / Real.sqrt 3)

def orthogonalPreimage (a : ℝ) : Set Vec3 :=
  {p | toOriginal p ∈ originalCircle a}

def rotatedMap (a φ : ℝ) : Vec3 :=
  (a * Real.cos φ, a * Real.sin φ, 0)

def originalMap (a φ : ℝ) : Vec3 :=
  toOriginal (rotatedMap a φ)

def momentX (a : ℝ) : ℝ :=
  ∫ φ in (0 : ℝ)..2 * Real.pi, (originalMap a φ).1 ^ 2 * a

def momentY (a : ℝ) : ℝ :=
  ∫ φ in (0 : ℝ)..2 * Real.pi, (originalMap a φ).2.1 ^ 2 * a

def momentZ (a : ℝ) : ℝ :=
  ∫ φ in (0 : ℝ)..2 * Real.pi, (originalMap a φ).2.2 ^ 2 * a

def totalMoment (a : ℝ) : ℝ :=
  ∫ φ in (0 : ℝ)..2 * Real.pi,
    ((originalMap a φ).1 ^ 2 + (originalMap a φ).2.1 ^ 2 +
      (originalMap a φ).2.2 ^ 2) * a

def circleLength (a : ℝ) : ℝ :=
  2 * Real.pi * a

def rotatedXMoment (a : ℝ) : ℝ :=
  ∫ φ in (0 : ℝ)..2 * Real.pi,
    (rotatedMap a φ).1 ^ 2 * a

def rotatedCrossMoment (a : ℝ) : ℝ :=
  ∫ φ in (0 : ℝ)..2 * Real.pi,
    (rotatedMap a φ).1 * (rotatedMap a φ).2.1 * a

private def pg4238_cosSqPrimitive (x : ℝ) : ℝ :=
  x / 2 + Real.sin x * Real.cos x / 2

private def pg4238_sinSqPrimitive (x : ℝ) : ℝ :=
  x / 2 - Real.sin x * Real.cos x / 2

private def pg4238_crossPrimitive (x : ℝ) : ℝ :=
  Real.sin x ^ 2 / 2

private theorem pg4238_hasDerivAt_cosSqPrimitive (x : ℝ) :
    HasDerivAt pg4238_cosSqPrimitive (Real.cos x ^ 2) x := by
  unfold pg4238_cosSqPrimitive
  convert ((hasDerivAt_id x).div_const 2).add
      (((Real.hasDerivAt_sin x).mul (Real.hasDerivAt_cos x)).div_const 2) using 1 <;>
    try ring
  nlinarith [Real.sin_sq_add_cos_sq x]

private theorem pg4238_hasDerivAt_sinSqPrimitive (x : ℝ) :
    HasDerivAt pg4238_sinSqPrimitive (Real.sin x ^ 2) x := by
  unfold pg4238_sinSqPrimitive
  convert ((hasDerivAt_id x).div_const 2).sub
      (((Real.hasDerivAt_sin x).mul (Real.hasDerivAt_cos x)).div_const 2) using 1 <;>
    try ring
  nlinarith [Real.sin_sq_add_cos_sq x]

private theorem pg4238_hasDerivAt_crossPrimitive (x : ℝ) :
    HasDerivAt pg4238_crossPrimitive (Real.cos x * Real.sin x) x := by
  unfold pg4238_crossPrimitive
  convert ((Real.hasDerivAt_sin x).pow 2).div_const 2 using 1 <;> ring

private def pg4238_quadraticPrimitive (A B C x : ℝ) : ℝ :=
  A * pg4238_cosSqPrimitive x + B * pg4238_sinSqPrimitive x +
    C * pg4238_crossPrimitive x

private theorem pg4238_hasDerivAt_quadraticPrimitive (A B C x : ℝ) :
    HasDerivAt (pg4238_quadraticPrimitive A B C)
      (A * Real.cos x ^ 2 + B * Real.sin x ^ 2 +
        C * Real.cos x * Real.sin x) x := by
  unfold pg4238_quadraticPrimitive
  convert
    (((hasDerivAt_const x A).mul (pg4238_hasDerivAt_cosSqPrimitive x)).add
      ((hasDerivAt_const x B).mul (pg4238_hasDerivAt_sinSqPrimitive x))).add
      ((hasDerivAt_const x C).mul (pg4238_hasDerivAt_crossPrimitive x)) using 1 <;>
    ring

private theorem pg4238_integral_trig_quadratic (A B C : ℝ) :
    (∫ x in (0 : ℝ)..2 * Real.pi,
      (A * Real.cos x ^ 2 + B * Real.sin x ^ 2 +
        C * Real.cos x * Real.sin x)) =
      (A + B) * Real.pi := by
  calc
    _ = pg4238_quadraticPrimitive A B C (2 * Real.pi) -
        pg4238_quadraticPrimitive A B C 0 := by
      have hcont : Continuous (fun x : ℝ =>
          A * Real.cos x ^ 2 + B * Real.sin x ^ 2 +
            C * Real.cos x * Real.sin x) :=
        ((continuous_const.mul (Real.continuous_cos.pow 2)).add
          (continuous_const.mul (Real.continuous_sin.pow 2))).add
          ((continuous_const.mul Real.continuous_cos).mul Real.continuous_sin)
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      all_goals
        first
        | exact hcont
        | exact hcont.continuousOn
        | exact hcont.intervalIntegrable _ _
        | (intro x hx; exact pg4238_hasDerivAt_quadraticPrimitive A B C x)
    _ = (A + B) * Real.pi := by
      simp [pg4238_quadraticPrimitive, pg4238_cosSqPrimitive,
        pg4238_sinSqPrimitive, pg4238_crossPrimitive, Real.sin_two_pi]
      ring

private theorem pg4238_momentX_value (a : ℝ) :
    momentX a = 2 * Real.pi * a ^ 3 / 3 := by
  simp only [momentX, originalMap, toOriginal, rotatedMap, zero_div, add_zero]
  calc
    (∫ φ in (0 : ℝ)..2 * Real.pi,
      (a * Real.cos φ / Real.sqrt 2 +
        a * Real.sin φ / Real.sqrt 6) ^ 2 * a) =
      ∫ φ in (0 : ℝ)..2 * Real.pi,
        ((a / Real.sqrt 2) ^ 2 * a) * Real.cos φ ^ 2 +
          ((a / Real.sqrt 6) ^ 2 * a) * Real.sin φ ^ 2 +
          (2 * (a / Real.sqrt 2) * (a / Real.sqrt 6) * a) *
            Real.cos φ * Real.sin φ := by
        apply intervalIntegral.integral_congr
        intro φ hφ
        ring
    _ = (((a / Real.sqrt 2) ^ 2 * a) +
          ((a / Real.sqrt 6) ^ 2 * a)) * Real.pi :=
      pg4238_integral_trig_quadratic _ _ _
    _ = 2 * Real.pi * a ^ 3 / 3 := by
      have h2 : Real.sqrt (2 : ℝ) ^ 2 = 2 :=
        Real.sq_sqrt (by norm_num)
      have h6 : Real.sqrt (6 : ℝ) ^ 2 = 6 :=
        Real.sq_sqrt (by norm_num)
      rw [div_pow, div_pow, h2, h6]
      ring

private theorem pg4238_momentY_value (a : ℝ) :
    momentY a = 2 * Real.pi * a ^ 3 / 3 := by
  simp only [momentY, originalMap, toOriginal, rotatedMap, zero_div, add_zero]
  calc
    (∫ φ in (0 : ℝ)..2 * Real.pi,
      (-(a * Real.cos φ) / Real.sqrt 2 +
        a * Real.sin φ / Real.sqrt 6) ^ 2 * a) =
      ∫ φ in (0 : ℝ)..2 * Real.pi,
        ((-a / Real.sqrt 2) ^ 2 * a) * Real.cos φ ^ 2 +
          ((a / Real.sqrt 6) ^ 2 * a) * Real.sin φ ^ 2 +
          (2 * (-a / Real.sqrt 2) * (a / Real.sqrt 6) * a) *
            Real.cos φ * Real.sin φ := by
        apply intervalIntegral.integral_congr
        intro φ hφ
        ring
    _ = (((-a / Real.sqrt 2) ^ 2 * a) +
          ((a / Real.sqrt 6) ^ 2 * a)) * Real.pi :=
      pg4238_integral_trig_quadratic _ _ _
    _ = 2 * Real.pi * a ^ 3 / 3 := by
      have h2 : Real.sqrt (2 : ℝ) ^ 2 = 2 :=
        Real.sq_sqrt (by norm_num)
      have h6 : Real.sqrt (6 : ℝ) ^ 2 = 6 :=
        Real.sq_sqrt (by norm_num)
      rw [div_pow, div_pow, h2, h6]
      ring

private theorem pg4238_momentZ_value (a : ℝ) :
    momentZ a = 2 * Real.pi * a ^ 3 / 3 := by
  simp only [momentZ, originalMap, toOriginal, rotatedMap, zero_div, add_zero]
  calc
    (∫ φ in (0 : ℝ)..2 * Real.pi,
      (-2 * (a * Real.sin φ) / Real.sqrt 6) ^ 2 * a) =
      ∫ φ in (0 : ℝ)..2 * Real.pi,
        0 * Real.cos φ ^ 2 +
          ((-2 * a / Real.sqrt 6) ^ 2 * a) * Real.sin φ ^ 2 +
          0 * Real.cos φ * Real.sin φ := by
        apply intervalIntegral.integral_congr
        intro φ hφ
        ring
    _ = (0 + ((-2 * a / Real.sqrt 6) ^ 2 * a)) * Real.pi :=
      pg4238_integral_trig_quadratic _ _ _
    _ = 2 * Real.pi * a ^ 3 / 3 := by
      have h6 : Real.sqrt (6 : ℝ) ^ 2 = 6 :=
        Real.sq_sqrt (by norm_num)
      rw [div_pow, h6]
      ring

private theorem pg4238_totalMoment_value (a : ℝ) :
    totalMoment a = 2 * Real.pi * a ^ 3 := by
  simp only [totalMoment, originalMap, toOriginal, rotatedMap, zero_div, add_zero]
  calc
    (∫ φ in (0 : ℝ)..2 * Real.pi,
      ((a * Real.cos φ / Real.sqrt 2 +
          a * Real.sin φ / Real.sqrt 6) ^ 2 +
        (-(a * Real.cos φ) / Real.sqrt 2 +
          a * Real.sin φ / Real.sqrt 6) ^ 2 +
        (-2 * (a * Real.sin φ) / Real.sqrt 6) ^ 2) * a) =
      ∫ φ in (0 : ℝ)..2 * Real.pi,
        (2 * (a / Real.sqrt 2) ^ 2 * a) * Real.cos φ ^ 2 +
          (6 * (a / Real.sqrt 6) ^ 2 * a) * Real.sin φ ^ 2 +
          0 * Real.cos φ * Real.sin φ := by
        apply intervalIntegral.integral_congr
        intro φ hφ
        ring
    _ = (2 * (a / Real.sqrt 2) ^ 2 * a +
          6 * (a / Real.sqrt 6) ^ 2 * a) * Real.pi :=
      pg4238_integral_trig_quadratic _ _ _
    _ = 2 * Real.pi * a ^ 3 := by
      have h2 : Real.sqrt (2 : ℝ) ^ 2 = 2 :=
        Real.sq_sqrt (by norm_num)
      have h6 : Real.sqrt (6 : ℝ) ^ 2 = 6 :=
        Real.sq_sqrt (by norm_num)
      rw [div_pow, div_pow, h2, h6]
      ring

private theorem pg4238_cosIntegral_value (a : ℝ) :
    (∫ φ in (0 : ℝ)..2 * Real.pi,
      a ^ 3 * Real.cos φ ^ 2) = Real.pi * a ^ 3 := by
  calc
    _ = ∫ φ in (0 : ℝ)..2 * Real.pi,
        a ^ 3 * Real.cos φ ^ 2 + 0 * Real.sin φ ^ 2 +
          0 * Real.cos φ * Real.sin φ := by
      apply intervalIntegral.integral_congr
      intro φ hφ
      ring
    _ = (a ^ 3 + 0) * Real.pi := pg4238_integral_trig_quadratic _ _ _
    _ = Real.pi * a ^ 3 := by ring

private theorem pg4238_crossIntegral_value (a : ℝ) :
    (∫ φ in (0 : ℝ)..2 * Real.pi,
      a ^ 3 * Real.cos φ * Real.sin φ) = 0 := by
  calc
    _ = ∫ φ in (0 : ℝ)..2 * Real.pi,
        0 * Real.cos φ ^ 2 + 0 * Real.sin φ ^ 2 +
          a ^ 3 * Real.cos φ * Real.sin φ := by
      apply intervalIntegral.integral_congr
      intro φ hφ
      ring
    _ = (0 + 0) * Real.pi := pg4238_integral_trig_quadratic _ _ _
    _ = 0 := by ring

private theorem pg4238_rotatedXMoment_value (a : ℝ) :
    rotatedXMoment a = Real.pi * a ^ 3 := by
  simp only [rotatedXMoment, rotatedMap]
  calc
    (∫ φ in (0 : ℝ)..2 * Real.pi,
      (a * Real.cos φ) ^ 2 * a) =
      ∫ φ in (0 : ℝ)..2 * Real.pi,
        a ^ 3 * Real.cos φ ^ 2 := by
          apply intervalIntegral.integral_congr
          intro φ hφ
          ring
    _ = Real.pi * a ^ 3 := pg4238_cosIntegral_value a

private theorem pg4238_rotatedCrossMoment_value (a : ℝ) :
    rotatedCrossMoment a = 0 := by
  simp only [rotatedCrossMoment, rotatedMap]
  calc
    (∫ φ in (0 : ℝ)..2 * Real.pi,
      (a * Real.cos φ) * (a * Real.sin φ) * a) =
      ∫ φ in (0 : ℝ)..2 * Real.pi,
        a ^ 3 * Real.cos φ * Real.sin φ := by
          apply intervalIntegral.integral_congr
          intro φ hφ
          ring
    _ = 0 := pg4238_crossIntegral_value a

private theorem pg4238_rotatedWeighted_value (a : ℝ) :
    (∫ φ in (0 : ℝ)..2 * Real.pi,
      (3 * (rotatedMap a φ).1 ^ 2 +
        (rotatedMap a φ).2.1 ^ 2) * a) =
      4 * Real.pi * a ^ 3 := by
  simp only [rotatedMap]
  calc
    (∫ φ in (0 : ℝ)..2 * Real.pi,
      (3 * (a * Real.cos φ) ^ 2 +
        (a * Real.sin φ) ^ 2) * a) =
      ∫ φ in (0 : ℝ)..2 * Real.pi,
        (3 * a ^ 3) * Real.cos φ ^ 2 +
          a ^ 3 * Real.sin φ ^ 2 +
          0 * Real.cos φ * Real.sin φ := by
        apply intervalIntegral.integral_congr
        intro φ hφ
        ring
    _ = (3 * a ^ 3 + a ^ 3) * Real.pi :=
      pg4238_integral_trig_quadratic _ _ _
    _ = 4 * Real.pi * a ^ 3 := by ring

theorem gap1 (a : ℝ) (ha : 0 < a) :
    momentX a = momentY a := by
  rw [pg4238_momentX_value, pg4238_momentY_value]

theorem gap2 (a : ℝ) (ha : 0 < a) :
    momentY a = momentZ a := by
  rw [pg4238_momentY_value, pg4238_momentZ_value]

theorem gap3 (a : ℝ) (ha : 0 < a) :
    momentX a = momentZ a := by
  rw [pg4238_momentX_value, pg4238_momentZ_value]

theorem gap4 (a : ℝ) (ha : 0 < a) :
    momentX a = 1 / 3 * totalMoment a := by
  rw [pg4238_momentX_value, pg4238_totalMoment_value]
  ring

theorem gap5 (a : ℝ) (ha : 0 < a) :
    1 / 3 * totalMoment a = a ^ 2 / 3 * circleLength a := by
  rw [pg4238_totalMoment_value]
  unfold circleLength
  ring

theorem gap6 (a : ℝ) (ha : 0 < a) :
    a ^ 2 / 3 * circleLength a = 2 * Real.pi * a ^ 3 / 3 := by
  unfold circleLength
  ring

theorem gap7 (a : ℝ) (ha : 0 < a) :
    momentX a = 2 * Real.pi * a ^ 3 / 3 := by
  exact pg4238_momentX_value a

theorem gap8 (a : ℝ) (ha : 0 < a) :
    orthogonalPreimage a = rotatedCircle a := by
  apply Set.ext
  intro p
  have h2 : Real.sqrt (2 : ℝ) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt (3 : ℝ) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  have h6 : Real.sqrt (6 : ℝ) ^ 2 = 6 :=
    Real.sq_sqrt (by norm_num)
  have hd2 : (1 / Real.sqrt (2 : ℝ)) ^ 2 = 1 / 2 := by
    rw [div_pow, one_pow, h2]
  have hd3 : (1 / Real.sqrt (3 : ℝ)) ^ 2 = 1 / 3 := by
    rw [div_pow, one_pow, h3]
  have hd6 : (1 / Real.sqrt (6 : ℝ)) ^ 2 = 1 / 6 := by
    rw [div_pow, one_pow, h6]
  have h3ne : Real.sqrt (3 : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have h3div : (3 : ℝ) / Real.sqrt 3 = Real.sqrt 3 := by
    apply (div_eq_iff h3ne).2
    nlinarith [h3]
  have hNorm :
      (p.1 / Real.sqrt 2 + p.2.1 / Real.sqrt 6 +
            p.2.2 / Real.sqrt 3) ^ 2 +
          (-p.1 / Real.sqrt 2 + p.2.1 / Real.sqrt 6 +
            p.2.2 / Real.sqrt 3) ^ 2 +
          (-2 * p.2.1 / Real.sqrt 6 + p.2.2 / Real.sqrt 3) ^ 2 =
        p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 := by
    calc
      _ = p.1 ^ 2 * (2 * (1 / Real.sqrt 2) ^ 2) +
            p.2.1 ^ 2 * (6 * (1 / Real.sqrt 6) ^ 2) +
            p.2.2 ^ 2 * (3 * (1 / Real.sqrt 3) ^ 2) := by ring
      _ = p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 := by
        rw [hd2, hd6, hd3]
        ring
  have hSum :
      p.1 / Real.sqrt 2 + p.2.1 / Real.sqrt 6 +
          p.2.2 / Real.sqrt 3 +
        (-p.1 / Real.sqrt 2 + p.2.1 / Real.sqrt 6 +
          p.2.2 / Real.sqrt 3) +
        (-2 * p.2.1 / Real.sqrt 6 + p.2.2 / Real.sqrt 3) =
      Real.sqrt 3 * p.2.2 := by
    calc
      _ = 3 * p.2.2 / Real.sqrt 3 := by ring
      _ = p.2.2 * (3 / Real.sqrt 3) := by ring
      _ = p.2.2 * Real.sqrt 3 := by rw [h3div]
      _ = Real.sqrt 3 * p.2.2 := by ring
  change
    (((p.1 / Real.sqrt 2 + p.2.1 / Real.sqrt 6 +
            p.2.2 / Real.sqrt 3) ^ 2 +
          (-p.1 / Real.sqrt 2 + p.2.1 / Real.sqrt 6 +
            p.2.2 / Real.sqrt 3) ^ 2 +
          (-2 * p.2.1 / Real.sqrt 6 + p.2.2 / Real.sqrt 3) ^ 2 = a ^ 2 ∧
        p.1 / Real.sqrt 2 + p.2.1 / Real.sqrt 6 +
            p.2.2 / Real.sqrt 3 +
          (-p.1 / Real.sqrt 2 + p.2.1 / Real.sqrt 6 +
            p.2.2 / Real.sqrt 3) +
          (-2 * p.2.1 / Real.sqrt 6 + p.2.2 / Real.sqrt 3) = 0) ↔
      (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 = a ^ 2 ∧ p.2.2 = 0))
  rw [hNorm, hSum]
  simp [h3ne]

theorem gap9 (a : ℝ) (ha : 0 < a) :
    momentX a =
      ∫ φ in (0 : ℝ)..2 * Real.pi,
        ((rotatedMap a φ).1 / Real.sqrt 2 +
          (rotatedMap a φ).2.1 / Real.sqrt 6 +
          (rotatedMap a φ).2.2 / Real.sqrt 3) ^ 2 * a := by
  rfl

theorem gap10 (a : ℝ) (ha : 0 < a) :
    (∫ φ in (0 : ℝ)..2 * Real.pi,
        ((rotatedMap a φ).1 / Real.sqrt 2 +
          (rotatedMap a φ).2.1 / Real.sqrt 6 +
          (rotatedMap a φ).2.2 / Real.sqrt 3) ^ 2 * a) =
      ∫ φ in (0 : ℝ)..2 * Real.pi,
        ((rotatedMap a φ).1 / Real.sqrt 2 +
          (rotatedMap a φ).2.1 / Real.sqrt 6) ^ 2 * a := by
  simp [rotatedMap]

theorem gap11 (a : ℝ) (ha : 0 < a) :
    momentX a =
      ∫ φ in (0 : ℝ)..2 * Real.pi,
        ((rotatedMap a φ).1 / Real.sqrt 2 +
          (rotatedMap a φ).2.1 / Real.sqrt 6) ^ 2 * a := by
  calc
    momentX a =
        ∫ φ in (0 : ℝ)..2 * Real.pi,
          ((rotatedMap a φ).1 / Real.sqrt 2 +
            (rotatedMap a φ).2.1 / Real.sqrt 6 +
            (rotatedMap a φ).2.2 / Real.sqrt 3) ^ 2 * a := gap9 a ha
    _ = ∫ φ in (0 : ℝ)..2 * Real.pi,
          ((rotatedMap a φ).1 / Real.sqrt 2 +
            (rotatedMap a φ).2.1 / Real.sqrt 6) ^ 2 * a := gap10 a ha

theorem gap12 (a : ℝ) (ha : 0 < a) :
    momentX a =
      1 / 6 *
          (∫ φ in (0 : ℝ)..2 * Real.pi,
            (3 * (rotatedMap a φ).1 ^ 2 +
              (rotatedMap a φ).2.1 ^ 2) * a) +
        1 / Real.sqrt 3 * rotatedCrossMoment a := by
  rw [pg4238_momentX_value, pg4238_rotatedWeighted_value,
    pg4238_rotatedCrossMoment_value]
  ring

theorem gap13 (a : ℝ) (ha : 0 < a) :
    momentX a =
      1 / 6 * (a ^ 2 * circleLength a) +
        1 / 3 * rotatedXMoment a +
        1 / Real.sqrt 3 * rotatedCrossMoment a := by
  rw [pg4238_momentX_value, pg4238_rotatedXMoment_value,
    pg4238_rotatedCrossMoment_value]
  unfold circleLength
  ring

theorem gap14 (a : ℝ) (ha : 0 < a) :
    momentX a =
      1 / 3 * Real.pi * a ^ 3 +
        1 / 3 *
          (∫ φ in (0 : ℝ)..2 * Real.pi,
            a ^ 3 * Real.cos φ ^ 2) +
        1 / Real.sqrt 3 *
          ∫ φ in (0 : ℝ)..2 * Real.pi,
            a ^ 3 * Real.cos φ * Real.sin φ := by
  rw [pg4238_momentX_value, pg4238_cosIntegral_value,
    pg4238_crossIntegral_value]
  ring

theorem gap15 (a : ℝ) :
    1 / 3 * Real.pi * a ^ 3 +
          1 / 3 *
            (∫ φ in (0 : ℝ)..2 * Real.pi,
              a ^ 3 * Real.cos φ ^ 2) +
          1 / Real.sqrt 3 *
            (∫ φ in (0 : ℝ)..2 * Real.pi,
              a ^ 3 * Real.cos φ * Real.sin φ) =
      1 / 3 * Real.pi * a ^ 3 + 1 / 3 * Real.pi * a ^ 3 := by
  rw [pg4238_cosIntegral_value, pg4238_crossIntegral_value]
  ring

theorem gap16 (a : ℝ) :
    1 / 3 * Real.pi * a ^ 3 + 1 / 3 * Real.pi * a ^ 3 =
      2 / 3 * Real.pi * a ^ 3 := by
  ring

theorem gap17 (a : ℝ) (ha : 0 < a) :
    momentX a = 2 / 3 * Real.pi * a ^ 3 := by
  rw [pg4238_momentX_value]
  ring

end

end ProofGap.Exercise4238

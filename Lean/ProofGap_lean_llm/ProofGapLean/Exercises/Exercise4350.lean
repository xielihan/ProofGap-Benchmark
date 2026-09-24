import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4350

noncomputable section

open scoped Interval

def coneHeight (x y : ℝ) : ℝ :=
  Real.sqrt (x ^ 2 + y ^ 2)

def projectionDisk (a : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ^ 2 + p.2 ^ 2 ≤ 2 * a * p.1}

def graphAreaFactor (x y : ℝ) : ℝ :=
  Real.sqrt
    (1 + (deriv (fun s => coneHeight s y) x) ^ 2 +
      (deriv (fun s => coneHeight x s) y) ^ 2)

def conePatchMoment (a : ℝ) : ℝ :=
  Real.sqrt 2 *
    ∫ φ in (-Real.pi / 2)..Real.pi / 2,
      ∫ r in (0 : ℝ)..2 * a * Real.cos φ,
        (r ^ 2 * Real.cos φ * Real.sin φ +
          r ^ 2 * (Real.cos φ + Real.sin φ)) * r

private theorem inner_moment_integral (a φ : ℝ) :
    (∫ r in (0 : ℝ)..2 * a * Real.cos φ,
      (r ^ 2 * Real.cos φ * Real.sin φ +
        r ^ 2 * (Real.cos φ + Real.sin φ)) * r) =
      (1 / 4 : ℝ) * (2 * a * Real.cos φ) ^ 4 *
        (Real.cos φ * Real.sin φ + Real.cos φ + Real.sin φ) := by
  let C : ℝ :=
    Real.cos φ * Real.sin φ + Real.cos φ + Real.sin φ
  have hderiv : ∀ r : ℝ,
      HasDerivAt (fun t : ℝ => (1 / 4 : ℝ) * C * t ^ 4)
        ((r ^ 2 * Real.cos φ * Real.sin φ +
          r ^ 2 * (Real.cos φ + Real.sin φ)) * r) r := by
    intro r
    convert ((hasDerivAt_id r).pow 4).const_mul ((1 / 4 : ℝ) * C) using 1 <;>
      dsimp [C, id] <;> ring
  have hFTC :
      (∫ r in (0 : ℝ)..2 * a * Real.cos φ,
        (r ^ 2 * Real.cos φ * Real.sin φ +
          r ^ 2 * (Real.cos φ + Real.sin φ)) * r) =
        ((1 / 4 : ℝ) * C * (2 * a * Real.cos φ) ^ 4) -
          ((1 / 4 : ℝ) * C * (0 : ℝ) ^ 4) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r _ => hderiv r)
      (by
        apply Continuous.intervalIntegrable
        fun_prop)
  rw [hFTC]
  dsimp [C]
  ring

private theorem integral_cos_five (u v : ℝ) :
    (∫ x in u..v, Real.cos x ^ 5) =
      (Real.sin v - (2 / 3 : ℝ) * Real.sin v ^ 3 +
          (1 / 5 : ℝ) * Real.sin v ^ 5) -
        (Real.sin u - (2 / 3 : ℝ) * Real.sin u ^ 3 +
          (1 / 5 : ℝ) * Real.sin u ^ 5) := by
  have hderiv : ∀ x : ℝ,
      HasDerivAt
        (fun t : ℝ =>
          Real.sin t - (2 / 3 : ℝ) * Real.sin t ^ 3 +
            (1 / 5 : ℝ) * Real.sin t ^ 5)
        (Real.cos x ^ 5) x := by
    intro x
    have hcos_sq :
        1 - Real.sin x ^ 2 = Real.cos x ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq x]
    have hpoly :
        Real.cos x - Real.cos x * Real.sin x ^ 2 * 2 +
            Real.cos x * Real.sin x ^ 4 =
          Real.cos x ^ 5 := by
      calc
        Real.cos x - Real.cos x * Real.sin x ^ 2 * 2 +
              Real.cos x * Real.sin x ^ 4 =
            Real.cos x * (1 - Real.sin x ^ 2) ^ 2 := by ring
        _ = Real.cos x * (Real.cos x ^ 2) ^ 2 := by rw [hcos_sq]
        _ = Real.cos x ^ 5 := by ring
    convert
      ((Real.hasDerivAt_sin x).sub
        (((Real.hasDerivAt_sin x).pow 3).const_mul (2 / 3 : ℝ))).add
        (((Real.hasDerivAt_sin x).pow 5).const_mul (1 / 5 : ℝ)) using 1 <;>
      ring_nf
    nlinarith [hpoly]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hderiv x)
    (by
      apply Continuous.intervalIntegrable
      fun_prop)

private theorem integral_cos_five_zero_half :
    (∫ x in (0 : ℝ)..Real.pi / 2, Real.cos x ^ 5) = (8 / 15 : ℝ) := by
  rw [integral_cos_five]
  norm_num [Real.sin_pi_div_two]

private theorem integral_cos_five_symmetric :
    (∫ x in (-Real.pi / 2)..Real.pi / 2, Real.cos x ^ 5) =
      (16 / 15 : ℝ) := by
  have hsin_neg_half : Real.sin (-Real.pi / 2) = -1 := by
    rw [show -Real.pi / 2 = -(Real.pi / 2) by ring,
      Real.sin_neg, Real.sin_pi_div_two]
  rw [integral_cos_five, Real.sin_pi_div_two, hsin_neg_half]
  norm_num

private theorem integral_cos_five_mul_sin_symmetric :
    (∫ x in (-Real.pi / 2)..Real.pi / 2,
      Real.cos x ^ 5 * Real.sin x) = 0 := by
  have hderiv : ∀ x : ℝ,
      HasDerivAt (fun t : ℝ => (-1 / 6 : ℝ) * Real.cos t ^ 6)
        (Real.cos x ^ 5 * Real.sin x) x := by
    intro x
    convert ((Real.hasDerivAt_cos x).pow 6).const_mul (-1 / 6 : ℝ) using 1 <;>
      ring
  have hcos_neg_half : Real.cos (-Real.pi / 2) = 0 := by
    rw [show -Real.pi / 2 = -(Real.pi / 2) by ring,
      Real.cos_neg, Real.cos_pi_div_two]
  have hFTC :
      (∫ x in (-Real.pi / 2)..Real.pi / 2,
        Real.cos x ^ 5 * Real.sin x) =
        (-1 / 6 : ℝ) * Real.cos (Real.pi / 2) ^ 6 -
          (-1 / 6 : ℝ) * Real.cos (-Real.pi / 2) ^ 6 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hderiv x)
      (by
        apply Continuous.intervalIntegrable
        fun_prop)
  rw [hFTC, hcos_neg_half, Real.cos_pi_div_two]
  norm_num

private theorem integral_cos_four_mul_sin_symmetric :
    (∫ x in (-Real.pi / 2)..Real.pi / 2,
      Real.cos x ^ 4 * Real.sin x) = 0 := by
  have hderiv : ∀ x : ℝ,
      HasDerivAt (fun t : ℝ => (-1 / 5 : ℝ) * Real.cos t ^ 5)
        (Real.cos x ^ 4 * Real.sin x) x := by
    intro x
    convert ((Real.hasDerivAt_cos x).pow 5).const_mul (-1 / 5 : ℝ) using 1 <;>
      ring
  have hcos_neg_half : Real.cos (-Real.pi / 2) = 0 := by
    rw [show -Real.pi / 2 = -(Real.pi / 2) by ring,
      Real.cos_neg, Real.cos_pi_div_two]
  have hFTC :
      (∫ x in (-Real.pi / 2)..Real.pi / 2,
        Real.cos x ^ 4 * Real.sin x) =
        (-1 / 5 : ℝ) * Real.cos (Real.pi / 2) ^ 5 -
          (-1 / 5 : ℝ) * Real.cos (-Real.pi / 2) ^ 5 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hderiv x)
      (by
        apply Continuous.intervalIntegrable
        fun_prop)
  rw [hFTC, hcos_neg_half, Real.cos_pi_div_two]
  norm_num

theorem gap1
    (x y : ℝ) (hne : (x, y) ≠ (0, 0)) :
    graphAreaFactor x y =
      Real.sqrt
        (1 + x ^ 2 / (x ^ 2 + y ^ 2) +
          y ^ 2 / (x ^ 2 + y ^ 2)) := by
  have hsum_ne : x ^ 2 + y ^ 2 ≠ 0 := by
    intro hzero
    have hx0 : x = 0 := by
      nlinarith [sq_nonneg x, sq_nonneg y]
    have hy0 : y = 0 := by
      nlinarith [sq_nonneg x, sq_nonneg y]
    exact hne (by simp [hx0, hy0])
  have hsum_pos : 0 < x ^ 2 + y ^ 2 :=
    lt_of_le_of_ne (add_nonneg (sq_nonneg x) (sq_nonneg y))
      (Ne.symm hsum_ne)
  have hsqrt_ne : Real.sqrt (x ^ 2 + y ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hsum_pos)
  have hxinner :
      HasDerivAt (fun s : ℝ => s ^ 2 + y ^ 2) (2 * x) x := by
    simpa [id, mul_comm] using
      (((hasDerivAt_id x).pow 2).add_const (y ^ 2))
  have hyinner :
      HasDerivAt (fun s : ℝ => x ^ 2 + s ^ 2) (2 * y) y := by
    convert (((hasDerivAt_id y).pow 2).const_add (x ^ 2)) using 1 <;>
      simp [id, mul_comm]
  have hxchain :
      HasDerivAt (fun s : ℝ => Real.sqrt (s ^ 2 + y ^ 2))
        (1 / (2 * Real.sqrt (x ^ 2 + y ^ 2)) * (2 * x)) x := by
    simpa [Function.comp_def] using
      ((Real.hasDerivAt_sqrt hsum_ne).comp x hxinner)
  have hychain :
      HasDerivAt (fun s : ℝ => Real.sqrt (x ^ 2 + s ^ 2))
        (1 / (2 * Real.sqrt (x ^ 2 + y ^ 2)) * (2 * y)) y := by
    simpa [Function.comp_def] using
      ((Real.hasDerivAt_sqrt hsum_ne).comp y hyinner)
  have hxderiv :
      deriv (fun s => coneHeight s y) x =
        x / Real.sqrt (x ^ 2 + y ^ 2) := by
    change deriv (fun s : ℝ => Real.sqrt (s ^ 2 + y ^ 2)) x = _
    calc
      deriv (fun s : ℝ => Real.sqrt (s ^ 2 + y ^ 2)) x =
          1 / (2 * Real.sqrt (x ^ 2 + y ^ 2)) * (2 * x) :=
        hxchain.deriv
      _ = x / Real.sqrt (x ^ 2 + y ^ 2) := by
        field_simp [hsqrt_ne]
        <;> ring
  have hyderiv :
      deriv (fun s => coneHeight x s) y =
        y / Real.sqrt (x ^ 2 + y ^ 2) := by
    change deriv (fun s : ℝ => Real.sqrt (x ^ 2 + s ^ 2)) y = _
    calc
      deriv (fun s : ℝ => Real.sqrt (x ^ 2 + s ^ 2)) y =
          1 / (2 * Real.sqrt (x ^ 2 + y ^ 2)) * (2 * y) :=
        hychain.deriv
      _ = y / Real.sqrt (x ^ 2 + y ^ 2) := by
        field_simp [hsqrt_ne]
        <;> ring
  unfold graphAreaFactor
  rw [hxderiv, hyderiv]
  congr 1
  simp [div_pow, Real.sq_sqrt (le_of_lt hsum_pos)]

theorem gap2
    (x y : ℝ) (hne : (x, y) ≠ (0, 0)) :
    Real.sqrt
        (1 + x ^ 2 / (x ^ 2 + y ^ 2) +
          y ^ 2 / (x ^ 2 + y ^ 2)) =
      Real.sqrt 2 := by
  have hsum_ne : x ^ 2 + y ^ 2 ≠ 0 := by
    intro hzero
    have hx0 : x = 0 := by
      nlinarith [sq_nonneg x, sq_nonneg y]
    have hy0 : y = 0 := by
      nlinarith [sq_nonneg x, sq_nonneg y]
    exact hne (by simp [hx0, hy0])
  apply congrArg Real.sqrt
  field_simp [hsum_ne]
  <;> ring

theorem gap3
    (x y : ℝ) (hne : (x, y) ≠ (0, 0)) :
    graphAreaFactor x y = Real.sqrt 2 := by
  exact (gap1 x y hne).trans (gap2 x y hne)

theorem gap4 (a : ℝ) (ha : 0 < a) :
    conePatchMoment a =
      Real.sqrt 2 *
        ∫ φ in (-Real.pi / 2)..Real.pi / 2,
          ∫ r in (0 : ℝ)..2 * a * Real.cos φ,
            (r ^ 2 * Real.cos φ * Real.sin φ +
              r ^ 2 * (Real.cos φ + Real.sin φ)) * r := by
  rfl

theorem gap5 (a : ℝ) (ha : 0 < a) :
    conePatchMoment a =
      Real.sqrt 2 *
        ∫ φ in (-Real.pi / 2)..Real.pi / 2,
          (1 / 4 : ℝ) * (2 * a * Real.cos φ) ^ 4 *
            Real.cos φ := by
  unfold conePatchMoment
  apply congrArg (fun z : ℝ => Real.sqrt 2 * z)
  simp_rw [inner_moment_integral]
  have hrewrite :
      (fun φ : ℝ =>
          (1 / 4 : ℝ) * (2 * a * Real.cos φ) ^ 4 *
            (Real.cos φ * Real.sin φ + Real.cos φ + Real.sin φ)) =
        (fun φ : ℝ =>
          (1 / 4 : ℝ) * (2 * a * Real.cos φ) ^ 4 * Real.cos φ +
          ((1 / 4 : ℝ) * (2 * a) ^ 4) *
            (Real.cos φ ^ 5 * Real.sin φ) +
          ((1 / 4 : ℝ) * (2 * a) ^ 4) *
            (Real.cos φ ^ 4 * Real.sin φ)) := by
    funext φ
    ring
  rw [hrewrite]
  have hmain_int : IntervalIntegrable
      (fun φ : ℝ =>
        (1 / 4 : ℝ) * (2 * a * Real.cos φ) ^ 4 * Real.cos φ)
      MeasureTheory.volume (-Real.pi / 2) (Real.pi / 2) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hodd5_int : IntervalIntegrable
      (fun φ : ℝ =>
        ((1 / 4 : ℝ) * (2 * a) ^ 4) *
          (Real.cos φ ^ 5 * Real.sin φ))
      MeasureTheory.volume (-Real.pi / 2) (Real.pi / 2) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hodd4_int : IntervalIntegrable
      (fun φ : ℝ =>
        ((1 / 4 : ℝ) * (2 * a) ^ 4) *
          (Real.cos φ ^ 4 * Real.sin φ))
      MeasureTheory.volume (-Real.pi / 2) (Real.pi / 2) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hsum_int : IntervalIntegrable
      (fun φ : ℝ =>
        (1 / 4 : ℝ) * (2 * a * Real.cos φ) ^ 4 * Real.cos φ +
          ((1 / 4 : ℝ) * (2 * a) ^ 4) *
            (Real.cos φ ^ 5 * Real.sin φ))
      MeasureTheory.volume (-Real.pi / 2) (Real.pi / 2) :=
    hmain_int.add hodd5_int
  rw [intervalIntegral.integral_add hsum_int hodd4_int,
    intervalIntegral.integral_add hmain_int hodd5_int]
  have hodd5 :
      (∫ φ in (-Real.pi / 2)..Real.pi / 2,
        ((1 / 4 : ℝ) * (2 * a) ^ 4) *
          (Real.cos φ ^ 5 * Real.sin φ)) = 0 := by
    rw [intervalIntegral.integral_const_mul,
      integral_cos_five_mul_sin_symmetric]
    ring
  have hodd4 :
      (∫ φ in (-Real.pi / 2)..Real.pi / 2,
        ((1 / 4 : ℝ) * (2 * a) ^ 4) *
          (Real.cos φ ^ 4 * Real.sin φ)) = 0 := by
    rw [intervalIntegral.integral_const_mul,
      integral_cos_four_mul_sin_symmetric]
    ring
  rw [hodd5, hodd4]
  simp

theorem gap6 (a : ℝ) (ha : 0 < a) :
    Real.sqrt 2 *
        (∫ φ in (-Real.pi / 2)..Real.pi / 2,
          (1 / 4 : ℝ) * (2 * a * Real.cos φ) ^ 4 *
            Real.cos φ) =
      8 * Real.sqrt 2 * a ^ 4 *
        (∫ φ in (0 : ℝ)..Real.pi / 2, Real.cos φ ^ 5) := by
  have hi :
      (∫ φ in (-Real.pi / 2)..Real.pi / 2,
        (1 / 4 : ℝ) * (2 * a * Real.cos φ) ^ 4 * Real.cos φ) =
        4 * a ^ 4 *
          (∫ φ in (-Real.pi / 2)..Real.pi / 2, Real.cos φ ^ 5) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro φ hφ
    ring
  rw [hi, integral_cos_five_symmetric, integral_cos_five_zero_half]
  ring

theorem gap7 (a : ℝ) :
    8 * Real.sqrt 2 * a ^ 4 *
        (∫ φ in (0 : ℝ)..Real.pi / 2, Real.cos φ ^ 5) =
      (64 / 15 : ℝ) * Real.sqrt 2 * a ^ 4 := by
  rw [integral_cos_five_zero_half]
  ring

theorem gap8 (a : ℝ) (ha : 0 < a) :
    conePatchMoment a =
      (64 / 15 : ℝ) * Real.sqrt 2 * a ^ 4 := by
  calc
    conePatchMoment a =
        Real.sqrt 2 *
          (∫ φ in (-Real.pi / 2)..Real.pi / 2,
            (1 / 4 : ℝ) * (2 * a * Real.cos φ) ^ 4 *
              Real.cos φ) := gap5 a ha
    _ = 8 * Real.sqrt 2 * a ^ 4 *
          (∫ φ in (0 : ℝ)..Real.pi / 2, Real.cos φ ^ 5) := gap6 a ha
    _ = (64 / 15 : ℝ) * Real.sqrt 2 * a ^ 4 := gap7 a

end

end ProofGap.Exercise4350

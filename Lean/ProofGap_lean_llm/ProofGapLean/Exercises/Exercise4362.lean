import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise4362

noncomputable section

open scoped Interval

abbrev Vec3 := ℝ × ℝ × ℝ

def sphereParam (a φ θ : ℝ) : Vec3 :=
  (a * Real.cos θ * Real.cos φ,
    a * Real.cos θ * Real.sin φ,
    a * Real.sin θ)

def sphereAreaVector (a φ θ : ℝ) : Vec3 :=
  (a ^ 2 * Real.cos θ ^ 2 * Real.cos φ,
    a ^ 2 * Real.cos θ ^ 2 * Real.sin φ,
    a ^ 2 * Real.cos θ * Real.sin θ)

def upperProjectionIntegral (a : ℝ) : ℝ :=
  ∫ φ in (0 : ℝ)..2 * Real.pi,
    ∫ r in (0 : ℝ)..a, r * Real.sqrt (a ^ 2 - r ^ 2)

def lowerProjectionIntegral (a : ℝ) : ℝ :=
  ∫ φ in (0 : ℝ)..2 * Real.pi,
    ∫ r in (0 : ℝ)..a, -r * Real.sqrt (a ^ 2 - r ^ 2)

def xFlux (a : ℝ) : ℝ :=
  ∫ φ in (0 : ℝ)..2 * Real.pi,
    ∫ θ in -Real.pi / 2..Real.pi / 2,
      (sphereParam a φ θ).1 * (sphereAreaVector a φ θ).1

def yFlux (a : ℝ) : ℝ :=
  ∫ φ in (0 : ℝ)..2 * Real.pi,
    ∫ θ in -Real.pi / 2..Real.pi / 2,
      (sphereParam a φ θ).2.1 * (sphereAreaVector a φ θ).2.1

def zFlux (a : ℝ) : ℝ :=
  ∫ φ in (0 : ℝ)..2 * Real.pi,
    ∫ θ in -Real.pi / 2..Real.pi / 2,
      (sphereParam a φ θ).2.2 * (sphereAreaVector a φ θ).2.2

def totalFlux (a : ℝ) : ℝ :=
  xFlux a + yFlux a + zFlux a

private theorem integral_cos_cube :
    (∫ x in -Real.pi / 2..Real.pi / 2, Real.cos x ^ 3) = 4 / 3 := by
  have hderiv : ∀ x ∈ Set.uIcc (-Real.pi / 2) (Real.pi / 2),
      HasDerivAt
        (fun y => Real.sin y - (1 / 3) * Real.sin y ^ 3)
        (Real.cos x ^ 3) x := by
    intro x hx
    have h := (Real.hasDerivAt_sin x).sub
      (((Real.hasDerivAt_sin x).pow 3).const_mul (1 / 3))
    convert h using 1
    norm_num
    calc
      Real.cos x ^ 3 = Real.cos x * Real.cos x ^ 2 := by ring
      _ = Real.cos x * (1 - Real.sin x ^ 2) := by
        rw [← Real.sin_sq_add_cos_sq x]
        ring
      _ = Real.cos x - Real.sin x ^ 2 * Real.cos x := by ring_nf
      _ = Real.cos x - (1 / 3) *
          (3 * Real.sin x ^ 2 * Real.cos x) := by ring
  have hi : IntervalIntegrable (fun x : ℝ => Real.cos x ^ 3)
      MeasureTheory.volume (-Real.pi / 2) (Real.pi / 2) :=
    (Real.continuous_cos.pow 3).intervalIntegrable _ _
  have h := (intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv) hi
  calc
    (∫ x in -Real.pi / 2..Real.pi / 2, Real.cos x ^ 3) =
        (Real.sin (Real.pi / 2) - (1 / 3) * Real.sin (Real.pi / 2) ^ 3) -
          (Real.sin (-Real.pi / 2) -
            (1 / 3) * Real.sin (-Real.pi / 2) ^ 3) := h
    _ = 4 / 3 := by
      have hneg : Real.sin (-Real.pi / 2) = -1 := by
        rw [show -Real.pi / 2 = -(Real.pi / 2) by ring,
          Real.sin_neg, Real.sin_pi_div_two]
      rw [Real.sin_pi_div_two, hneg]
      norm_num

private theorem integral_cos_cube_mul (c : ℝ) :
    (∫ x in -Real.pi / 2..Real.pi / 2, c * Real.cos x ^ 3) = c * (4 / 3) := by
  rw [intervalIntegral.integral_const_mul, integral_cos_cube]

private theorem integral_cos_sin_sq :
    (∫ x in -Real.pi / 2..Real.pi / 2,
      Real.cos x * Real.sin x ^ 2) = 2 / 3 := by
  have hderiv : ∀ x ∈ Set.uIcc (-Real.pi / 2) (Real.pi / 2),
      HasDerivAt
        (fun y => (1 / 3) * Real.sin y ^ 3)
        (Real.cos x * Real.sin x ^ 2) x := by
    intro x hx
    have h := ((Real.hasDerivAt_sin x).pow 3).const_mul (1 / 3)
    convert h using 1 <;> norm_num <;> ring_nf
  have hi : IntervalIntegrable
      (fun x : ℝ => Real.cos x * Real.sin x ^ 2)
      MeasureTheory.volume (-Real.pi / 2) (Real.pi / 2) :=
    (Real.continuous_cos.mul (Real.continuous_sin.pow 2)).intervalIntegrable _ _
  have h := (intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv) hi
  calc
    (∫ x in -Real.pi / 2..Real.pi / 2,
      Real.cos x * Real.sin x ^ 2) =
        (1 / 3) * Real.sin (Real.pi / 2) ^ 3 -
          (1 / 3) * Real.sin (-Real.pi / 2) ^ 3 := h
    _ = 2 / 3 := by
      have hneg : Real.sin (-Real.pi / 2) = -1 := by
        rw [show -Real.pi / 2 = -(Real.pi / 2) by ring,
          Real.sin_neg, Real.sin_pi_div_two]
      rw [Real.sin_pi_div_two, hneg]
      norm_num

private theorem integral_cos_sin_sq_mul (c : ℝ) :
    (∫ x in -Real.pi / 2..Real.pi / 2,
      c * (Real.cos x * Real.sin x ^ 2)) = c * (2 / 3) := by
  rw [intervalIntegral.integral_const_mul, integral_cos_sin_sq]

private theorem integral_cos_sq :
    (∫ x in (0 : ℝ)..2 * Real.pi, Real.cos x ^ 2) = Real.pi := by
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) (2 * Real.pi),
      HasDerivAt
        (fun y => (1 / 2) * y + (1 / 2) * (Real.sin y * Real.cos y))
        (Real.cos x ^ 2) x := by
    intro x hx
    have hp := (Real.hasDerivAt_sin x).mul (Real.hasDerivAt_cos x)
    have h := ((hasDerivAt_id x).const_mul (1 / 2)).add
      (hp.const_mul (1 / 2))
    convert h using 1
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hi : IntervalIntegrable (fun x : ℝ => Real.cos x ^ 2)
      MeasureTheory.volume 0 (2 * Real.pi) :=
    (Real.continuous_cos.pow 2).intervalIntegrable _ _
  have h := (intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv) hi
  convert h using 1 <;> simp [Real.sin_two_pi] <;> ring

private theorem integral_cos_sq_mul (c : ℝ) :
    (∫ x in (0 : ℝ)..2 * Real.pi, c * Real.cos x ^ 2) = c * Real.pi := by
  rw [intervalIntegral.integral_const_mul, integral_cos_sq]

private theorem integral_sin_sq :
    (∫ x in (0 : ℝ)..2 * Real.pi, Real.sin x ^ 2) = Real.pi := by
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) (2 * Real.pi),
      HasDerivAt
        (fun y => (1 / 2) * y - (1 / 2) * (Real.sin y * Real.cos y))
        (Real.sin x ^ 2) x := by
    intro x hx
    have hp := (Real.hasDerivAt_sin x).mul (Real.hasDerivAt_cos x)
    have h := ((hasDerivAt_id x).const_mul (1 / 2)).sub
      (hp.const_mul (1 / 2))
    convert h using 1
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hi : IntervalIntegrable (fun x : ℝ => Real.sin x ^ 2)
      MeasureTheory.volume 0 (2 * Real.pi) :=
    (Real.continuous_sin.pow 2).intervalIntegrable _ _
  have h := (intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv) hi
  convert h using 1 <;> simp [Real.sin_two_pi] <;> ring

private theorem integral_sin_sq_mul (c : ℝ) :
    (∫ x in (0 : ℝ)..2 * Real.pi, c * Real.sin x ^ 2) = c * Real.pi := by
  rw [intervalIntegral.integral_const_mul, integral_sin_sq]

private theorem radial_integral_eval (a : ℝ) (ha : 0 < a) :
    (∫ r in (0 : ℝ)..a, r * Real.sqrt (a ^ 2 - r ^ 2)) = a ^ 3 / 3 := by
  have hderiv : ∀ r ∈ Set.uIcc (0 : ℝ) a,
      HasDerivAt
        (fun x => (-1 / 3) * (a ^ 2 - x ^ 2) ^ (3 / 2 : ℝ))
        (r * Real.sqrt (a ^ 2 - r ^ 2)) r := by
    intro r hr
    have hbase : HasDerivAt (fun x => a ^ 2 - x ^ 2) (-2 * r) r := by
      convert (hasDerivAt_const r (a ^ 2)).sub ((hasDerivAt_id r).pow 2) using 1 <;>
        simp only [id_eq] <;> ring
    have hp :=
      (Real.hasDerivAt_rpow_const (p := (3 / 2 : ℝ))
        (Or.inr (by norm_num))).comp r hbase
    have hc := hp.const_mul (-1 / 3)
    convert hc using 1 <;> norm_num [Real.sqrt_eq_rpow] <;> ring
  have hpow : (a ^ 2) ^ (3 / 2 : ℝ) = a ^ 3 := by
    calc
      (a ^ 2) ^ (3 / 2 : ℝ) =
          (a ^ 2) ^ ((1 : ℝ) + 1 / 2) := by norm_num
      _ = (a ^ 2) ^ (1 : ℝ) * (a ^ 2) ^ (1 / 2 : ℝ) := by
        rw [Real.rpow_add (by positivity : 0 < a ^ 2)]
      _ = a ^ 3 := by
        rw [Real.rpow_one, ← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs,
          abs_of_pos ha]
        ring
  have hi : IntervalIntegrable
      (fun r : ℝ => r * Real.sqrt (a ^ 2 - r ^ 2))
      MeasureTheory.volume 0 a :=
    (continuous_id.mul
      ((continuous_const.sub (continuous_id.pow 2)).sqrt)).intervalIntegrable _ _
  have h := (intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv) hi
  convert h using 1 <;> simp [hpow] <;> ring

private theorem xFlux_eval (a : ℝ) :
    xFlux a = 4 / 3 * Real.pi * a ^ 3 := by
  rw [xFlux]
  simp only [sphereParam, sphereAreaVector]
  rw [show
    (fun φ : ℝ =>
      ∫ θ in -Real.pi / 2..Real.pi / 2,
        (a * Real.cos θ * Real.cos φ) *
          (a ^ 2 * Real.cos θ ^ 2 * Real.cos φ)) =
      (fun φ : ℝ => (a ^ 3 * Real.cos φ ^ 2) * (4 / 3)) by
        funext φ
        calc
          (∫ θ in -Real.pi / 2..Real.pi / 2,
            (a * Real.cos θ * Real.cos φ) *
              (a ^ 2 * Real.cos θ ^ 2 * Real.cos φ)) =
              ∫ θ in -Real.pi / 2..Real.pi / 2,
                (a ^ 3 * Real.cos φ ^ 2) * Real.cos θ ^ 3 := by
                  congr 1
                  funext θ
                  ring
          _ = (a ^ 3 * Real.cos φ ^ 2) * (4 / 3) :=
            integral_cos_cube_mul (a ^ 3 * Real.cos φ ^ 2)]
  rw [show
    (fun φ : ℝ => (a ^ 3 * Real.cos φ ^ 2) * (4 / 3)) =
      (fun φ : ℝ => (4 / 3 * a ^ 3) * Real.cos φ ^ 2) by
        funext φ
        ring]
  rw [integral_cos_sq_mul]
  ring

private theorem yFlux_eval (a : ℝ) :
    yFlux a = 4 / 3 * Real.pi * a ^ 3 := by
  rw [yFlux]
  simp only [sphereParam, sphereAreaVector]
  rw [show
    (fun φ : ℝ =>
      ∫ θ in -Real.pi / 2..Real.pi / 2,
        (a * Real.cos θ * Real.sin φ) *
          (a ^ 2 * Real.cos θ ^ 2 * Real.sin φ)) =
      (fun φ : ℝ => (a ^ 3 * Real.sin φ ^ 2) * (4 / 3)) by
        funext φ
        calc
          (∫ θ in -Real.pi / 2..Real.pi / 2,
            (a * Real.cos θ * Real.sin φ) *
              (a ^ 2 * Real.cos θ ^ 2 * Real.sin φ)) =
              ∫ θ in -Real.pi / 2..Real.pi / 2,
                (a ^ 3 * Real.sin φ ^ 2) * Real.cos θ ^ 3 := by
                  congr 1
                  funext θ
                  ring
          _ = (a ^ 3 * Real.sin φ ^ 2) * (4 / 3) :=
            integral_cos_cube_mul (a ^ 3 * Real.sin φ ^ 2)]
  rw [show
    (fun φ : ℝ => (a ^ 3 * Real.sin φ ^ 2) * (4 / 3)) =
      (fun φ : ℝ => (4 / 3 * a ^ 3) * Real.sin φ ^ 2) by
        funext φ
        ring]
  rw [integral_sin_sq_mul]
  ring

private theorem zFlux_eval (a : ℝ) :
    zFlux a = 4 / 3 * Real.pi * a ^ 3 := by
  rw [zFlux]
  simp only [sphereParam, sphereAreaVector]
  rw [show
    (fun φ : ℝ =>
      ∫ θ in -Real.pi / 2..Real.pi / 2,
        (a * Real.sin θ) *
          (a ^ 2 * Real.cos θ * Real.sin θ)) =
      (fun _ : ℝ => a ^ 3 * (2 / 3)) by
        funext φ
        calc
          (∫ θ in -Real.pi / 2..Real.pi / 2,
            (a * Real.sin θ) *
              (a ^ 2 * Real.cos θ * Real.sin θ)) =
              ∫ θ in -Real.pi / 2..Real.pi / 2,
                a ^ 3 * (Real.cos θ * Real.sin θ ^ 2) := by
                  congr 1
                  funext θ
                  ring
          _ = a ^ 3 * (2 / 3) := integral_cos_sin_sq_mul (a ^ 3)]
  simp
  ring

private theorem upperProjectionIntegral_eval (a : ℝ) (ha : 0 < a) :
    upperProjectionIntegral a = 2 * Real.pi * (a ^ 3 / 3) := by
  rw [upperProjectionIntegral, radial_integral_eval a ha]
  simp
  ring

private theorem lowerProjectionIntegral_eval (a : ℝ) (ha : 0 < a) :
    lowerProjectionIntegral a = -(2 * Real.pi * (a ^ 3 / 3)) := by
  rw [lowerProjectionIntegral]
  have hneg :
      (∫ r in (0 : ℝ)..a, -r * Real.sqrt (a ^ 2 - r ^ 2)) =
        -(∫ r in (0 : ℝ)..a, r * Real.sqrt (a ^ 2 - r ^ 2)) := by
    rw [show
      (fun r : ℝ => -r * Real.sqrt (a ^ 2 - r ^ 2)) =
        (fun r : ℝ => -(r * Real.sqrt (a ^ 2 - r ^ 2))) by
          funext r
          ring]
    rw [intervalIntegral.integral_neg]
  rw [hneg, radial_integral_eval a ha]
  simp
  ring

theorem gap1 (a : ℝ) (ha : 0 < a) :
    totalFlux a = 3 * zFlux a := by
  rw [totalFlux, xFlux_eval a, yFlux_eval a, zFlux_eval a]
  ring

theorem gap2 (a : ℝ) (ha : 0 < a) :
    zFlux a =
      upperProjectionIntegral a - lowerProjectionIntegral a := by
  rw [zFlux_eval a, upperProjectionIntegral_eval a ha,
    lowerProjectionIntegral_eval a ha]
  ring

theorem gap3 (a : ℝ) (ha : 0 < a) :
    zFlux a =
      2 *
        ∫ φ in (0 : ℝ)..2 * Real.pi,
          ∫ r in (0 : ℝ)..a, r * Real.sqrt (a ^ 2 - r ^ 2) := by
  change zFlux a = 2 * upperProjectionIntegral a
  rw [zFlux_eval a, upperProjectionIntegral_eval a ha]
  ring

theorem gap4 (a : ℝ) (ha : 0 < a) :
    2 *
        (∫ φ in (0 : ℝ)..2 * Real.pi,
          ∫ r in (0 : ℝ)..a, r * Real.sqrt (a ^ 2 - r ^ 2)) =
      4 / 3 * Real.pi * a ^ 3 := by
  change 2 * upperProjectionIntegral a = 4 / 3 * Real.pi * a ^ 3
  rw [upperProjectionIntegral_eval a ha]
  ring

theorem gap5 (a : ℝ) (ha : 0 < a) :
    zFlux a = 4 / 3 * Real.pi * a ^ 3 := by
  rw [gap3 a ha, gap4 a ha]

theorem gap6 (a : ℝ) (ha : 0 < a) :
    totalFlux a = 4 * Real.pi * a ^ 3 := by
  rw [gap1 a ha, gap5 a ha]
  ring

end

end ProofGap.Exercise4362

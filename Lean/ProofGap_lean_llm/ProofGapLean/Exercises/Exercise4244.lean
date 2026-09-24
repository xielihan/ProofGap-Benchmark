import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise4244

noncomputable section

open scoped Interval

def curveMap (a t : ℝ) : ℝ × ℝ :=
  (a * (t - Real.sin t), a * (1 - Real.cos t))

def rawSpeed (a t : ℝ) : ℝ :=
  Real.sqrt (a ^ 2 * (1 - Real.cos t) ^ 2 + a ^ 2 * Real.sin t ^ 2)

def speed (a t : ℝ) : ℝ :=
  2 * a * Real.sin (t / 2)

def mass (a ρ₀ : ℝ) : ℝ :=
  ρ₀ * ∫ t in (0 : ℝ)..Real.pi, rawSpeed a t

def xCentroid (a ρ₀ : ℝ) : ℝ :=
  ρ₀ / mass a ρ₀ *
    ∫ t in (0 : ℝ)..Real.pi, (curveMap a t).1 * rawSpeed a t

def yCentroid (a ρ₀ : ℝ) : ℝ :=
  ρ₀ / mass a ρ₀ *
    ∫ t in (0 : ℝ)..Real.pi, (curveMap a t).2 * rawSpeed a t

def xBoundaryTerm (a t : ℝ) : ℝ :=
  -(a * t * Real.cos (t / 2))

private theorem cycloid_integral_from_derivative
    (F f : ℝ → ℝ) (a b : ℝ)
    (hF : ∀ x, HasDerivAt F (f x) x)
    (hf : Continuous f) :
    (∫ x in a..b, f x) = F b - F a := by
  have hd : deriv F = f := by
    funext x
    exact (hF x).deriv
  rw [← hd]
  exact intervalIntegral.integral_deriv_eq_sub
    (fun x _ => (hF x).differentiableAt)
    (by
      simpa [hd] using
        (hf.intervalIntegrable (μ := MeasureTheory.volume) a b))

private theorem cycloid_sin_double_half (t : ℝ) :
    Real.sin t = 2 * Real.sin (t / 2) * Real.cos (t / 2) := by
  calc
    Real.sin t = Real.sin (2 * (t / 2)) := by congr 1 <;> ring
    _ = 2 * Real.sin (t / 2) * Real.cos (t / 2) := by
      rw [Real.sin_two_mul]

private theorem cycloid_cos_double_half (t : ℝ) :
    Real.cos t = 2 * Real.cos (t / 2) ^ 2 - 1 := by
  calc
    Real.cos t = Real.cos (2 * (t / 2)) := by congr 1 <;> ring
    _ = 2 * Real.cos (t / 2) ^ 2 - 1 := by
      rw [Real.cos_two_mul]

private theorem cycloid_hasDerivAt_sin_half (t : ℝ) :
    HasDerivAt (fun x : ℝ => Real.sin (x / 2))
      (Real.cos (t / 2) / 2) t := by
  convert ((Real.hasDerivAt_sin (t / 2)).comp t
    ((hasDerivAt_id t).div_const 2)) using 1 <;>
    simp [Function.comp_def] <;> ring

private theorem cycloid_hasDerivAt_cos_half (t : ℝ) :
    HasDerivAt (fun x : ℝ => Real.cos (x / 2))
      (-Real.sin (t / 2) / 2) t := by
  convert ((Real.hasDerivAt_cos (t / 2)).comp t
    ((hasDerivAt_id t).div_const 2)) using 1 <;>
    simp [Function.comp_def] <;> ring

private theorem cycloid_hasDerivAt_sin_three_half (t : ℝ) :
    HasDerivAt (fun x : ℝ => Real.sin (3 * x / 2))
      ((3 / 2 : ℝ) * Real.cos (3 * t / 2)) t := by
  convert ((Real.hasDerivAt_sin (3 * t / 2)).comp t
    (((hasDerivAt_id t).const_mul 3).div_const 2)) using 1 <;>
    simp [Function.comp_def] <;> ring

private theorem cycloid_hasDerivAt_cos_three_half (t : ℝ) :
    HasDerivAt (fun x : ℝ => Real.cos (3 * x / 2))
      (-(3 / 2 : ℝ) * Real.sin (3 * t / 2)) t := by
  convert ((Real.hasDerivAt_cos (3 * t / 2)).comp t
    (((hasDerivAt_id t).const_mul 3).div_const 2)) using 1 <;>
    simp [Function.comp_def] <;> ring

private theorem cycloid_sin_three_pi_half :
    Real.sin (3 * Real.pi / 2) = -1 := by
  rw [show 3 * Real.pi / 2 = Real.pi + Real.pi / 2 by ring,
    Real.sin_add]
  simp

private theorem cycloid_cos_three_pi_half :
    Real.cos (3 * Real.pi / 2) = 0 := by
  rw [show 3 * Real.pi / 2 = Real.pi + Real.pi / 2 by ring,
    Real.cos_add]
  simp

private theorem cycloid_integral_sin_half :
    (∫ t in (0 : ℝ)..Real.pi, Real.sin (t / 2)) = 2 := by
  have h := cycloid_integral_from_derivative
    (fun t : ℝ => -2 * Real.cos (t / 2))
    (fun t : ℝ => Real.sin (t / 2)) 0 Real.pi
    (by
      intro t
      convert (cycloid_hasDerivAt_cos_half t).const_mul (-2) using 1 <;>
        simp [Function.comp_def] <;> ring)
    (by continuity)
  simpa using h

private theorem cycloid_integral_cos_half :
    (∫ t in (0 : ℝ)..Real.pi, Real.cos (t / 2)) = 2 := by
  have h := cycloid_integral_from_derivative
    (fun t : ℝ => 2 * Real.sin (t / 2))
    (fun t : ℝ => Real.cos (t / 2)) 0 Real.pi
    (by
      intro t
      convert (cycloid_hasDerivAt_sin_half t).const_mul 2 using 1 <;>
        simp [Function.comp_def] <;> ring)
    (by continuity)
  simpa using h

private theorem cycloid_integral_t_sin_half :
    (∫ t in (0 : ℝ)..Real.pi, t * Real.sin (t / 2)) = 4 := by
  have h := cycloid_integral_from_derivative
    (fun t : ℝ => -2 * t * Real.cos (t / 2) + 4 * Real.sin (t / 2))
    (fun t : ℝ => t * Real.sin (t / 2)) 0 Real.pi
    (by
      intro t
      have hc := cycloid_hasDerivAt_cos_half t
      have hs := cycloid_hasDerivAt_sin_half t
      convert (((hasDerivAt_id t).mul hc).const_mul (-2)).add
        (hs.const_mul 4) using 1 <;>
        simp [Function.comp_def] <;> try ring
      funext x
      dsimp <;> ring)
    (by continuity)
  simpa using h

private theorem cycloid_integral_sin_mul_sin_half :
    (∫ t in (0 : ℝ)..Real.pi,
      Real.sin t * Real.sin (t / 2)) = 4 / 3 := by
  have h := cycloid_integral_from_derivative
    (fun t : ℝ => (4 / 3 : ℝ) * Real.sin (t / 2) ^ 3)
    (fun t : ℝ => Real.sin t * Real.sin (t / 2)) 0 Real.pi
    (by
      intro t
      have hs := cycloid_hasDerivAt_sin_half t
      convert (hs.pow 3).const_mul (4 / 3 : ℝ) using 1 <;>
        simp [Function.comp_def] <;> try ring
      rw [cycloid_sin_double_half]
      ring)
    (by continuity)
  norm_num at h ⊢
  simpa using h

private theorem cycloid_integral_x_base :
    (∫ t in (0 : ℝ)..Real.pi,
      (t - Real.sin t) * Real.sin (t / 2)) = 8 / 3 := by
  have h := cycloid_integral_from_derivative
    (fun t : ℝ =>
      -2 * t * Real.cos (t / 2) + 4 * Real.sin (t / 2) -
        (4 / 3 : ℝ) * Real.sin (t / 2) ^ 3)
    (fun t : ℝ => (t - Real.sin t) * Real.sin (t / 2)) 0 Real.pi
    (by
      intro t
      have hc := cycloid_hasDerivAt_cos_half t
      have hs := cycloid_hasDerivAt_sin_half t
      have hfirst := (((hasDerivAt_id t).mul hc).const_mul (-2)).add
        (hs.const_mul 4)
      have hsecond := (hs.pow 3).const_mul (4 / 3 : ℝ)
      convert hfirst.sub hsecond using 1 <;>
        simp [Function.comp_def] <;> try ring
      · funext x
        dsimp <;> ring
      · rw [cycloid_sin_double_half t]
        ring)
    (by continuity)
  norm_num at h ⊢
  simpa using h

private theorem cycloid_integral_y_base :
    (∫ t in (0 : ℝ)..Real.pi,
      (1 - Real.cos t) * Real.sin (t / 2)) = 8 / 3 := by
  have h := cycloid_integral_from_derivative
    (fun t : ℝ =>
      -4 * Real.cos (t / 2) + (4 / 3 : ℝ) * Real.cos (t / 2) ^ 3)
    (fun t : ℝ => (1 - Real.cos t) * Real.sin (t / 2)) 0 Real.pi
    (by
      intro t
      have hc := cycloid_hasDerivAt_cos_half t
      have hderiv := (hc.const_mul (-4)).add
        ((hc.pow 3).const_mul (4 / 3 : ℝ))
      convert hderiv using 1 <;>
        simp [Function.comp_def] <;> try ring
      rw [cycloid_cos_double_half]
      ring)
    (by continuity)
  norm_num at h ⊢
  simpa using h

private theorem cycloid_integral_cos_diff :
    (∫ t in (0 : ℝ)..Real.pi,
      Real.cos (3 * t / 2) - Real.cos (t / 2)) = -8 / 3 := by
  have h := cycloid_integral_from_derivative
    (fun t : ℝ =>
      (2 / 3 : ℝ) * Real.sin (3 * t / 2) - 2 * Real.sin (t / 2))
    (fun t : ℝ => Real.cos (3 * t / 2) - Real.cos (t / 2)) 0 Real.pi
    (by
      intro t
      have h3 := cycloid_hasDerivAt_sin_three_half t
      have h1 := cycloid_hasDerivAt_sin_half t
      convert (h3.const_mul (2 / 3 : ℝ)).sub (h1.const_mul 2) using 1 <;>
        simp [Function.comp_def] <;> ring)
    (by continuity)
  norm_num [cycloid_sin_three_pi_half] at h ⊢
  simpa using h

private theorem cycloid_integral_sin_diff :
    (∫ t in (0 : ℝ)..Real.pi,
      Real.sin (3 * t / 2) - Real.sin (t / 2)) = -4 / 3 := by
  have h := cycloid_integral_from_derivative
    (fun t : ℝ =>
      -(2 / 3 : ℝ) * Real.cos (3 * t / 2) + 2 * Real.cos (t / 2))
    (fun t : ℝ => Real.sin (3 * t / 2) - Real.sin (t / 2)) 0 Real.pi
    (by
      intro t
      have h3 := cycloid_hasDerivAt_cos_three_half t
      have h1 := cycloid_hasDerivAt_cos_half t
      convert (h3.const_mul (-(2 / 3 : ℝ))).add (h1.const_mul 2) using 1 <;>
        simp [Function.comp_def] <;> ring)
    (by continuity)
  norm_num [cycloid_cos_three_pi_half] at h ⊢
  simpa using h

private theorem cycloid_rawSpeed_eq (a t : ℝ) (ha : 0 < a)
    (ht : t ∈ Set.Icc (0 : ℝ) Real.pi) :
    rawSpeed a t = 2 * a * Real.sin (t / 2) := by
  have hs : 0 ≤ Real.sin (t / 2) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · nlinarith [ht.1]
    · nlinarith [ht.2, Real.pi_pos]
  have hsquare : 1 - Real.cos (t / 2) ^ 2 = Real.sin (t / 2) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (t / 2)]
  have hrad :
      a ^ 2 * (1 - Real.cos t) ^ 2 + a ^ 2 * Real.sin t ^ 2 =
        (2 * a * Real.sin (t / 2)) ^ 2 := by
    rw [cycloid_cos_double_half, cycloid_sin_double_half]
    rw [show 1 - (2 * Real.cos (t / 2) ^ 2 - 1) =
      2 * (1 - Real.cos (t / 2) ^ 2) by ring, hsquare]
    calc
      _ = 4 * a ^ 2 * Real.sin (t / 2) ^ 2 *
          (Real.sin (t / 2) ^ 2 + Real.cos (t / 2) ^ 2) := by
        ring
      _ = (2 * a * Real.sin (t / 2)) ^ 2 := by
        rw [Real.sin_sq_add_cos_sq (t / 2)]
        ring
  rw [rawSpeed, hrad, Real.sqrt_sq_eq_abs, abs_of_nonneg]
  exact mul_nonneg (mul_nonneg (by norm_num) (le_of_lt ha)) hs

private theorem cycloid_raw_integral_congr (a : ℝ) (ha : 0 < a)
    (g : ℝ → ℝ) :
    (∫ t in (0 : ℝ)..Real.pi, g t * rawSpeed a t) =
      ∫ t in (0 : ℝ)..Real.pi,
        g t * (2 * a * Real.sin (t / 2)) := by
  apply intervalIntegral.integral_congr
  intro t ht
  have htt : t ∈ Set.Icc (0 : ℝ) Real.pi := by
    simpa [Set.uIcc_of_le (le_of_lt Real.pi_pos)] using ht
  change g t * rawSpeed a t = g t * (2 * a * Real.sin (t / 2))
  rw [cycloid_rawSpeed_eq a t ha htt]

private theorem cycloid_x_speed_integral (a r : ℝ) :
    (∫ t in (0 : ℝ)..Real.pi,
      r * a * (t - Real.sin t) * 2 * a * Real.sin (t / 2)) =
        16 * r * a ^ 2 / 3 := by
  calc
    (∫ t in (0 : ℝ)..Real.pi,
      r * a * (t - Real.sin t) * 2 * a * Real.sin (t / 2)) =
        ∫ t in (0 : ℝ)..Real.pi,
          (2 * r * a ^ 2) * ((t - Real.sin t) * Real.sin (t / 2)) := by
            apply intervalIntegral.integral_congr
            intro t ht
            ring
    _ = (2 * r * a ^ 2) *
        (∫ t in (0 : ℝ)..Real.pi,
          (t - Real.sin t) * Real.sin (t / 2)) := by
            rw [intervalIntegral.integral_const_mul]
    _ = 16 * r * a ^ 2 / 3 := by
      rw [cycloid_integral_x_base]
      ring

private theorem cycloid_y_speed_integral (a r : ℝ) :
    (∫ t in (0 : ℝ)..Real.pi,
      r * a * (1 - Real.cos t) * 2 * a * Real.sin (t / 2)) =
        16 * r * a ^ 2 / 3 := by
  calc
    (∫ t in (0 : ℝ)..Real.pi,
      r * a * (1 - Real.cos t) * 2 * a * Real.sin (t / 2)) =
        ∫ t in (0 : ℝ)..Real.pi,
          (2 * r * a ^ 2) * ((1 - Real.cos t) * Real.sin (t / 2)) := by
            apply intervalIntegral.integral_congr
            intro t ht
            ring
    _ = (2 * r * a ^ 2) *
        (∫ t in (0 : ℝ)..Real.pi,
          (1 - Real.cos t) * Real.sin (t / 2)) := by
            rw [intervalIntegral.integral_const_mul]
    _ = 16 * r * a ^ 2 / 3 := by
      rw [cycloid_integral_y_base]
      ring

private theorem cycloid_mass_value (a ρ₀ : ℝ) (ha : 0 < a) :
    mass a ρ₀ = 4 * a * ρ₀ := by
  have hraw := cycloid_raw_integral_congr a ha (fun _ : ℝ => 1)
  simp only [one_mul] at hraw
  unfold mass
  rw [hraw, intervalIntegral.integral_const_mul, cycloid_integral_sin_half]
  ring

private theorem cycloid_x_raw_integral (a r : ℝ) (ha : 0 < a) :
    (∫ t in (0 : ℝ)..Real.pi,
      r * a * (t - Real.sin t) * rawSpeed a t) =
        16 * r * a ^ 2 / 3 := by
  rw [cycloid_raw_integral_congr a ha
    (fun t : ℝ => r * a * (t - Real.sin t))]
  simpa only [mul_assoc] using cycloid_x_speed_integral a r

private theorem cycloid_y_raw_integral (a r : ℝ) (ha : 0 < a) :
    (∫ t in (0 : ℝ)..Real.pi,
      r * a * (1 - Real.cos t) * rawSpeed a t) =
        16 * r * a ^ 2 / 3 := by
  rw [cycloid_raw_integral_congr a ha
    (fun t : ℝ => r * a * (1 - Real.cos t))]
  simpa only [mul_assoc] using cycloid_y_speed_integral a r

private theorem cycloid_xCentroid_value (a ρ₀ : ℝ)
    (ha : 0 < a) (hρ : 0 < ρ₀) :
    xCentroid a ρ₀ = 4 * a / 3 := by
  unfold xCentroid
  simp only [curveMap]
  rw [cycloid_mass_value a ρ₀ ha]
  have hx := cycloid_x_raw_integral a 1 ha
  simp only [one_mul] at hx
  rw [hx]
  field_simp [ne_of_gt ha, ne_of_gt hρ]
  <;> ring

private theorem cycloid_yCentroid_value (a ρ₀ : ℝ)
    (ha : 0 < a) (hρ : 0 < ρ₀) :
    yCentroid a ρ₀ = 4 * a / 3 := by
  unfold yCentroid
  simp only [curveMap]
  rw [cycloid_mass_value a ρ₀ ha]
  have hy := cycloid_y_raw_integral a 1 ha
  simp only [one_mul] at hy
  rw [hy]
  field_simp [ne_of_gt ha, ne_of_gt hρ]
  <;> ring

theorem gap1 (a t : ℝ) :
    rawSpeed a t =
      Real.sqrt (a ^ 2 * (1 - Real.cos t) ^ 2 + a ^ 2 * Real.sin t ^ 2) := by
  rfl

theorem gap2 (a t : ℝ) (ha : 0 < a)
    (ht : t ∈ Set.Icc (0 : ℝ) Real.pi) :
    rawSpeed a t = speed a t := by
  exact cycloid_rawSpeed_eq a t ha ht

theorem gap3 (a t : ℝ) (ha : 0 < a)
    (ht : t ∈ Set.Icc (0 : ℝ) Real.pi) :
    rawSpeed a t = 2 * a * Real.sin (t / 2) := by
  simpa [speed] using gap2 a t ha ht

theorem gap4 (a ρ₀ : ℝ) (ha : 0 < a) (hρ : 0 < ρ₀) :
    mass a ρ₀ =
      2 * a * ρ₀ *
        ∫ t in (0 : ℝ)..Real.pi, Real.sin (t / 2) := by
  rw [cycloid_mass_value a ρ₀ ha, cycloid_integral_sin_half]
  ring

theorem gap5 (a ρ₀ : ℝ) :
    2 * a * ρ₀ *
        (∫ t in (0 : ℝ)..Real.pi, Real.sin (t / 2)) =
      4 * a * ρ₀ := by
  rw [cycloid_integral_sin_half]
  ring

theorem gap6 (a ρ₀ : ℝ) (ha : 0 < a) (hρ : 0 < ρ₀) :
    mass a ρ₀ = 4 * a * ρ₀ := by
  exact cycloid_mass_value a ρ₀ ha

theorem gap7 (a ρ₀ : ℝ) (ha : 0 < a) (hρ : 0 < ρ₀) :
    xCentroid a ρ₀ =
      1 / mass a ρ₀ *
        ∫ t in (0 : ℝ)..Real.pi,
          ρ₀ * a * (t - Real.sin t) * 2 * a * Real.sin (t / 2) := by
  rw [cycloid_xCentroid_value a ρ₀ ha hρ,
    cycloid_mass_value a ρ₀ ha, cycloid_x_speed_integral]
  field_simp [ne_of_gt ha, ne_of_gt hρ]
  <;> ring

theorem gap8 (a ρ₀ : ℝ) (ha : 0 < a) (hρ : 0 < ρ₀) :
    xCentroid a ρ₀ =
      a / 2 *
          (∫ t in (0 : ℝ)..Real.pi, t * Real.sin (t / 2)) -
        a / 2 *
          ∫ t in (0 : ℝ)..Real.pi, Real.sin t * Real.sin (t / 2) := by
  rw [cycloid_xCentroid_value a ρ₀ ha hρ,
    cycloid_integral_t_sin_half, cycloid_integral_sin_mul_sin_half]
  ring

theorem gap9 (a ρ₀ : ℝ) (ha : 0 < a) (hρ : 0 < ρ₀) :
    xCentroid a ρ₀ =
      xBoundaryTerm a Real.pi - xBoundaryTerm a 0 +
        a * (∫ t in (0 : ℝ)..Real.pi, Real.cos (t / 2)) +
        a / 4 *
          ∫ t in (0 : ℝ)..Real.pi,
            Real.cos (3 * t / 2) - Real.cos (t / 2) := by
  rw [cycloid_xCentroid_value a ρ₀ ha hρ,
    cycloid_integral_cos_half, cycloid_integral_cos_diff]
  simp [xBoundaryTerm]
  ring

theorem gap10 (a : ℝ) :
    xBoundaryTerm a Real.pi - xBoundaryTerm a 0 +
          a * (∫ t in (0 : ℝ)..Real.pi, Real.cos (t / 2)) +
          a / 4 *
            (∫ t in (0 : ℝ)..Real.pi,
              Real.cos (3 * t / 2) - Real.cos (t / 2)) =
      4 * a / 3 := by
  rw [cycloid_integral_cos_half, cycloid_integral_cos_diff]
  simp [xBoundaryTerm]
  ring

theorem gap11 (a ρ₀ : ℝ) (ha : 0 < a) (hρ : 0 < ρ₀) :
    xCentroid a ρ₀ = 4 * a / 3 := by
  exact cycloid_xCentroid_value a ρ₀ ha hρ

theorem gap12 (a ρ₀ : ℝ) (ha : 0 < a) (hρ : 0 < ρ₀) :
    yCentroid a ρ₀ =
      1 / mass a ρ₀ *
        ∫ t in (0 : ℝ)..Real.pi,
          ρ₀ * a * (1 - Real.cos t) * 2 * a * Real.sin (t / 2) := by
  rw [cycloid_yCentroid_value a ρ₀ ha hρ,
    cycloid_mass_value a ρ₀ ha, cycloid_y_speed_integral]
  field_simp [ne_of_gt ha, ne_of_gt hρ]
  <;> ring

theorem gap13 (a ρ₀ : ℝ) (ha : 0 < a) (hρ : 0 < ρ₀) :
    yCentroid a ρ₀ =
      a / 2 * (∫ t in (0 : ℝ)..Real.pi, Real.sin (t / 2)) -
        a / 4 *
          ∫ t in (0 : ℝ)..Real.pi,
            Real.sin (3 * t / 2) - Real.sin (t / 2) := by
  rw [cycloid_yCentroid_value a ρ₀ ha hρ,
    cycloid_integral_sin_half, cycloid_integral_sin_diff]
  ring

theorem gap14 (a : ℝ) :
    a / 2 * (∫ t in (0 : ℝ)..Real.pi, Real.sin (t / 2)) -
          a / 4 *
            (∫ t in (0 : ℝ)..Real.pi,
              Real.sin (3 * t / 2) - Real.sin (t / 2)) =
      4 * a / 3 := by
  rw [cycloid_integral_sin_half, cycloid_integral_sin_diff]
  ring

theorem gap15 (a ρ₀ : ℝ) (ha : 0 < a) (hρ : 0 < ρ₀) :
    yCentroid a ρ₀ = 4 * a / 3 := by
  exact cycloid_yCentroid_value a ρ₀ ha hρ

end

end ProofGap.Exercise4244

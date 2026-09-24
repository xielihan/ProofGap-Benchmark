import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open scoped Interval

namespace ProofGap.Exercise2495_1

noncomputable section

def cycloidX (a t : ℝ) : ℝ := a * (t - Real.sin t)

def cycloidY (a t : ℝ) : ℝ := a * (1 - Real.cos t)

def speed (a t : ℝ) : ℝ :=
  Real.sqrt (deriv (cycloidX a) t ^ 2 + deriv (cycloidY a) t ^ 2)

def surfaceArea (a : ℝ) : ℝ :=
  2 * Real.pi * ∫ t in 0..(2 * Real.pi),
    cycloidY a t * speed a t

private theorem one_sub_cos_eq_two_sin_sq (x : ℝ) :
    1 - Real.cos x = 2 * Real.sin (x / 2) ^ 2 := by
  have h := Real.cos_two_mul (x / 2)
  have hx : 2 * (x / 2) = x := by ring
  rw [hx] at h
  nlinarith [h, Real.sin_sq_add_cos_sq (x / 2)]

private theorem hasDerivAt_sin_cube_primitive (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => -Real.cos y + Real.cos y ^ 3 / 3)
      (Real.sin x ^ 3) x := by
  convert (Real.hasDerivAt_cos x).neg.add
      (((Real.hasDerivAt_cos x).pow 3).div_const 3) using 1
  norm_num
  have hsq : Real.sin x ^ 2 = 1 - Real.cos x ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  rw [show Real.sin x ^ 3 = Real.sin x * Real.sin x ^ 2 by ring, hsq]
  ring

private theorem integral_sin_cube :
    (∫ u in 0..Real.pi, Real.sin u ^ 3) = (4 / 3 : ℝ) := by
  calc
    (∫ u in 0..Real.pi, Real.sin u ^ 3) =
        (-Real.cos Real.pi + Real.cos Real.pi ^ 3 / 3) -
          (-Real.cos 0 + Real.cos 0 ^ 3 / 3) := by
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => hasDerivAt_sin_cube_primitive x)
        ((Real.continuous_sin.pow 3).intervalIntegrable 0 Real.pi)
    _ = (4 / 3 : ℝ) := by
      rw [Real.cos_pi, Real.cos_zero]
      norm_num

private theorem cycloid_integral_value (a : ℝ) :
    (∫ t in 0..(2 * Real.pi),
      a * (1 - Real.cos t) * (2 * a * Real.sin (t / 2))) =
        32 / 3 * a ^ 2 := by
  have hderiv : ∀ x : ℝ,
      HasDerivAt
        (fun y : ℝ => 8 * a ^ 2 *
          (-Real.cos (y / 2) + Real.cos (y / 2) ^ 3 / 3))
        (4 * a ^ 2 * Real.sin (x / 2) ^ 3) x := by
    intro x
    have hinner :=
      (hasDerivAt_sin_cube_primitive (x / 2)).comp x
        ((hasDerivAt_id x).div_const 2)
    convert hinner.const_mul (8 * a ^ 2) using 1 <;> ring
  have hcont : Continuous
      (fun x : ℝ => 4 * a ^ 2 * Real.sin (x / 2) ^ 3) := by
    exact continuous_const.mul
      ((Real.continuous_sin.comp (continuous_id.div_const 2)).pow 3)
  calc
    (∫ t in 0..(2 * Real.pi),
        a * (1 - Real.cos t) * (2 * a * Real.sin (t / 2))) =
        ∫ t in 0..(2 * Real.pi),
          4 * a ^ 2 * Real.sin (t / 2) ^ 3 := by
      apply intervalIntegral.integral_congr
      intro t ht
      change a * (1 - Real.cos t) * (2 * a * Real.sin (t / 2)) =
        4 * a ^ 2 * Real.sin (t / 2) ^ 3
      rw [one_sub_cos_eq_two_sin_sq]
      ring
    _ = (8 * a ^ 2 *
          (-Real.cos ((2 * Real.pi) / 2) +
            Real.cos ((2 * Real.pi) / 2) ^ 3 / 3)) -
        (8 * a ^ 2 *
          (-Real.cos (0 / 2) + Real.cos (0 / 2) ^ 3 / 3)) := by
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => hderiv x)
        (hcont.intervalIntegrable 0 (2 * Real.pi))
    _ = 32 / 3 * a ^ 2 := by
      have hpi : (2 * Real.pi) / 2 = Real.pi := by ring
      rw [hpi, Real.cos_pi]
      norm_num [Real.cos_zero] <;> ring

theorem gap1 (a t : ℝ) :
    speed a t =
      Real.sqrt (deriv (cycloidX a) t ^ 2 + deriv (cycloidY a) t ^ 2) := by
  rfl

theorem gap2 (a t : ℝ) (ha : 0 ≤ a)
    (ht : t ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
    speed a t = 2 * a * Real.sin (t / 2) := by
  have hdx : HasDerivAt (cycloidX a) (a * (1 - Real.cos t)) t := by
    unfold cycloidX
    convert ((hasDerivAt_id t).sub (Real.hasDerivAt_sin t)).const_mul a using 1 <;> ring
  have hdy : HasDerivAt (cycloidY a) (a * Real.sin t) t := by
    unfold cycloidY
    convert ((hasDerivAt_const (x := t) (c := (1 : ℝ))).sub
      (Real.hasDerivAt_cos t)).const_mul a using 1 <;> ring
  have ht0 : 0 ≤ t / 2 := by
    linarith [ht.1]
  have htpi : t / 2 ≤ Real.pi := by
    linarith [ht.2]
  have hs : 0 ≤ Real.sin (t / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi ht0 htpi
  have hz : 0 ≤ 2 * a * Real.sin (t / 2) := by
    exact mul_nonneg (mul_nonneg (by norm_num) ha) hs
  have hcircle :
      (1 - Real.cos t) ^ 2 + Real.sin t ^ 2 =
        2 * (1 - Real.cos t) := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  have hrad :
      (a * (1 - Real.cos t)) ^ 2 + (a * Real.sin t) ^ 2 =
        (2 * a * Real.sin (t / 2)) ^ 2 := by
    calc
      (a * (1 - Real.cos t)) ^ 2 + (a * Real.sin t) ^ 2 =
          a ^ 2 * ((1 - Real.cos t) ^ 2 + Real.sin t ^ 2) := by ring
      _ = a ^ 2 * (2 * (1 - Real.cos t)) := by rw [hcircle]
      _ = (2 * a * Real.sin (t / 2)) ^ 2 := by
        rw [one_sub_cos_eq_two_sin_sq]
        ring
  unfold speed
  rw [hdx.deriv, hdy.deriv, hrad, Real.sqrt_sq hz]

theorem gap3 (a : ℝ) (ha : 0 ≤ a) :
    ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      speed a t = 2 * a * Real.sin (t / 2) := by
  intro t ht
  exact gap2 a t ha ht

theorem gap4 (a Pₓ : ℝ) (ha : 0 ≤ a) (hP : Pₓ = surfaceArea a) :
    Pₓ = 2 * Real.pi * ∫ t in 0..(2 * Real.pi),
      a * (1 - Real.cos t) * (2 * a * Real.sin (t / 2)) := by
  calc
    Pₓ = surfaceArea a := hP
    _ = 2 * Real.pi * ∫ t in 0..(2 * Real.pi),
          a * (1 - Real.cos t) * (2 * a * Real.sin (t / 2)) := by
      unfold surfaceArea
      refine congrArg (fun z : ℝ => 2 * Real.pi * z) ?_
      apply intervalIntegral.integral_congr
      intro t ht
      have horder : (0 : ℝ) ≤ 2 * Real.pi := by
        nlinarith [Real.pi_pos]
      have ht' : t ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
        simpa [Set.uIcc_of_le horder] using ht
      change cycloidY a t * speed a t =
        a * (1 - Real.cos t) * (2 * a * Real.sin (t / 2))
      rw [gap2 a t ha ht']
      rfl

theorem gap5 (a : ℝ) :
    2 * Real.pi * (∫ t in 0..(2 * Real.pi),
      a * (1 - Real.cos t) * (2 * a * Real.sin (t / 2))) =
        16 * Real.pi * a ^ 2 *
          ∫ u in 0..Real.pi, Real.sin u ^ 3 := by
  rw [cycloid_integral_value, integral_sin_cube]
  ring

theorem gap6 (a : ℝ) :
    16 * Real.pi * a ^ 2 *
        (∫ u in 0..Real.pi, Real.sin u ^ 3) =
      64 / 3 * Real.pi * a ^ 2 := by
  rw [integral_sin_cube]
  ring

theorem gap7 (a Pₓ : ℝ) (ha : 0 ≤ a) (hP : Pₓ = surfaceArea a) :
    Pₓ = 64 / 3 * Real.pi * a ^ 2 := by
  calc
    Pₓ = 2 * Real.pi * ∫ t in 0..(2 * Real.pi),
        a * (1 - Real.cos t) * (2 * a * Real.sin (t / 2)) :=
      gap4 a Pₓ ha hP
    _ = 16 * Real.pi * a ^ 2 *
        ∫ u in 0..Real.pi, Real.sin u ^ 3 := gap5 a
    _ = 64 / 3 * Real.pi * a ^ 2 := gap6 a

end

end ProofGap.Exercise2495_1

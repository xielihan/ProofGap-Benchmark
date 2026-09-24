import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3803

noncomputable section

open MeasureTheory

def gaussian (x : ℝ) : ℝ :=
  Real.exp (-(x ^ 2))

def I : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ), gaussian x

private theorem scaleIntegralIoi (f : ℝ → ℝ) (u : ℝ) (hu : 0 < u) :
    u * (∫ x in Set.Ioi (0 : ℝ), f (u * x)) =
      ∫ x in Set.Ioi (0 : ℝ), f x := by
  rw [MeasureTheory.integral_comp_mul_left_Ioi f 0 hu]
  simp [hu.ne']

private theorem firstMomentGaussianIoi (a : ℝ) (ha : 0 < a) :
    (∫ u in Set.Ioi (0 : ℝ), Real.exp (-(a * u ^ 2)) * u) =
      1 / (2 * a) := by
  let s := Real.sqrt a
  have hs : 0 < s := Real.sqrt_pos.2 ha
  have hs2 : s ^ 2 = a := by
    simpa [s] using Real.sq_sqrt ha.le
  have hscale := scaleIntegralIoi
    (fun x : ℝ => Real.exp (-(x ^ 2)) * x) s hs
  have hinner :
      (∫ u in Set.Ioi (0 : ℝ),
        Real.exp (-((s * u) ^ 2)) * (s * u)) =
      s * ∫ u in Set.Ioi (0 : ℝ), Real.exp (-(a * u ^ 2)) * u := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with u
    have he : (s * u) ^ 2 = a * u ^ 2 := by
      rw [mul_pow, hs2]
    rw [he]
    ring
  rw [hinner] at hscale
  have hbase :
      (∫ x in Set.Ioi (0 : ℝ), Real.exp (-(x ^ 2)) * x) = 1 / 2 := by
    have hpow := MeasureTheory.integral_comp_rpow_Ioi
      (g := fun x : ℝ => Real.exp (-x)) (p := (2 : ℝ))
      (hp := by norm_num)
    rw [integral_exp_neg_Ioi] at hpow
    have htwice :
        2 * (∫ x in Set.Ioi (0 : ℝ), Real.exp (-(x ^ 2)) * x) = 1 := by
      rw [← MeasureTheory.integral_const_mul]
      simpa [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one,
        Real.rpow_two, mul_comm, mul_left_comm, mul_assoc] using hpow
    linarith
  have hscaled :
      s * (s * ∫ u in Set.Ioi (0 : ℝ),
        Real.exp (-(a * u ^ 2)) * u) = 1 / 2 := by
    calc
      s * (s * ∫ u in Set.Ioi (0 : ℝ),
        Real.exp (-(a * u ^ 2)) * u) =
          ∫ x in Set.Ioi (0 : ℝ), Real.exp (-(x ^ 2)) * x := hscale
      _ = 1 / 2 := hbase
  have hAJ :
      a * (∫ u in Set.Ioi (0 : ℝ),
        Real.exp (-(a * u ^ 2)) * u) = 1 / 2 := by
    calc
      a * (∫ u in Set.Ioi (0 : ℝ),
        Real.exp (-(a * u ^ 2)) * u) =
          s * (s * ∫ u in Set.Ioi (0 : ℝ),
            Real.exp (-(a * u ^ 2)) * u) := by
              rw [← hs2]
              ring
      _ = 1 / 2 := hscaled
  apply (eq_div_iff (mul_ne_zero (by norm_num) ha.ne')).2
  calc
    (∫ u in Set.Ioi (0 : ℝ), Real.exp (-(a * u ^ 2)) * u) * (2 * a) =
        2 * (a * ∫ u in Set.Ioi (0 : ℝ),
          Real.exp (-(a * u ^ 2)) * u) := by ring
    _ = 2 * (1 / 2) := by rw [hAJ]
    _ = 1 := by norm_num

private theorem cauchyIntegralIoi :
    (∫ t in Set.Ioi (0 : ℝ), 1 / (1 + t ^ 2)) = Real.pi / 2 := by
  simpa [one_div] using integral_inv_one_add_sq_Ioi

theorem gap1 (u : ℝ) (hu : 0 < u) :
    I = u * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(u ^ 2 * t ^ 2)) := by
  unfold I gaussian
  calc
    (∫ x in Set.Ioi (0 : ℝ), Real.exp (-(x ^ 2))) =
        u * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-((u * t) ^ 2)) :=
      (scaleIntegralIoi (fun x : ℝ => Real.exp (-(x ^ 2))) u hu).symm
    _ = u * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(u ^ 2 * t ^ 2)) := by
      congr 1
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with t
      congr 2
      ring

theorem gap2 (u : ℝ) (hu : 0 < u) :
    I ^ 2 =
      (∫ v in Set.Ioi (0 : ℝ), gaussian v) *
        (u * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(u ^ 2 * t ^ 2))) := by
  rw [← gap1 u hu]
  simp [I, pow_two]

theorem gap3 (t : ℝ) :
    (∫ u in Set.Ioi (0 : ℝ),
      Real.exp (-((1 + t ^ 2) * u ^ 2)) * u) =
        1 / (2 * (1 + t ^ 2)) := by
  have ha : 0 < 1 + t ^ 2 := by
    nlinarith [sq_nonneg t]
  simpa using firstMomentGaussianIoi (1 + t ^ 2) ha

theorem gap4 (u : ℝ) (hu : 0 < u) :
    (∫ t in Set.Ioi (0 : ℝ),
      Real.exp (-((1 + t ^ 2) * u ^ 2)) * u) =
        Real.exp (-(u ^ 2)) * I := by
  rw [gap1 u hu]
  calc
    (∫ t in Set.Ioi (0 : ℝ),
        Real.exp (-((1 + t ^ 2) * u ^ 2)) * u) =
        ∫ t in Set.Ioi (0 : ℝ),
          (Real.exp (-(u ^ 2)) * u) * Real.exp (-(u ^ 2 * t ^ 2)) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with t
      have he : -((1 + t ^ 2) * u ^ 2) =
          -(u ^ 2) + -(u ^ 2 * t ^ 2) := by ring
      rw [he, Real.exp_add]
      ring
    _ = (Real.exp (-(u ^ 2)) * u) *
        ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(u ^ 2 * t ^ 2)) := by
      rw [MeasureTheory.integral_const_mul]
    _ = Real.exp (-(u ^ 2)) *
        (u * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(u ^ 2 * t ^ 2))) := by
      ring

theorem gap5 :
    I ^ 2 =
      ∫ t in Set.Ioi (0 : ℝ),
        (∫ u in Set.Ioi (0 : ℝ),
          Real.exp (-((1 + t ^ 2) * u ^ 2)) * u) := by
  have hI : I = Real.sqrt Real.pi / 2 := by
    simpa [I, gaussian] using (integral_gaussian_Ioi (1 : ℝ))
  rw [hI]
  calc
    (Real.sqrt Real.pi / 2) ^ 2 = Real.pi / 4 := by
      rw [div_pow, Real.sq_sqrt (le_of_lt Real.pi_pos)]
      norm_num
    _ = 1 / 2 * (Real.pi / 2) := by ring
    _ = 1 / 2 * (∫ t in Set.Ioi (0 : ℝ), 1 / (1 + t ^ 2)) := by
      rw [cauchyIntegralIoi]
    _ = ∫ t in Set.Ioi (0 : ℝ), 1 / (2 * (1 + t ^ 2)) := by
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with t
      have ht : 0 < 1 + t ^ 2 := by nlinarith [sq_nonneg t]
      field_simp
    _ = ∫ t in Set.Ioi (0 : ℝ),
        (∫ u in Set.Ioi (0 : ℝ),
          Real.exp (-((1 + t ^ 2) * u ^ 2)) * u) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with t
      exact (gap3 t).symm

theorem gap6 :
    I ^ 2 =
      1 / 2 * ∫ t in Set.Ioi (0 : ℝ), 1 / (1 + t ^ 2) := by
  rw [gap5]
  calc
    (∫ t in Set.Ioi (0 : ℝ),
      (∫ u in Set.Ioi (0 : ℝ),
        Real.exp (-((1 + t ^ 2) * u ^ 2)) * u)) =
        ∫ t in Set.Ioi (0 : ℝ), 1 / (2 * (1 + t ^ 2)) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with t
      exact gap3 t
    _ = 1 / 2 * ∫ t in Set.Ioi (0 : ℝ), 1 / (1 + t ^ 2) := by
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with t
      have ht : 0 < 1 + t ^ 2 := by nlinarith [sq_nonneg t]
      field_simp

theorem gap7 :
    1 / 2 * (∫ t in Set.Ioi (0 : ℝ), 1 / (1 + t ^ 2)) =
      Real.pi / 4 := by
  rw [cauchyIntegralIoi]
  ring

theorem gap8 :
    I ^ 2 = Real.pi / 4 := by
  calc
    I ^ 2 = 1 / 2 * ∫ t in Set.Ioi (0 : ℝ), 1 / (1 + t ^ 2) := gap6
    _ = Real.pi / 4 := gap7

theorem gap9 :
    I = Real.sqrt Real.pi / 2 := by
  have hI : 0 ≤ I := by
    unfold I gaussian
    exact MeasureTheory.integral_nonneg (fun x => Real.exp_nonneg _)
  have hsqrt : 0 ≤ Real.sqrt Real.pi / 2 := by positivity
  have hsquare : (Real.sqrt Real.pi / 2) ^ 2 = Real.pi / 4 := by
    rw [div_pow, Real.sq_sqrt (le_of_lt Real.pi_pos)]
    norm_num
  nlinarith [gap8]

theorem gap10 :
    (∫ x in Set.Ioi (0 : ℝ), Real.exp (-(x ^ 2))) =
      Real.sqrt Real.pi / 2 := by
  simpa [I, gaussian] using gap9

end

end ProofGap.Exercise3803

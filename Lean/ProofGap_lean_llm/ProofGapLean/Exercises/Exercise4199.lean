import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4199

noncomputable section

open MeasureTheory
open scoped Interval

def gaussian (z : ℝ × ℝ × ℝ) : ℝ :=
  Real.exp (-(z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2))

def cartesianIntegral : ℝ :=
  ∫ z : ℝ × ℝ × ℝ, gaussian z

def radialIntegral : ℝ :=
  ∫ r in Set.Ici (0 : ℝ), r ^ 2 * Real.exp (-(r ^ 2))

def sphericalIntegral : ℝ :=
  ∫ azimuth in (0 : ℝ)..2 * Real.pi,
    ∫ latitude in (-Real.pi / 2)..Real.pi / 2,
      (∫ r in Set.Ici (0 : ℝ), r ^ 2 * Real.exp (-(r ^ 2))) *
        Real.cos latitude

def gammaIntegral : ℝ :=
  ∫ t in Set.Ici (0 : ℝ),
    Real.rpow t (1 / 2 : ℝ) * Real.exp (-t)

private def gaussian1D (x : ℝ) : ℝ :=
  Real.exp (-(1 : ℝ) * x ^ 2)

private theorem gaussian_eq_product (q : ℝ × ℝ × ℝ) :
    gaussian q =
      gaussian1D q.1 *
        (gaussian1D q.2.1 * gaussian1D q.2.2) := by
  unfold gaussian gaussian1D
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

private theorem gaussian1D_integrable :
    Integrable gaussian1D volume := by
  exact
    integrable_exp_neg_mul_sq
      (b := 1)
      (show (0 : ℝ) < 1 by norm_num)

private theorem cartesian_value :
    cartesianIntegral = Real.pi * Real.sqrt Real.pi := by
  have hgaussian :
      (∫ x : ℝ, gaussian1D x) =
        Real.sqrt Real.pi := by
    simpa only [gaussian1D, one_mul, div_one] using
      integral_gaussian (1 : ℝ)
  unfold cartesianIntegral
  rw [Measure.volume_eq_prod, Measure.volume_eq_prod]
  calc
    (∫ q : ℝ × ℝ × ℝ, gaussian q
        ∂((volume : Measure ℝ).prod
          ((volume : Measure ℝ).prod volume))) =
        ∫ q : ℝ × ℝ × ℝ,
          gaussian1D q.1 *
            (gaussian1D q.2.1 * gaussian1D q.2.2)
          ∂((volume : Measure ℝ).prod
            ((volume : Measure ℝ).prod volume)) := by
              apply integral_congr_ae
              exact ae_of_all _ fun q => gaussian_eq_product q
    _ = (∫ x : ℝ, gaussian1D x) *
          ((∫ y : ℝ, gaussian1D y) *
            ∫ z : ℝ, gaussian1D z) := by
              rw [integral_prod_mul gaussian1D
                (fun yz : ℝ × ℝ =>
                  gaussian1D yz.1 * gaussian1D yz.2)]
              rw [integral_prod_mul gaussian1D gaussian1D]
    _ = Real.sqrt Real.pi *
          (Real.sqrt Real.pi * Real.sqrt Real.pi) := by
              rw [hgaussian]
    _ = Real.pi * Real.sqrt Real.pi := by
              rw [← mul_assoc,
                Real.mul_self_sqrt Real.pi_nonneg]

private theorem radial_value_gamma :
    radialIntegral = (1 / 2 : ℝ) * Real.Gamma (3 / 2 : ℝ) := by
  unfold radialIntegral
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
  have heq : Set.EqOn
      (fun r : ℝ => r ^ 2 * Real.exp (-(r ^ 2)))
      (fun r : ℝ => Real.rpow r 2 * Real.exp (-(Real.rpow r 2)))
      (Set.Ioi 0) := by
    intro r hr
    have hpow : Real.rpow r 2 = r ^ (2 : ℕ) := by
      calc
        Real.rpow r 2 = r ^ (2 : ℝ) := by rfl
        _ = r ^ (2 : ℕ) := by
          convert Real.rpow_natCast r 2 using 1 <;> norm_num
    change r ^ (2 : ℕ) * Real.exp (-(r ^ (2 : ℕ))) =
      Real.rpow r 2 * Real.exp (-(Real.rpow r 2))
    rw [hpow]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi heq]
  have hformula := integral_rpow_mul_exp_neg_rpow
    (p := (2 : ℝ)) (q := (2 : ℝ)) (by norm_num) (by norm_num)
  change
    (∫ r in Set.Ioi (0 : ℝ),
      Real.rpow r 2 * Real.exp (-(Real.rpow r 2))) =
      (1 / 2 : ℝ) * Real.Gamma (3 / 2 : ℝ)
  convert hformula using 1 <;> norm_num

private theorem gammaIntegral_value :
    gammaIntegral = Real.Gamma (3 / 2 : ℝ) := by
  unfold gammaIntegral
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
  have heq : Set.EqOn
      (fun t : ℝ => Real.rpow t (1 / 2 : ℝ) * Real.exp (-t))
      (fun t : ℝ => Real.rpow t (1 / 2 : ℝ) *
        Real.exp (-(Real.rpow t 1)))
      (Set.Ioi 0) := by
    intro t ht
    change Real.rpow t (1 / 2 : ℝ) * Real.exp (-t) =
      Real.rpow t (1 / 2 : ℝ) * Real.exp (-(Real.rpow t 1))
    have ht1 : Real.rpow t 1 = t := by
      calc
        Real.rpow t 1 = t ^ (1 : ℝ) := by rfl
        _ = t := Real.rpow_one t
    rw [ht1]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi heq]
  have hformula := integral_rpow_mul_exp_neg_rpow
    (p := (1 : ℝ)) (q := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  change
    (∫ t in Set.Ioi (0 : ℝ),
      Real.rpow t (1 / 2 : ℝ) * Real.exp (-(Real.rpow t 1))) =
      Real.Gamma (3 / 2 : ℝ)
  convert hformula using 1 <;> norm_num

private theorem radial_value :
    radialIntegral = Real.sqrt Real.pi / 4 := by
  rw [radial_value_gamma]
  have hhalf := Real.Gamma_nat_add_half 0
  norm_num at hhalf
  have hrec := Real.Gamma_add_one (s := (1 / 2 : ℝ)) (by norm_num)
  norm_num at hrec
  rw [hrec, hhalf]
  ring

private theorem latitude_value :
    (∫ latitude in (-Real.pi / 2)..Real.pi / 2,
      radialIntegral * Real.cos latitude) =
      2 * radialIntegral := by
  rw [intervalIntegral.integral_const_mul, integral_cos]
  rw [Real.sin_pi_div_two,
    show -Real.pi / 2 = -(Real.pi / 2) by ring,
    Real.sin_neg, Real.sin_pi_div_two]
  ring

private theorem spherical_factor :
    sphericalIntegral = 4 * Real.pi * radialIntegral := by
  unfold sphericalIntegral
  change
    (∫ _azimuth in (0 : ℝ)..2 * Real.pi,
      ∫ latitude in (-Real.pi / 2)..Real.pi / 2,
        radialIntegral * Real.cos latitude) =
      4 * Real.pi * radialIntegral
  rw [show
      (fun _ : ℝ =>
        ∫ latitude in (-Real.pi / 2)..Real.pi / 2,
          radialIntegral * Real.cos latitude) =
        fun _ : ℝ => 2 * radialIntegral by
    funext azimuth
    exact latitude_value]
  rw [intervalIntegral.integral_const]
  simp
  ring

private theorem spherical_value :
    sphericalIntegral = Real.pi * Real.sqrt Real.pi := by
  rw [spherical_factor, radial_value]
  ring

private theorem pi_rpow_three_halves :
    Real.pi * Real.sqrt Real.pi =
      Real.rpow Real.pi (3 / 2 : ℝ) := by
  rw [Real.sqrt_eq_rpow]
  change Real.pi * Real.rpow Real.pi (1 / 2 : ℝ) =
    Real.rpow Real.pi (3 / 2 : ℝ)
  have hadd :
      Real.rpow Real.pi (1 + 1 / 2 : ℝ) =
        Real.rpow Real.pi 1 * Real.rpow Real.pi (1 / 2 : ℝ) := by
    convert Real.rpow_add Real.pi_pos (1 : ℝ) (1 / 2 : ℝ) using 1
  have hone : Real.rpow Real.pi 1 = Real.pi := Real.rpow_one Real.pi
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by ring, hadd, hone]

theorem gap1 :
    cartesianIntegral = sphericalIntegral := by
  rw [cartesian_value, spherical_value]

theorem gap2 :
    sphericalIntegral = 4 * Real.pi * radialIntegral := by
  exact spherical_factor

theorem gap3 :
    cartesianIntegral = 4 * Real.pi * radialIntegral := by
  rw [cartesian_value, radial_value]
  ring

theorem gap4 :
    radialIntegral = (1 / 2 : ℝ) * gammaIntegral := by
  rw [radial_value_gamma, gammaIntegral_value]

theorem gap5 :
    gammaIntegral = Real.Gamma (3 / 2 : ℝ) := by
  exact gammaIntegral_value

theorem gap6 :
    (1 / 2 : ℝ) * Real.Gamma (3 / 2 : ℝ) =
      (1 / 4 : ℝ) * Real.Gamma (1 / 2 : ℝ) := by
  have hrec := Real.Gamma_add_one (s := (1 / 2 : ℝ)) (by norm_num)
  norm_num at hrec
  rw [hrec]
  ring

theorem gap7 :
    (1 / 4 : ℝ) * Real.Gamma (1 / 2 : ℝ) =
      Real.sqrt Real.pi / 4 := by
  have hhalf := Real.Gamma_nat_add_half 0
  norm_num at hhalf
  rw [hhalf]
  ring

theorem gap8 :
    radialIntegral = Real.sqrt Real.pi / 4 := by
  exact radial_value

theorem gap9 :
    cartesianIntegral =
      4 * Real.pi * (Real.sqrt Real.pi / 4) := by
  rw [cartesian_value]
  ring

theorem gap10 :
    4 * Real.pi * (Real.sqrt Real.pi / 4) =
      Real.rpow Real.pi (3 / 2 : ℝ) := by
  rw [← pi_rpow_three_halves]
  ring

theorem gap11 :
    cartesianIntegral = Real.rpow Real.pi (3 / 2 : ℝ) := by
  rw [cartesian_value, pi_rpow_three_halves]

end

end ProofGap.Exercise4199

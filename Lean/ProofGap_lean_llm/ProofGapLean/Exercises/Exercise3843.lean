import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ProofGap.Exercise3843

noncomputable section

open MeasureTheory
open scoped Interval

def betaFn (x y : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    Real.rpow t (x - 1) * Real.rpow (1 - t) (y - 1)

theorem gap1 :
    (∫ x in (0 : ℝ)..1, Real.sqrt (x - x ^ 2)) =
      ∫ x in (0 : ℝ)..1,
        Real.rpow x (1 / 2 : ℝ) *
          Real.rpow (1 - x) (1 / 2 : ℝ) := by
  apply intervalIntegral.integral_congr
  intro x hx
  simp only [Set.uIcc_of_le zero_le_one, Set.mem_Icc] at hx
  change Real.sqrt (x - x ^ 2) =
    Real.rpow x (1 / 2 : ℝ) * Real.rpow (1 - x) (1 / 2 : ℝ)
  rw [show x - x ^ 2 = x * (1 - x) by ring]
  rw [Real.sqrt_mul hx.1]
  simp only [Real.sqrt_eq_rpow]
  rfl

theorem gap2 :
    (∫ x in (0 : ℝ)..1,
        Real.rpow x (1 / 2 : ℝ) *
          Real.rpow (1 - x) (1 / 2 : ℝ)) =
      betaFn (3 / 2) (3 / 2) := by
  norm_num [betaFn]

theorem gap3 :
    betaFn (3 / 2) (3 / 2) =
      Real.Gamma (3 / 2) ^ 2 / Real.Gamma 3 := by
  rw [← Complex.ofReal_inj]
  have hbeta :
      (betaFn (3 / 2) (3 / 2) : ℂ) =
        Complex.betaIntegral (3 / 2) (3 / 2) := by
    rw [betaFn, ← intervalIntegral.integral_ofReal, Complex.betaIntegral]
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [Set.uIcc_of_le zero_le_one, Set.mem_Icc] at hx
    dsimp only
    push_cast
    norm_num
    have hxpow :
        (((x ^ (1 / 2 : ℝ)) : ℝ) : ℂ) =
          (x : ℂ) ^ ((1 / 2 : ℝ) : ℂ) :=
      Complex.ofReal_cpow hx.1 (1 / 2 : ℝ)
    have honepow :
        ((((1 - x) ^ (1 / 2 : ℝ)) : ℝ) : ℂ) =
          ((1 - x : ℝ) : ℂ) ^ ((1 / 2 : ℝ) : ℂ) :=
      Complex.ofReal_cpow (sub_nonneg.mpr hx.2) (1 / 2 : ℝ)
    rw [hxpow, honepow]
    push_cast
    norm_num
  rw [hbeta]
  rw [Complex.betaIntegral_eq_Gamma_mul_div
    (3 / 2) (3 / 2) (by norm_num) (by norm_num)]
  push_cast
  have h32 : (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) := by norm_num
  have hsum :
      ((3 / 2 : ℝ) : ℂ) + ((3 / 2 : ℝ) : ℂ) = ((3 : ℝ) : ℂ) := by norm_num
  rw [h32, hsum]
  rw [Complex.Gamma_ofReal]
  rw [Complex.Gamma_ofReal (3 : ℝ)]
  ring

theorem gap4 :
    Real.Gamma (3 / 2) ^ 2 / Real.Gamma 3 =
      ((1 / 2 : ℝ) * Real.Gamma (1 / 2)) ^ 2 /
        (Nat.factorial 2 : ℝ) := by
  rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
    Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0)]
  rw [show (3 : ℝ) = (2 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]

theorem gap5 :
    (∫ x in (0 : ℝ)..1, Real.sqrt (x - x ^ 2)) =
      ((1 / 2 : ℝ) * Real.Gamma (1 / 2)) ^ 2 /
        (Nat.factorial 2 : ℝ) := by
  rw [gap1, gap2, gap3, gap4]

theorem gap6 :
    Real.Gamma (1 / 2) ^ 2 =
      Real.Gamma (1 / 2) * Real.Gamma (1 - 1 / 2) := by
  norm_num [pow_two]

theorem gap7 :
    Real.Gamma (1 / 2) * Real.Gamma (1 - 1 / 2) =
      Real.pi / Real.sin (Real.pi / 2) := by
  have h : Real.pi * (1 / 2 : ℝ) = Real.pi / 2 := by ring
  rw [← h]
  exact Real.Gamma_mul_Gamma_one_sub (1 / 2 : ℝ)

theorem gap8 :
    Real.pi / Real.sin (Real.pi / 2) = Real.pi := by
  rw [Real.sin_pi_div_two, div_one]

theorem gap9 :
    Real.Gamma (1 / 2) ^ 2 = Real.pi := by
  rw [gap6, gap7, gap8]

theorem gap10 :
    Real.Gamma (1 / 2) = Real.sqrt Real.pi := by
  exact Real.Gamma_one_half_eq

theorem gap11 :
    (∫ x in (0 : ℝ)..1, Real.sqrt (x - x ^ 2)) =
      Real.pi / 8 := by
  rw [gap5, gap10]
  rw [mul_pow, Real.sq_sqrt Real.pi_pos.le]
  norm_num
  ring

end

end ProofGap.Exercise3843

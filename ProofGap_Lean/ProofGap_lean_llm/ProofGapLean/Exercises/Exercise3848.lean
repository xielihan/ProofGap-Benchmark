import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ProofGap.Exercise3848

noncomputable section

open MeasureTheory
open scoped Interval

def betaFn (x y : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..1,
    Real.rpow u (x - 1) * Real.rpow (1 - u) (y - 1)

private theorem rpow_sq_three_halves (x : ℝ) (hx : 0 ≤ x) :
    Real.rpow (x ^ 2) (3 / 2 : ℝ) = x ^ 3 := by
  calc
    Real.rpow (x ^ 2) (3 / 2 : ℝ) =
        Real.rpow (Real.rpow x (2 : ℝ)) (3 / 2 : ℝ) := by
      exact congrArg (fun y => Real.rpow y (3 / 2 : ℝ))
        (Real.rpow_natCast x 2).symm
    _ = Real.rpow x ((2 : ℝ) * (3 / 2 : ℝ)) :=
      (Real.rpow_mul hx (2 : ℝ) (3 / 2 : ℝ)).symm
    _ = x ^ 3 := by
      convert Real.rpow_natCast x 3 using 1 <;> norm_num

private theorem rpow_sq_five_halves (x : ℝ) (hx : 0 ≤ x) :
    Real.rpow (x ^ 2) (5 / 2 : ℝ) = x ^ 5 := by
  calc
    Real.rpow (x ^ 2) (5 / 2 : ℝ) =
        Real.rpow (Real.rpow x (2 : ℝ)) (5 / 2 : ℝ) := by
      exact congrArg (fun y => Real.rpow y (5 / 2 : ℝ))
        (Real.rpow_natCast x 2).symm
    _ = Real.rpow x ((2 : ℝ) * (5 / 2 : ℝ)) :=
      (Real.rpow_mul hx (2 : ℝ) (5 / 2 : ℝ)).symm
    _ = x ^ 5 := by
      convert Real.rpow_natCast x 5 using 1 <;> norm_num

theorem gap1 :
    (∫ x in (0 : ℝ)..Real.pi / 2,
        Real.sin x ^ 6 * Real.cos x ^ 4) =
      ∫ t in (0 : ℝ)..1,
        t ^ 6 * Real.rpow (1 - t ^ 2) (3 / 2 : ℝ) := by
  let g : ℝ → ℝ :=
    fun t => t ^ 6 * Real.rpow (1 - t ^ 2) (3 / 2 : ℝ)
  have hg : Continuous g := by
    exact (continuous_id.pow 6).mul
      ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 3 / 2)).comp
        (continuous_const.sub (continuous_id.pow 2)))
  have hsubst :
      (∫ x in (0 : ℝ)..Real.pi / 2,
          (g ∘ Real.sin) x * Real.cos x) =
        ∫ t in (0 : ℝ)..1, g t := by
    simpa using intervalIntegral.integral_comp_mul_deriv
      (a := (0 : ℝ)) (b := Real.pi / 2)
      (f := Real.sin) (f' := Real.cos) (g := g)
      (fun x hx => Real.hasDerivAt_sin x)
      Real.continuous_cos.continuousOn hg
  calc
    (∫ x in (0 : ℝ)..Real.pi / 2,
        Real.sin x ^ 6 * Real.cos x ^ 4) =
        ∫ x in (0 : ℝ)..Real.pi / 2,
          (g ∘ Real.sin) x * Real.cos x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)] at hx
      have hcos : 0 ≤ Real.cos x :=
        Real.cos_nonneg_of_mem_Icc
          ⟨(neg_nonpos.mpr (by positivity : (0 : ℝ) ≤ Real.pi / 2)).trans hx.1, hx.2⟩
      have htrig : 1 - Real.sin x ^ 2 = Real.cos x ^ 2 := by
        nlinarith [Real.sin_sq_add_cos_sq x]
      change Real.sin x ^ 6 * Real.cos x ^ 4 =
        Real.sin x ^ 6 *
          Real.rpow (1 - Real.sin x ^ 2) (3 / 2 : ℝ) * Real.cos x
      rw [htrig, rpow_sq_three_halves _ hcos]
      ring
    _ = ∫ t in (0 : ℝ)..1, g t := hsubst
    _ = ∫ t in (0 : ℝ)..1,
        t ^ 6 * Real.rpow (1 - t ^ 2) (3 / 2 : ℝ) := by rfl

theorem gap2 :
    (∫ x in (0 : ℝ)..Real.pi / 2,
        Real.sin x ^ 6 * Real.cos x ^ 4) =
      (1 / 2 : ℝ) *
        ∫ u in (0 : ℝ)..1,
          Real.rpow u (5 / 2 : ℝ) *
            Real.rpow (1 - u) (3 / 2 : ℝ) := by
  let g : ℝ → ℝ :=
    fun u => Real.rpow u (5 / 2 : ℝ) *
      Real.rpow (1 - u) (3 / 2 : ℝ)
  have hg : Continuous g := by
    exact
      (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 5 / 2)).mul
        ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 3 / 2)).comp
          (continuous_const.sub continuous_id))
  have hsubst :
      (∫ t in (0 : ℝ)..1,
          (g ∘ fun s : ℝ => s ^ 2) t * (2 * t)) =
        ∫ u in (0 : ℝ)..1, g u := by
    have hraw := intervalIntegral.integral_comp_mul_deriv
      (a := (0 : ℝ)) (b := (1 : ℝ))
      (f := fun s : ℝ => s ^ 2) (f' := fun s : ℝ => 2 * s) (g := g)
      (fun t ht => by
        convert (hasDerivAt_id t).pow 2 using 1 <;> simp)
      ((continuous_const.mul continuous_id).continuousOn) hg
    norm_num at hraw
    exact hraw
  have hpointwise :
      (∫ t in (0 : ℝ)..1,
          (g ∘ fun s : ℝ => s ^ 2) t * (2 * t)) =
        ∫ t in (0 : ℝ)..1,
          2 * (t ^ 6 * Real.rpow (1 - t ^ 2) (3 / 2 : ℝ)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    change
      (Real.rpow (t ^ 2) (5 / 2 : ℝ) *
          Real.rpow (1 - t ^ 2) (3 / 2 : ℝ)) * (2 * t) =
        2 * (t ^ 6 * Real.rpow (1 - t ^ 2) (3 / 2 : ℝ))
    rw [rpow_sq_five_halves _ ht.1]
    ring
  have htwo :
      (2 : ℝ) *
          (∫ t in (0 : ℝ)..1,
            t ^ 6 * Real.rpow (1 - t ^ 2) (3 / 2 : ℝ)) =
        ∫ u in (0 : ℝ)..1, g u := by
    rw [← intervalIntegral.integral_const_mul]
    rw [← hpointwise]
    exact hsubst
  calc
    (∫ x in (0 : ℝ)..Real.pi / 2,
        Real.sin x ^ 6 * Real.cos x ^ 4) =
        ∫ t in (0 : ℝ)..1,
          t ^ 6 * Real.rpow (1 - t ^ 2) (3 / 2 : ℝ) :=
      gap1
    _ = (1 / 2 : ℝ) * (∫ u in (0 : ℝ)..1, g u) := by
      rw [← htwo]
      ring
    _ = (1 / 2 : ℝ) *
        ∫ u in (0 : ℝ)..1,
          Real.rpow u (5 / 2 : ℝ) *
            Real.rpow (1 - u) (3 / 2 : ℝ) := by rfl

theorem gap3 :
    (1 / 2 : ℝ) *
        (∫ u in (0 : ℝ)..1,
          Real.rpow u (5 / 2 : ℝ) *
            Real.rpow (1 - u) (3 / 2 : ℝ)) =
      (1 / 2 : ℝ) * betaFn (7 / 2) (5 / 2) := by
  norm_num [betaFn]

theorem gap4 :
    (1 / 2 : ℝ) * betaFn (7 / 2) (5 / 2) =
      (1 / 2 : ℝ) *
        (Real.Gamma (7 / 2) * Real.Gamma (5 / 2) /
          Real.Gamma 6) := by
  congr 1
  rw [← Complex.ofReal_inj]
  have hbeta :
      (betaFn (7 / 2) (5 / 2) : ℂ) =
        Complex.betaIntegral (7 / 2) (5 / 2) := by
    rw [betaFn, ← intervalIntegral.integral_ofReal, Complex.betaIntegral]
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [Set.uIcc_of_le zero_le_one, Set.mem_Icc] at hx
    dsimp only
    push_cast
    norm_num
    have hxpow :
        (((x ^ (5 / 2 : ℝ)) : ℝ) : ℂ) =
          (x : ℂ) ^ ((5 / 2 : ℝ) : ℂ) :=
      Complex.ofReal_cpow hx.1 (5 / 2 : ℝ)
    have honepow :
        ((((1 - x) ^ (3 / 2 : ℝ)) : ℝ) : ℂ) =
          ((1 - x : ℝ) : ℂ) ^ ((3 / 2 : ℝ) : ℂ) :=
      Complex.ofReal_cpow (sub_nonneg.mpr hx.2) (3 / 2 : ℝ)
    rw [hxpow, honepow]
    push_cast
    norm_num
  rw [hbeta]
  rw [Complex.betaIntegral_eq_Gamma_mul_div
    (7 / 2) (5 / 2) (by norm_num) (by norm_num)]
  push_cast
  have h72 : (7 / 2 : ℂ) = ((7 / 2 : ℝ) : ℂ) := by norm_num
  have h52 : (5 / 2 : ℂ) = ((5 / 2 : ℝ) : ℂ) := by norm_num
  have hsum :
      ((7 / 2 : ℝ) : ℂ) + ((5 / 2 : ℝ) : ℂ) = ((6 : ℝ) : ℂ) := by norm_num
  rw [h72, h52, hsum]
  rw [Complex.Gamma_ofReal]
  rw [Complex.Gamma_ofReal (5 / 2 : ℝ)]
  rw [Complex.Gamma_ofReal (6 : ℝ)]

theorem gap5 :
    (∫ x in (0 : ℝ)..Real.pi / 2,
        Real.sin x ^ 6 * Real.cos x ^ 4) =
      (1 / 2 : ℝ) *
        (Real.Gamma (7 / 2) * Real.Gamma (5 / 2) /
          Real.Gamma 6) := by
  rw [gap2, gap3, gap4]

private theorem gamma_three_half :
    Real.Gamma (3 / 2) = (1 / 2 : ℝ) * Real.sqrt Real.pi := by
  rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
    Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0)]
  rw [Real.Gamma_one_half_eq]

private theorem gamma_five_half :
    Real.Gamma (5 / 2) =
      (3 / 2 : ℝ) * ((1 / 2 : ℝ) * Real.sqrt Real.pi) := by
  rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num,
    Real.Gamma_add_one (by norm_num : (3 / 2 : ℝ) ≠ 0)]
  rw [gamma_three_half]

private theorem gamma_seven_half :
    Real.Gamma (7 / 2) =
      (5 / 2 : ℝ) *
        ((3 / 2 : ℝ) * ((1 / 2 : ℝ) * Real.sqrt Real.pi)) := by
  rw [show (7 / 2 : ℝ) = 5 / 2 + 1 by norm_num,
    Real.Gamma_add_one (by norm_num : (5 / 2 : ℝ) ≠ 0)]
  rw [gamma_five_half]

private theorem gamma_six :
    Real.Gamma 6 = (Nat.factorial 5 : ℝ) := by
  rw [show (6 : ℝ) = (5 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]

theorem gap6 :
    (∫ x in (0 : ℝ)..Real.pi / 2,
        Real.sin x ^ 6 * Real.cos x ^ 4) =
      (1 / 2 : ℝ) *
        (((5 / 2 : ℝ) * (3 / 2 : ℝ) * (1 / 2 : ℝ) *
              Real.sqrt Real.pi *
            (3 / 2 : ℝ) * (1 / 2 : ℝ) * Real.sqrt Real.pi) /
          (Nat.factorial 5 : ℝ)) := by
  rw [gap5, gamma_seven_half, gamma_five_half, gamma_six]
  ring

theorem gap7 :
    (1 / 2 : ℝ) *
        (((5 / 2 : ℝ) * (3 / 2 : ℝ) * (1 / 2 : ℝ) *
              Real.sqrt Real.pi *
            (3 / 2 : ℝ) * (1 / 2 : ℝ) * Real.sqrt Real.pi) /
          (Nat.factorial 5 : ℝ)) =
      3 * Real.pi / 512 := by
  norm_num
  ring_nf
  rw [Real.sq_sqrt Real.pi_pos.le]

theorem gap8 :
    (∫ x in (0 : ℝ)..Real.pi / 2,
        Real.sin x ^ 6 * Real.cos x ^ 4) =
      3 * Real.pi / 512 := by
  rw [gap6, gap7]

end

end ProofGap.Exercise3848

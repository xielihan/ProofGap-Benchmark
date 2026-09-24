import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ProofGap.Exercise3844

noncomputable section

open MeasureTheory
open scoped Interval

def betaFn (x y : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    Real.rpow t (x - 1) * Real.rpow (1 - t) (y - 1)

private theorem twice_u_integral_eq_beta_integral :
    2 * (∫ u in (0 : ℝ)..1,
      u ^ 2 * Real.rpow (1 - u ^ 2) (1 / 2 : ℝ)) =
      ∫ t in (0 : ℝ)..1,
        Real.rpow t (1 / 2 : ℝ) *
          Real.rpow (1 - t) (1 / 2 : ℝ) := by
  let g : ℝ → ℝ := fun t =>
    t ^ (1 / 2 : ℝ) * (1 - t) ^ (1 / 2 : ℝ)
  have hhalf : 0 ≤ (1 / 2 : ℝ) := by norm_num
  have hg : Continuous g := by
    dsimp [g]
    exact (Real.continuous_rpow_const hhalf).mul
      ((continuous_const.sub continuous_id).rpow_const
        (fun _ => Or.inr hhalf))
  have hsquare :
      ∀ u ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun s : ℝ => s ^ 2) (2 * u) u := by
    intro u _
    convert (hasDerivAt_id u).pow 2 using 1 <;> norm_num <;> ring
  have hderivContinuous :
      ContinuousOn (fun u : ℝ => 2 * u) (Set.uIcc (0 : ℝ) 1) := by
    fun_prop
  have hsub :=
    intervalIntegral.integral_comp_mul_deriv
      (a := (0 : ℝ)) (b := 1)
      (f := fun u : ℝ => u ^ 2) (f' := fun u : ℝ => 2 * u)
      (g := g) hsquare hderivContinuous hg
  simp only [Real.rpow_eq_pow]
  calc
    2 * (∫ u in (0 : ℝ)..1,
        u ^ 2 * (1 - u ^ 2) ^ (1 / 2 : ℝ)) =
        ∫ u in (0 : ℝ)..1,
          2 * (u ^ 2 * (1 - u ^ 2) ^ (1 / 2 : ℝ)) := by
      rw [intervalIntegral.integral_const_mul]
    _ = ∫ u in (0 : ℝ)..1,
          (g ∘ fun s : ℝ => s ^ 2) u * (2 * u) := by
      apply intervalIntegral.integral_congr
      intro u hu
      have hu0 : 0 ≤ u := by
        rw [Set.uIcc_of_le (by norm_num)] at hu
        exact hu.1
      have hroot : (u ^ 2) ^ (1 / 2 : ℝ) = u := by
        rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hu0]
      dsimp [g, Function.comp_def]
      rw [hroot]
      ring
    _ = ∫ t in (0 : ℝ) ^ 2..(1 : ℝ) ^ 2, g t := hsub
    _ = ∫ t in (0 : ℝ)..1,
          t ^ (1 / 2 : ℝ) * (1 - t) ^ (1 / 2 : ℝ) := by
      norm_num [g]

private theorem betaFn_three_halves :
    betaFn (3 / 2) (3 / 2) = Real.pi / 8 := by
  have hscale :
      2 * (∫ t in (0 : ℝ)..1,
        Real.sqrt (1 - (2 * t - 1) ^ 2)) =
        ∫ x in (-1 : ℝ)..1, Real.sqrt (1 - x ^ 2) := by
    convert
      (intervalIntegral.smul_integral_comp_mul_sub
        (fun x : ℝ => Real.sqrt (1 - x ^ 2))
        (a := (0 : ℝ)) (b := 1) 2 1) using 1 <;>
      norm_num [smul_eq_mul]
  have hpoint :
      ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        Real.sqrt (1 - (2 * t - 1) ^ 2) =
          2 * (Real.rpow t (1 / 2 : ℝ) *
            Real.rpow (1 - t) (1 / 2 : ℝ)) := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num)] at ht
    have ht0 : 0 ≤ t := ht.1
    rw [Real.rpow_eq_pow, Real.rpow_eq_pow]
    rw [show 1 - (2 * t - 1) ^ 2 =
        4 * (t * (1 - t)) by ring]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
    rw [Real.sqrt_mul ht0, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  have hcongr :
      (∫ t in (0 : ℝ)..1,
        Real.sqrt (1 - (2 * t - 1) ^ 2)) =
        ∫ t in (0 : ℝ)..1,
          2 * (Real.rpow t (1 / 2 : ℝ) *
            Real.rpow (1 - t) (1 / 2 : ℝ)) := by
    apply intervalIntegral.integral_congr
    exact hpoint
  have hdef :
      betaFn (3 / 2) (3 / 2) =
        ∫ t in (0 : ℝ)..1,
          Real.rpow t (1 / 2 : ℝ) *
            Real.rpow (1 - t) (1 / 2 : ℝ) := by
    unfold betaFn
    apply intervalIntegral.integral_congr
    intro t _
    congr 1 <;> norm_num
  rw [hcongr, intervalIntegral.integral_const_mul,
    integral_sqrt_one_sub_sq, ← hdef] at hscale
  linarith

theorem gap1 (a : ℝ) (ha : 0 < a) :
    (∫ x in (0 : ℝ)..a, x ^ 2 * Real.sqrt (a ^ 2 - x ^ 2)) =
      a ^ 4 *
        ∫ u in (0 : ℝ)..1,
          u ^ 2 * Real.rpow (1 - u ^ 2) (1 / 2 : ℝ) := by
  have hchange :
      (∫ x in (0 : ℝ)..a, x ^ 2 * Real.sqrt (a ^ 2 - x ^ 2)) =
        a * ∫ u in (0 : ℝ)..1,
          (a * u) ^ 2 * Real.sqrt (a ^ 2 - (a * u) ^ 2) := by
    simpa [smul_eq_mul] using
      (intervalIntegral.smul_integral_comp_mul_left
        (fun x : ℝ => x ^ 2 * Real.sqrt (a ^ 2 - x ^ 2))
        (a := (0 : ℝ)) (b := 1) a).symm
  calc
    (∫ x in (0 : ℝ)..a, x ^ 2 * Real.sqrt (a ^ 2 - x ^ 2)) =
        a * ∫ u in (0 : ℝ)..1,
          (a * u) ^ 2 * Real.sqrt (a ^ 2 - (a * u) ^ 2) :=
      hchange
    _ = a * ∫ u in (0 : ℝ)..1,
          a ^ 3 * (u ^ 2 *
            Real.rpow (1 - u ^ 2) (1 / 2 : ℝ)) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro u _
      change
        (a * u) ^ 2 * Real.sqrt (a ^ 2 - (a * u) ^ 2) =
          a ^ 3 * (u ^ 2 *
            Real.rpow (1 - u ^ 2) (1 / 2 : ℝ))
      rw [show a ^ 2 - (a * u) ^ 2 =
          a ^ 2 * (1 - u ^ 2) by ring]
      rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha.le,
        Real.sqrt_eq_rpow]
      rw [Real.rpow_eq_pow]
      ring
    _ = a ^ 4 * ∫ u in (0 : ℝ)..1,
          u ^ 2 * Real.rpow (1 - u ^ 2) (1 / 2 : ℝ) := by
      rw [intervalIntegral.integral_const_mul]
      ring

theorem gap2 (a : ℝ) (ha : 0 < a) :
    (∫ x in (0 : ℝ)..a, x ^ 2 * Real.sqrt (a ^ 2 - x ^ 2)) =
      a ^ 4 / 2 *
        ∫ t in (0 : ℝ)..1,
          Real.rpow t (1 / 2 : ℝ) *
            Real.rpow (1 - t) (1 / 2 : ℝ) := by
  calc
    (∫ x in (0 : ℝ)..a, x ^ 2 * Real.sqrt (a ^ 2 - x ^ 2)) =
        a ^ 4 * (∫ u in (0 : ℝ)..1,
          u ^ 2 * Real.rpow (1 - u ^ 2) (1 / 2 : ℝ)) :=
      gap1 a ha
    _ = a ^ 4 / 2 *
        ∫ t in (0 : ℝ)..1,
          Real.rpow t (1 / 2 : ℝ) *
            Real.rpow (1 - t) (1 / 2 : ℝ) := by
      rw [← twice_u_integral_eq_beta_integral]
      ring

theorem gap3 (a : ℝ) (ha : 0 < a) :
    a ^ 4 / 2 *
        (∫ t in (0 : ℝ)..1,
          Real.rpow t (1 / 2 : ℝ) *
            Real.rpow (1 - t) (1 / 2 : ℝ)) =
      a ^ 4 / 2 * betaFn (3 / 2) (3 / 2) := by
  unfold betaFn
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  congr 1 <;> norm_num

theorem gap4 (a : ℝ) (ha : 0 < a) :
    a ^ 4 / 2 * betaFn (3 / 2) (3 / 2) =
      Real.pi * a ^ 4 / 16 := by
  rw [betaFn_three_halves]
  ring

theorem gap5 (a : ℝ) (ha : 0 < a) :
    (∫ x in (0 : ℝ)..a, x ^ 2 * Real.sqrt (a ^ 2 - x ^ 2)) =
      Real.pi * a ^ 4 / 16 := by
  exact (gap2 a ha).trans ((gap3 a ha).trans (gap4 a ha))

end

end ProofGap.Exercise3844

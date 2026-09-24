import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic

open scoped Interval

namespace ProofGap.Exercise2271

noncomputable section

def cubeRoot (x : ℝ) : ℝ :=
  if x < 0 then -Real.rpow (-x) (1 / 3 : ℝ) else Real.rpow x (1 / 3 : ℝ)

def originalIntegral : ℝ :=
  ∫ x in 1..9, x * cubeRoot (1 - x)

def transformedIntegral : ℝ :=
  -3 * ∫ t in 0..(-2), (t ^ 3 - t ^ 6)

theorem gap1 :
    originalIntegral = transformedIntegral := by
  have hcube (x : ℝ) (hx : 1 ≤ x) :
      cubeRoot (1 - x) = -Real.rpow (x - 1) (1 / 3 : ℝ) := by
    by_cases hxeq : x = 1
    · subst x
      norm_num [cubeRoot]
    · have hxgt : 1 < x := lt_of_le_of_ne hx (Ne.symm hxeq)
      have hxlt : 1 - x < 0 := by linarith
      rw [cubeRoot, if_pos hxlt]
      congr 2
      ring
  have hrpow : Continuous (fun x : ℝ => Real.rpow (x - 1) (1 / 3 : ℝ)) := by
    apply Continuous.rpow (continuous_id.sub continuous_const) continuous_const
    intro x
    right
    norm_num
  have hgcont : Continuous
      (fun x : ℝ => x * (-Real.rpow (x - 1) (1 / 3 : ℝ))) :=
    continuous_id.mul hrpow.neg
  have horig :
      originalIntegral =
        ∫ x in (1 : ℝ)..9, x * (-Real.rpow (x - 1) (1 / 3 : ℝ)) := by
    unfold originalIntegral
    apply intervalIntegral.integral_congr
    intro x hx
    have hx1 : 1 ≤ x := by
      norm_num [Set.mem_uIcc] at hx
      exact hx.1
    exact congrArg (fun z : ℝ => x * z) (hcube x hx1)
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) (-2),
      HasDerivAt (fun u : ℝ => 1 - u ^ 3) (-3 * t ^ 2) t := by
    intro t ht
    have h1 := hasDerivAt_id t
    have h2 := h1.mul h1
    have h3 := h2.mul h1
    convert (hasDerivAt_const t (1 : ℝ)).sub h3 using 1
    · funext u
      dsimp
      ring
    · dsimp
      ring
  have hderivCont : Continuous (fun t : ℝ => -3 * t ^ 2) :=
    continuous_const.mul (continuous_id.pow 2)
  have hsub := intervalIntegral.integral_comp_mul_deriv
    (a := (0 : ℝ)) (b := (-2 : ℝ))
    (f := fun t : ℝ => 1 - t ^ 3)
    (f' := fun t : ℝ => -3 * t ^ 2)
    (g := fun x : ℝ => x * (-Real.rpow (x - 1) (1 / 3 : ℝ)))
    hderiv hderivCont.continuousOn hgcont
  norm_num at hsub
  have hsub' :
      (∫ t in (0 : ℝ)..(-2),
        ((1 - t ^ 3) * (-Real.rpow ((1 - t ^ 3) - 1) (1 / 3 : ℝ))) *
          (-3 * t ^ 2)) =
        ∫ x in (1 : ℝ)..9,
          x * (-Real.rpow (x - 1) (1 / 3 : ℝ)) := by
    simpa [Function.comp_def] using hsub
  unfold transformedIntegral
  calc
    originalIntegral =
        ∫ x in (1 : ℝ)..9,
          x * (-Real.rpow (x - 1) (1 / 3 : ℝ)) := horig
    _ = ∫ t in (0 : ℝ)..(-2),
          ((1 - t ^ 3) * (-Real.rpow ((1 - t ^ 3) - 1) (1 / 3 : ℝ))) *
            (-3 * t ^ 2) := hsub'.symm
    _ = -3 * ∫ t in (0 : ℝ)..(-2), (t ^ 3 - t ^ 6) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t ht
      have ht0 : t ≤ 0 := by
        norm_num [Set.mem_uIcc] at ht
        exact ht.2
      have hp : Real.rpow ((-t) ^ (3 : ℕ)) ((3 : ℝ)⁻¹) = -t :=
        Real.pow_rpow_inv_natCast (x := -t) (n := 3)
          (neg_nonneg.mpr ht0) (by norm_num)
      have hroot : Real.rpow (-t ^ 3) (1 / 3 : ℝ) = -t := by
        rw [show -t ^ 3 = (-t) ^ (3 : ℕ) by ring]
        simpa [one_div] using hp
      change
        ((1 - t ^ 3) * (-Real.rpow ((1 - t ^ 3) - 1) (1 / 3 : ℝ))) *
            (-3 * t ^ 2) =
          -3 * (t ^ 3 - t ^ 6)
      rw [show (1 - t ^ 3) - 1 = -t ^ 3 by ring, hroot]
      ring

theorem gap2 :
    transformedIntegral = -(468 / 7 : ℝ) := by
  have hanti (t : ℝ) :
      HasDerivAt (fun u : ℝ => u ^ 4 / 4 - u ^ 7 / 7) (t ^ 3 - t ^ 6) t := by
    have h1 := hasDerivAt_id t
    have h2 := h1.mul h1
    have h3 := h2.mul h1
    have h4 := h3.mul h1
    have h5 := h4.mul h1
    have h6 := h5.mul h1
    have h7 := h6.mul h1
    have h4scaled := h4.const_mul (1 / 4 : ℝ)
    have h7scaled := h7.const_mul (1 / 7 : ℝ)
    convert h4scaled.sub h7scaled using 1
    · funext u
      dsimp
      ring
    · dsimp
      ring
  have hcontinuous : Continuous (fun t : ℝ => t ^ 3 - t ^ 6) :=
    (continuous_id.pow 3).sub (continuous_id.pow 6)
  have hint :
      (∫ t in (0 : ℝ)..(-2), t ^ 3 - t ^ 6) =
        (((-2 : ℝ) ^ 4 / 4 - (-2 : ℝ) ^ 7 / 7) -
          ((0 : ℝ) ^ 4 / 4 - (0 : ℝ) ^ 7 / 7)) := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hanti t)
      (hcontinuous.intervalIntegrable (0 : ℝ) (-2 : ℝ))
  unfold transformedIntegral
  rw [hint]
  norm_num

theorem gap3 :
    originalIntegral = -(468 / 7 : ℝ) := by
  rw [gap1, gap2]

end

end ProofGap.Exercise2271

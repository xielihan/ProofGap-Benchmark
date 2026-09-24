import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

open scoped Interval

namespace ProofGap.Exercise2255

noncomputable section

def tOfX (x : ℝ) : ℝ := x ^ 2
def jacobian (x : ℝ) : ℝ := 2 * x
def xOfT (t : ℝ) : ℝ := Real.sqrt t

def pullback (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.rpow t (3 / 2 : ℝ) * f t / (2 * Real.sqrt t)

private theorem rpow_three_halves_eq_mul_sqrt {t : ℝ} (ht : 0 < t) :
    Real.rpow t (3 / 2 : ℝ) = t * Real.sqrt t := by
  change t ^ (3 / 2 : ℝ) = t * Real.sqrt t
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num]
  rw [Real.rpow_add ht, Real.rpow_one, ← Real.sqrt_eq_rpow]

private theorem pullback_eq_half_mul (f : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    pullback f t = (1 / 2 : ℝ) * (t * f t) := by
  by_cases ht0 : t = 0
  · subst t
    norm_num [pullback]
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    have hsqrt : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 htpos).ne'
    unfold pullback
    rw [rpow_three_halves_eq_mul_sqrt htpos]
    field_simp [hsqrt]

private theorem integral_pullback_eq_half (a : ℝ) (f : ℝ → ℝ) :
    (∫ t in (0 : ℝ)..a ^ 2, pullback f t) =
      (1 / 2 : ℝ) * ∫ t in (0 : ℝ)..a ^ 2, t * f t := by
  calc
    (∫ t in (0 : ℝ)..a ^ 2, pullback f t) =
        ∫ t in (0 : ℝ)..a ^ 2, (1 / 2 : ℝ) * (t * f t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (sq_nonneg a)] at ht
      exact pullback_eq_half_mul f ht.1
    _ = (1 / 2 : ℝ) * ∫ t in (0 : ℝ)..a ^ 2, t * f t := by
      rw [intervalIntegral.integral_const_mul]

private theorem integral_square_substitution (a : ℝ) (f : ℝ → ℝ)
    (hf : Continuous f) :
    (∫ x in (0 : ℝ)..a, x ^ 3 * f (x ^ 2)) =
      (1 / 2 : ℝ) * ∫ t in (0 : ℝ)..a ^ 2, t * f t := by
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) a,
      HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    intro x hx
    have h := (hasDerivAt_id x).mul (hasDerivAt_id x)
    convert h using 1
    · funext y
      simp [id_eq, pow_two]
    · simp [id_eq]
      ring
  have hderivContinuous :
      ContinuousOn (fun x : ℝ => 2 * x) (Set.uIcc (0 : ℝ) a) :=
    (continuous_const.mul continuous_id).continuousOn
  have hintegrand : Continuous (fun t : ℝ => (1 / 2 : ℝ) * (t * f t)) :=
    continuous_const.mul (continuous_id.mul hf)
  have hsub :
      (∫ x in (0 : ℝ)..a,
          ((1 / 2 : ℝ) * (x ^ 2 * f (x ^ 2))) * (2 * x)) =
        ∫ t in (0 : ℝ)..a ^ 2, (1 / 2 : ℝ) * (t * f t) := by
    simpa [Function.comp_def] using
      (intervalIntegral.integral_comp_mul_deriv
        (a := (0 : ℝ)) (b := a)
        (f := fun x : ℝ => x ^ 2) (f' := fun x : ℝ => 2 * x)
        (g := fun t : ℝ => (1 / 2 : ℝ) * (t * f t))
        hderiv hderivContinuous hintegrand)
  calc
    (∫ x in (0 : ℝ)..a, x ^ 3 * f (x ^ 2)) =
        ∫ x in (0 : ℝ)..a,
          ((1 / 2 : ℝ) * (x ^ 2 * f (x ^ 2))) * (2 * x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      ring
    _ = ∫ t in (0 : ℝ)..a ^ 2, (1 / 2 : ℝ) * (t * f t) := hsub
    _ = (1 / 2 : ℝ) * ∫ t in (0 : ℝ)..a ^ 2, t * f t := by
      rw [intervalIntegral.integral_const_mul]

theorem gap1 (a : ℝ) (ha : 0 ≤ a) (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ x in (0 : ℝ)..a, x ^ 3 * f (x ^ 2)) =
      ∫ t in (0 : ℝ)..a ^ 2, pullback f t := by
  rw [integral_square_substitution a f hf, integral_pullback_eq_half a f]

theorem gap2 (a : ℝ) (ha : 0 ≤ a) (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ t in (0 : ℝ)..a ^ 2, pullback f t) =
      (1 / 2 : ℝ) * ∫ t in (0 : ℝ)..a ^ 2, t * f t := by
  exact integral_pullback_eq_half a f

theorem gap3 (a : ℝ) (ha : 0 ≤ a) (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ x in (0 : ℝ)..a, x ^ 3 * f (x ^ 2)) =
      (1 / 2 : ℝ) * ∫ t in (0 : ℝ)..a ^ 2, t * f t := by
  exact (gap1 a ha f hf).trans (gap2 a ha f hf)

theorem gap4 (a : ℝ) (ha : 0 ≤ a) (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ x in (0 : ℝ)..a, x ^ 3 * f (x ^ 2)) =
      (1 / 2 : ℝ) * ∫ x in (0 : ℝ)..a ^ 2, x * f x := by
  exact gap3 a ha f hf

theorem gap5 (a : ℝ) (ha : 0 ≤ a) (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ x in (0 : ℝ)..a, x ^ 3 * f (x ^ 2)) =
      (1 / 2 : ℝ) * ∫ x in (0 : ℝ)..a ^ 2, x * f x := by
  exact gap4 a ha f hf

end

end ProofGap.Exercise2255

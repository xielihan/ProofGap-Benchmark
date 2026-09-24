import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open scoped Interval

namespace ProofGap.Exercise2273

noncomputable section

def substitution (x : ℝ) : ℝ := 1 + 3 * x ^ 8

def originalIntegral : ℝ :=
  ∫ x in 0..1, x ^ 15 * Real.sqrt (1 + 3 * x ^ 8)

def transformedIntegral : ℝ :=
  (1 / 72 : ℝ) * ∫ t in 1..4, (t - 1) * Real.sqrt t

private def integralAntiderivative (t : ℝ) : ℝ :=
  (2 / 5 : ℝ) * (t ^ 2 * Real.sqrt t) -
    (2 / 3 : ℝ) * (t * Real.sqrt t)

private theorem hasDerivAt_integralAntiderivative {t : ℝ} (ht : 0 < t) :
    HasDerivAt integralAntiderivative ((t - 1) * Real.sqrt t) t := by
  have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hpow : HasDerivAt (fun z : ℝ => z ^ 2) (2 * t) t := by
    simpa using (hasDerivAt_id t).pow 2
  unfold integralAntiderivative
  convert
    ((((hpow.mul (Real.hasDerivAt_sqrt ht.ne')).const_mul (2 / 5 : ℝ)).sub
      (((hasDerivAt_id t).mul
        (Real.hasDerivAt_sqrt ht.ne')).const_mul (2 / 3 : ℝ)))) using 1
  field_simp [hsqrt.ne']
  simp only [id_eq, Real.sq_sqrt ht.le]
  ring

private theorem kernel_integral_value :
    (∫ t in (1 : ℝ)..4, (t - 1) * Real.sqrt t) = (116 / 15 : ℝ) := by
  calc
    (∫ t in (1 : ℝ)..4, (t - 1) * Real.sqrt t) =
        integralAntiderivative 4 - integralAntiderivative 1 := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := integralAntiderivative)
        (f' := fun t : ℝ => (t - 1) * Real.sqrt t) ?_ ?_
      · intro t ht
        rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 4)] at ht
        apply hasDerivAt_integralAntiderivative
        nlinarith [ht.1]
      · have hcontinuous :
            Continuous (fun t : ℝ => (t - 1) * Real.sqrt t) :=
          (continuous_id.sub continuous_const).mul Real.continuous_sqrt
        exact hcontinuous.intervalIntegrable
          (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) 1 4
    _ = (116 / 15 : ℝ) := by
      have h4 : Real.sqrt (4 : ℝ) = 2 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4),
          Real.sqrt_nonneg (4 : ℝ)]
      have h1 : Real.sqrt (1 : ℝ) = 1 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1),
          Real.sqrt_nonneg (1 : ℝ)]
      unfold integralAntiderivative
      rw [h4, h1]
      norm_num

theorem gap1 (x : ℝ) :
    HasDerivAt substitution (24 * x ^ 7) x := by
  have h : HasDerivAt substitution (3 * (8 * x ^ 7)) x := by
    simpa [substitution] using
      (hasDerivAt_const x (1 : ℝ)).add
        ((hasDerivAt_const x (3 : ℝ)).mul ((hasDerivAt_id x).pow 8))
  have heq : (3 : ℝ) * (8 * x ^ 7) = 24 * x ^ 7 := by
    ring
  rw [← heq]
  exact h

theorem gap2 (x t : ℝ) (ht : t = substitution x) :
    x ^ 8 = (t - 1) / 3 := by
  subst t
  unfold substitution
  ring

theorem gap3 :
    originalIntegral = transformedIntegral := by
  have hderiv :
      ∀ x : ℝ,
        HasDerivAt
          (fun y : ℝ =>
            (1 / 72 : ℝ) * integralAntiderivative (substitution y))
          (x ^ 15 * Real.sqrt (1 + 3 * x ^ 8)) x := by
    intro x
    have hs : 0 < substitution x := by
      unfold substitution
      positivity
    have hc :
        HasDerivAt
          (fun y : ℝ => integralAntiderivative (substitution y))
          (((substitution x - 1) * Real.sqrt (substitution x)) *
            (24 * x ^ 7)) x := by
      simpa only [Function.comp_apply] using
        (hasDerivAt_integralAntiderivative hs).comp x (gap1 x)
    convert (hasDerivAt_const x (1 / 72 : ℝ)).mul hc using 1
    dsimp [substitution]
    ring
  calc
    originalIntegral =
        (1 / 72 : ℝ) * integralAntiderivative (substitution 1) -
          (1 / 72 : ℝ) * integralAntiderivative (substitution 0) := by
      unfold originalIntegral
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun y : ℝ =>
          (1 / 72 : ℝ) * integralAntiderivative (substitution y))
        (f' := fun x : ℝ =>
          x ^ 15 * Real.sqrt (1 + 3 * x ^ 8)) ?_ ?_
      · intro x hx
        exact hderiv x
      · have hcontinuous :
            Continuous (fun x : ℝ =>
              x ^ 15 * Real.sqrt (1 + 3 * x ^ 8)) :=
          (continuous_id.pow 15).mul
            (Real.continuous_sqrt.comp
              (continuous_const.add
                (continuous_const.mul (continuous_id.pow 8))))
        exact hcontinuous.intervalIntegrable
          (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) 0 1
    _ = (29 / 270 : ℝ) := by
      have h4 : Real.sqrt (4 : ℝ) = 2 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4),
          Real.sqrt_nonneg (4 : ℝ)]
      have h1 : Real.sqrt (1 : ℝ) = 1 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1),
          Real.sqrt_nonneg (1 : ℝ)]
      norm_num [integralAntiderivative, substitution, h4, h1]
    _ = transformedIntegral := by
      unfold transformedIntegral
      rw [kernel_integral_value]
      norm_num

theorem gap4 :
    transformedIntegral = (29 / 270 : ℝ) := by
  unfold transformedIntegral
  rw [kernel_integral_value]
  norm_num

theorem gap5 :
    originalIntegral = (29 / 270 : ℝ) := by
  exact gap3.trans gap4

end

end ProofGap.Exercise2273

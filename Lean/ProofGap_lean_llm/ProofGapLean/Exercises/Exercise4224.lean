import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise4224

noncomputable section

open scoped Interval

def curveMap (a t : ℝ) : ℝ × ℝ :=
  (a * Real.cosh t, a * Real.sinh t)

def curve (a t₀ : ℝ) : Set (ℝ × ℝ) :=
  curveMap a '' Set.Icc 0 t₀

def rawSpeed (a t : ℝ) : ℝ :=
  Real.sqrt (a ^ 2 * Real.sinh t ^ 2 + a ^ 2 * Real.cosh t ^ 2)

def speed (a t : ℝ) : ℝ :=
  a * Real.sqrt (Real.cosh (2 * t))

def weightedLength (a t₀ : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..t₀,
    (curveMap a t).1 * (curveMap a t).2 * rawSpeed a t

private theorem integral_hyperbolic_sqrt (t₀ : ℝ) :
    (∫ t in (0 : ℝ)..t₀,
      Real.sqrt (Real.cosh (2 * t)) * (2 * Real.sinh (2 * t))) =
      (2 / 3 : ℝ) *
          (Real.cosh (2 * t₀) * Real.sqrt (Real.cosh (2 * t₀))) -
        2 / 3 := by
  let F : ℝ → ℝ := fun x =>
    (2 / 3 : ℝ) *
      (Real.cosh (2 * x) * Real.sqrt (Real.cosh (2 * x)))
  have hderiv : ∀ x : ℝ,
      HasDerivAt F
        (Real.sqrt (Real.cosh (2 * x)) * (2 * Real.sinh (2 * x))) x := by
    intro x
    have hu : 0 < Real.cosh (2 * x) := Real.cosh_pos (2 * x)
    have hspos : 0 < Real.sqrt (Real.cosh (2 * x)) :=
      Real.sqrt_pos.2 hu
    have hsq : Real.sqrt (Real.cosh (2 * x)) ^ 2 = Real.cosh (2 * x) :=
      Real.sq_sqrt (le_of_lt hu)
    have hsq' : Real.sqrt (Real.cosh (x * 2)) ^ 2 = Real.cosh (x * 2) := by
      simpa only [mul_comm] using hsq
    have hinner : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
      simpa using (hasDerivAt_id x).const_mul 2
    have hcosh :
        HasDerivAt (fun y : ℝ => Real.cosh (2 * y))
          (2 * Real.sinh (2 * x)) x := by
      convert (Real.hasDerivAt_cosh (2 * x)).comp x hinner using 1 <;> ring
    have hsqrt :=
      (Real.hasDerivAt_sqrt (ne_of_gt hu)).comp x hcosh
    have hfull := (hcosh.mul hsqrt).const_mul (2 / 3 : ℝ)
    simp only [Function.comp_apply] at hfull
    dsimp [F]
    convert hfull using 1
    field_simp [ne_of_gt hspos] <;> ring_nf <;> rw [hsq'] <;> ring
  have hlin : Continuous (fun x : ℝ => 2 * x) :=
    continuous_const.mul continuous_id
  have hcosh : Continuous (fun x : ℝ => Real.cosh (2 * x)) :=
    Real.continuous_cosh.comp hlin
  have hsqrt : Continuous (fun x : ℝ => Real.sqrt (Real.cosh (2 * x))) :=
    Real.continuous_sqrt.comp hcosh
  have hsinh : Continuous (fun x : ℝ => Real.sinh (2 * x)) :=
    Real.continuous_sinh.comp hlin
  have hint : Continuous
      (fun x : ℝ =>
        Real.sqrt (Real.cosh (2 * x)) * (2 * Real.sinh (2 * x))) :=
    hsqrt.mul (continuous_const.mul hsinh)
  have hi :
      (∫ t in (0 : ℝ)..t₀,
        Real.sqrt (Real.cosh (2 * t)) * (2 * Real.sinh (2 * t))) =
        F t₀ - F 0 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hderiv x) (hint.intervalIntegrable 0 t₀)
  simpa [F] using hi

theorem gap1 (a t : ℝ) :
    rawSpeed a t =
      Real.sqrt (a ^ 2 * Real.sinh t ^ 2 + a ^ 2 * Real.cosh t ^ 2) := by
  rfl

theorem gap2 (a t : ℝ) (ha : 0 < a) :
    rawSpeed a t = speed a t := by
  unfold rawSpeed speed
  have hsum :
      Real.sinh t ^ 2 + Real.cosh t ^ 2 = Real.cosh (2 * t) := by
    rw [Real.cosh_two_mul]
    nlinarith [Real.cosh_sq_sub_sinh_sq t]
  rw [← mul_add, hsum, Real.sqrt_mul (sq_nonneg a),
    Real.sqrt_sq_eq_abs, abs_of_pos ha]

theorem gap3 (a t : ℝ) (ha : 0 < a) :
    rawSpeed a t = a * Real.sqrt (Real.cosh (2 * t)) := by
  exact gap2 a t ha

theorem gap4 (a t₀ : ℝ) (ha : 0 < a) (ht : 0 ≤ t₀) :
    weightedLength a t₀ =
      a ^ 3 *
        ∫ t in (0 : ℝ)..t₀,
          Real.cosh t * Real.sinh t * Real.sqrt (Real.cosh (2 * t)) := by
  unfold weightedLength
  calc
    (∫ t in (0 : ℝ)..t₀,
        (curveMap a t).1 * (curveMap a t).2 * rawSpeed a t) =
        ∫ t in (0 : ℝ)..t₀,
          a ^ 3 *
            (Real.cosh t * Real.sinh t *
              Real.sqrt (Real.cosh (2 * t))) := by
      apply intervalIntegral.integral_congr
      intro t _
      change
        (curveMap a t).1 * (curveMap a t).2 * rawSpeed a t =
          a ^ 3 *
            (Real.cosh t * Real.sinh t *
              Real.sqrt (Real.cosh (2 * t)))
      rw [gap3 a t ha]
      simp only [curveMap]
      ring
    _ = a ^ 3 *
        ∫ t in (0 : ℝ)..t₀,
          Real.cosh t * Real.sinh t *
            Real.sqrt (Real.cosh (2 * t)) := by
      rw [intervalIntegral.integral_const_mul]

theorem gap5 (a t₀ : ℝ) :
    a ^ 3 *
        (∫ t in (0 : ℝ)..t₀,
          Real.cosh t * Real.sinh t * Real.sqrt (Real.cosh (2 * t))) =
      a ^ 3 / 2 *
        ∫ t in (0 : ℝ)..t₀,
          Real.sinh (2 * t) * Real.sqrt (Real.cosh (2 * t)) := by
  calc
    a ^ 3 *
        (∫ t in (0 : ℝ)..t₀,
          Real.cosh t * Real.sinh t * Real.sqrt (Real.cosh (2 * t))) =
      a ^ 3 / 2 *
        (2 * ∫ t in (0 : ℝ)..t₀,
          Real.cosh t * Real.sinh t * Real.sqrt (Real.cosh (2 * t))) := by
        ring
    _ = a ^ 3 / 2 *
        ∫ t in (0 : ℝ)..t₀,
          Real.sinh (2 * t) * Real.sqrt (Real.cosh (2 * t)) := by
      congr 1
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      change
        2 * (Real.cosh t * Real.sinh t * Real.sqrt (Real.cosh (2 * t))) =
          Real.sinh (2 * t) * Real.sqrt (Real.cosh (2 * t))
      rw [Real.sinh_two_mul]
      ring

theorem gap6 (a t₀ : ℝ) :
    a ^ 3 / 2 *
        (∫ t in (0 : ℝ)..t₀,
          Real.sinh (2 * t) * Real.sqrt (Real.cosh (2 * t))) =
      a ^ 3 / 4 *
        ∫ t in (0 : ℝ)..t₀,
          Real.sqrt (Real.cosh (2 * t)) * (2 * Real.sinh (2 * t)) := by
  calc
    a ^ 3 / 2 *
        (∫ t in (0 : ℝ)..t₀,
          Real.sinh (2 * t) * Real.sqrt (Real.cosh (2 * t))) =
      a ^ 3 / 4 *
        (2 * ∫ t in (0 : ℝ)..t₀,
          Real.sinh (2 * t) * Real.sqrt (Real.cosh (2 * t))) := by
        ring
    _ = a ^ 3 / 4 *
        ∫ t in (0 : ℝ)..t₀,
          Real.sqrt (Real.cosh (2 * t)) * (2 * Real.sinh (2 * t)) := by
      congr 1
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      ring

theorem gap7 (a t₀ : ℝ) (ht : 0 ≤ t₀) :
    a ^ 3 / 4 *
        (∫ t in (0 : ℝ)..t₀,
          Real.sqrt (Real.cosh (2 * t)) * (2 * Real.sinh (2 * t))) =
      a ^ 3 / 6 * (Real.sqrt (Real.cosh (2 * t₀) ^ 3) - 1) := by
  have hcube :
      Real.sqrt (Real.cosh (2 * t₀) ^ 3) =
        Real.cosh (2 * t₀) * Real.sqrt (Real.cosh (2 * t₀)) := by
    have hu : 0 ≤ Real.cosh (2 * t₀) :=
      le_of_lt (Real.cosh_pos (2 * t₀))
    calc
      Real.sqrt (Real.cosh (2 * t₀) ^ 3) =
          Real.sqrt
            (Real.cosh (2 * t₀) ^ 2 * Real.cosh (2 * t₀)) := by
        congr 1 <;> ring
      _ = Real.sqrt (Real.cosh (2 * t₀) ^ 2) *
          Real.sqrt (Real.cosh (2 * t₀)) := by
        rw [Real.sqrt_mul (sq_nonneg (Real.cosh (2 * t₀)))]
      _ = Real.cosh (2 * t₀) * Real.sqrt (Real.cosh (2 * t₀)) := by
        simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg hu]
  rw [integral_hyperbolic_sqrt t₀, ← hcube] <;> ring

theorem gap8 (a t₀ : ℝ) (ha : 0 < a) (ht : 0 ≤ t₀) :
    weightedLength a t₀ =
      a ^ 3 / 6 * (Real.sqrt (Real.cosh (2 * t₀) ^ 3) - 1) := by
  rw [gap4 a t₀ ha ht, gap5 a t₀, gap6 a t₀, gap7 a t₀ ht]

end

end ProofGap.Exercise4224

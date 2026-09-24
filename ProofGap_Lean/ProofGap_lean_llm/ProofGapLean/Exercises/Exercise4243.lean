import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise4243

noncomputable section

open scoped Interval

def height (a x : ℝ) : ℝ :=
  a * Real.cosh (x / a)

def endpointHeight (a b : ℝ) : ℝ :=
  height a b

def rawSpeed (a x : ℝ) : ℝ :=
  Real.sqrt (1 + Real.sinh (x / a) ^ 2)

def speed (a x : ℝ) : ℝ :=
  Real.cosh (x / a)

def mass (a b ρ₀ : ℝ) : ℝ :=
  ρ₀ * ∫ x in (0 : ℝ)..b, speed a x

def xCentroid (a b ρ₀ : ℝ) : ℝ :=
  ρ₀ / mass a b ρ₀ *
    ∫ x in (0 : ℝ)..b, x * speed a x

def yCentroid (a b ρ₀ : ℝ) : ℝ :=
  ρ₀ / mass a b ρ₀ *
    ∫ x in (0 : ℝ)..b, height a x * speed a x

def yMomentPrimitive (a ρ₀ M x : ℝ) : ℝ :=
  a * ρ₀ / M * (x / 2 + a / 4 * Real.sinh (2 * x / a))

private theorem integral_cosh_scaled (a b : ℝ) (ha : 0 < a) :
    (∫ x in (0 : ℝ)..b, Real.cosh (x / a)) =
      a * Real.sinh (b / a) := by
  have hderiv : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => a * Real.sinh (y / a))
        (Real.cosh (x / a)) x := by
    intro x
    convert ((Real.hasDerivAt_sinh (x / a)).comp x
      ((hasDerivAt_id x).div_const a)).const_mul a using 1 <;>
      field_simp [ha.ne'] <;> ring
  have hcont : Continuous (fun x : ℝ => Real.cosh (x / a)) :=
    Real.continuous_cosh.comp (continuous_id.div_const a)
  have hi :
      (∫ x in (0 : ℝ)..b, Real.cosh (x / a)) =
        (a * Real.sinh (b / a)) -
          (a * Real.sinh ((0 : ℝ) / a)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0 : ℝ)) (b := b)
      (fun x hx => hderiv x)
      (hcont.intervalIntegrable (μ := MeasureTheory.volume) (0 : ℝ) b)
  simpa using hi

private theorem integral_x_cosh_scaled (a b : ℝ) (ha : 0 < a) :
    (∫ x in (0 : ℝ)..b, x * Real.cosh (x / a)) =
      a * b * Real.sinh (b / a) -
        a ^ 2 * (Real.cosh (b / a) - 1) := by
  have hderiv : ∀ x : ℝ,
      HasDerivAt
        (fun y : ℝ =>
          a * y * Real.sinh (y / a) -
            a ^ 2 * (Real.cosh (y / a) - 1))
        (x * Real.cosh (x / a)) x := by
    intro x
    have hs := (Real.hasDerivAt_sinh (x / a)).comp x
      ((hasDerivAt_id x).div_const a)
    have hc := (Real.hasDerivAt_cosh (x / a)).comp x
      ((hasDerivAt_id x).div_const a)
    have hfirst :=
      (((hasDerivAt_const x a).mul (hasDerivAt_id x)).mul hs)
    have hsecond :=
      ((hasDerivAt_const x (a ^ 2)).mul (hc.sub_const 1))
    convert hfirst.sub hsecond using 1 <;>
      simp [Function.comp_apply] <;>
      field_simp [ha.ne'] <;> ring
  have hcont : Continuous (fun x : ℝ => x * Real.cosh (x / a)) :=
    continuous_id.mul
      (Real.continuous_cosh.comp (continuous_id.div_const a))
  have hi :
      (∫ x in (0 : ℝ)..b, x * Real.cosh (x / a)) =
        (a * b * Real.sinh (b / a) -
          a ^ 2 * (Real.cosh (b / a) - 1)) -
        (a * 0 * Real.sinh ((0 : ℝ) / a) -
          a ^ 2 * (Real.cosh ((0 : ℝ) / a) - 1)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0 : ℝ)) (b := b)
      (fun x hx => hderiv x)
      (hcont.intervalIntegrable (μ := MeasureTheory.volume) (0 : ℝ) b)
  simpa using hi

private theorem integral_cosh_double_scaled (a b : ℝ) (ha : 0 < a) :
    (∫ x in (0 : ℝ)..b, (1 + Real.cosh (2 * x / a)) / 2) =
      b / 2 + a / 4 * Real.sinh (2 * b / a) := by
  have hderiv : ∀ x : ℝ,
      HasDerivAt
        (fun y : ℝ => y / 2 + a / 4 * Real.sinh (2 * y / a))
        ((1 + Real.cosh (2 * x / a)) / 2) x := by
    intro x
    have hinner := ((hasDerivAt_id x).const_mul 2).div_const a
    have hs := (Real.hasDerivAt_sinh (2 * x / a)).comp x hinner
    have hd := (hasDerivAt_id x).div_const 2 |>.add
      (hs.const_mul (a / 4))
    convert hd using 1 <;> field_simp [ha.ne'] <;> ring
  have hcont : Continuous (fun x : ℝ =>
      (1 + Real.cosh (2 * x / a)) / 2) :=
    (continuous_const.add
      (Real.continuous_cosh.comp
        ((continuous_const.mul continuous_id).div_const a))).div_const 2
  have hi :
      (∫ x in (0 : ℝ)..b, (1 + Real.cosh (2 * x / a)) / 2) =
        (b / 2 + a / 4 * Real.sinh (2 * b / a)) -
          ((0 : ℝ) / 2 + a / 4 * Real.sinh (2 * 0 / a)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0 : ℝ)) (b := b)
      (fun x hx => hderiv x)
      (hcont.intervalIntegrable (μ := MeasureTheory.volume) (0 : ℝ) b)
  simpa using hi

theorem gap1 (a x : ℝ) (ha : 0 < a) :
    rawSpeed a x = Real.sqrt (1 + Real.sinh (x / a) ^ 2) := by
  rfl

theorem gap2 (a x : ℝ) (ha : 0 < a) :
    rawSpeed a x = speed a x := by
  unfold rawSpeed speed
  have hsq : 1 + Real.sinh (x / a) ^ 2 = Real.cosh (x / a) ^ 2 := by
    nlinarith [Real.cosh_sq_sub_sinh_sq (x / a)]
  rw [hsq, Real.sqrt_sq_eq_abs, abs_of_pos (Real.cosh_pos _)]

theorem gap3 (a x : ℝ) (ha : 0 < a) :
    rawSpeed a x = Real.cosh (x / a) := by
  exact gap2 a x ha

theorem gap4 (a b ρ₀ : ℝ) (ha : 0 < a) (hb : 0 < b) (hρ : 0 < ρ₀) :
    mass a b ρ₀ =
      ρ₀ * ∫ x in (0 : ℝ)..b, Real.cosh (x / a) := by
  rfl

theorem gap5 (a b ρ₀ : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ρ₀ * (∫ x in (0 : ℝ)..b, Real.cosh (x / a)) =
      a * ρ₀ * Real.sinh (b / a) := by
  rw [integral_cosh_scaled a b ha]
  ring

theorem gap6 (a b ρ₀ : ℝ) (ha : 0 < a) (hb : 0 ≤ b) :
    a * ρ₀ * Real.sinh (b / a) =
      ρ₀ * Real.sqrt (endpointHeight a b ^ 2 - a ^ 2) := by
  have ht : 0 ≤ b / a := div_nonneg hb ha.le
  have hs : 0 ≤ Real.sinh (b / a) := by
    rcases ht.eq_or_lt with hzero | hpos
    · rw [← hzero]
      simp
    · exact (Real.sinh_pos_iff.mpr hpos).le
  have hinside :
      endpointHeight a b ^ 2 - a ^ 2 =
        (a * Real.sinh (b / a)) ^ 2 := by
    unfold endpointHeight height
    nlinarith [Real.cosh_sq_sub_sinh_sq (b / a)]
  rw [hinside, Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg ha.le hs)]
  ring

theorem gap7 (a b ρ₀ : ℝ) (ha : 0 < a) (hb : 0 < b) (hρ : 0 < ρ₀) :
    mass a b ρ₀ =
      ρ₀ * Real.sqrt (endpointHeight a b ^ 2 - a ^ 2) := by
  calc
    mass a b ρ₀ =
        ρ₀ * ∫ x in (0 : ℝ)..b, Real.cosh (x / a) :=
      gap4 a b ρ₀ ha hb hρ
    _ = a * ρ₀ * Real.sinh (b / a) := gap5 a b ρ₀ ha hb
    _ = ρ₀ * Real.sqrt (endpointHeight a b ^ 2 - a ^ 2) :=
      gap6 a b ρ₀ ha hb.le

theorem gap8 (a b ρ₀ : ℝ) (ha : 0 < a) (hb : 0 < b) (hρ : 0 < ρ₀) :
    xCentroid a b ρ₀ =
      ρ₀ / mass a b ρ₀ *
        ∫ x in (0 : ℝ)..b, x * Real.cosh (x / a) := by
  rfl

theorem gap9 (a b ρ₀ : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ρ₀ / mass a b ρ₀ *
        (∫ x in (0 : ℝ)..b, x * Real.cosh (x / a)) =
      ρ₀ / mass a b ρ₀ *
        (a * b * Real.sinh (b / a) -
          a ^ 2 * (Real.cosh (b / a) - 1)) := by
  rw [integral_x_cosh_scaled a b ha]

theorem gap10 (a b ρ₀ : ℝ) (ha : 0 < a) (hb : 0 < b) (hρ : 0 < ρ₀) :
    xCentroid a b ρ₀ =
      ρ₀ / mass a b ρ₀ *
        (a * b * Real.sinh (b / a) -
          a ^ 2 * (Real.cosh (b / a) - 1)) := by
  calc
    xCentroid a b ρ₀ =
        ρ₀ / mass a b ρ₀ *
          ∫ x in (0 : ℝ)..b, x * Real.cosh (x / a) :=
      gap8 a b ρ₀ ha hb hρ
    _ = ρ₀ / mass a b ρ₀ *
          (a * b * Real.sinh (b / a) -
            a ^ 2 * (Real.cosh (b / a) - 1)) :=
      gap9 a b ρ₀ ha hb

theorem gap11 (a b ρ₀ : ℝ) (ha : 0 < a) (hb : 0 < b) (hρ : 0 < ρ₀) :
    xCentroid a b ρ₀ =
      1 / Real.sqrt (endpointHeight a b ^ 2 - a ^ 2) *
        (b * Real.sqrt (endpointHeight a b ^ 2 - a ^ 2) -
          a ^ 2 * (endpointHeight a b / a - 1)) := by
  have hs : 0 < Real.sinh (b / a) :=
    Real.sinh_pos_iff.mpr (div_pos hb ha)
  have hsqrt :
      Real.sqrt ((a * Real.cosh (b / a)) ^ 2 - a ^ 2) =
        a * Real.sinh (b / a) := by
    simpa [endpointHeight, height] using
      (gap6 a b 1 ha hb.le).symm
  rw [gap10 a b ρ₀ ha hb hρ, gap7 a b ρ₀ ha hb hρ]
  unfold endpointHeight height
  rw [hsqrt]
  field_simp [ha.ne', hρ.ne', hs.ne'] <;> ring

theorem gap12 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    1 / Real.sqrt (endpointHeight a b ^ 2 - a ^ 2) *
        (b * Real.sqrt (endpointHeight a b ^ 2 - a ^ 2) -
          a ^ 2 * (endpointHeight a b / a - 1)) =
      b - a *
        Real.sqrt
          ((endpointHeight a b - a) / (endpointHeight a b + a)) := by
  have hs : 0 < Real.sinh (b / a) :=
    Real.sinh_pos_iff.mpr (div_pos hb ha)
  have hid := Real.cosh_sq_sub_sinh_sq (b / a)
  have hc : 1 < Real.cosh (b / a) := by
    have hcp := Real.cosh_pos (b / a)
    nlinarith
  have hden : 0 < a * Real.cosh (b / a) + a := by
    have hp : 0 < a * Real.cosh (b / a) :=
      mul_pos ha (Real.cosh_pos _)
    linarith
  have hsqrt :
      Real.sqrt ((a * Real.cosh (b / a)) ^ 2 - a ^ 2) =
        a * Real.sinh (b / a) := by
    simpa [endpointHeight, height] using
      (gap6 a b 1 ha hb.le).symm
  have hratio :
      ((Real.cosh (b / a) - 1) / Real.sinh (b / a)) ^ 2 =
        (a * Real.cosh (b / a) - a) /
          (a * Real.cosh (b / a) + a) := by
    field_simp [ha.ne', hs.ne', hden.ne']
    nlinarith
  have hnum : 0 ≤ a * Real.cosh (b / a) - a := by
    have hp : 0 < a * (Real.cosh (b / a) - 1) :=
      mul_pos ha (sub_pos.mpr hc)
    nlinarith
  have hrad :
      0 ≤ (a * Real.cosh (b / a) - a) /
        (a * Real.cosh (b / a) + a) :=
    div_nonneg hnum hden.le
  have hquot :
      0 ≤ (Real.cosh (b / a) - 1) / Real.sinh (b / a) :=
    div_nonneg (sub_nonneg.mpr hc.le) hs.le
  have hroot :
      Real.sqrt
          ((a * Real.cosh (b / a) - a) /
            (a * Real.cosh (b / a) + a)) =
        (Real.cosh (b / a) - 1) / Real.sinh (b / a) := by
    have hr := Real.sqrt_nonneg
      ((a * Real.cosh (b / a) - a) /
        (a * Real.cosh (b / a) + a))
    have hrsq := Real.sq_sqrt hrad
    nlinarith
  unfold endpointHeight height
  rw [hsqrt, hroot]
  field_simp [ha.ne', hs.ne'] <;> ring

theorem gap13 (a b ρ₀ : ℝ) (ha : 0 < a) (hb : 0 < b) (hρ : 0 < ρ₀) :
    xCentroid a b ρ₀ =
      b - a *
        Real.sqrt
          ((endpointHeight a b - a) / (endpointHeight a b + a)) := by
  calc
    xCentroid a b ρ₀ =
        1 / Real.sqrt (endpointHeight a b ^ 2 - a ^ 2) *
          (b * Real.sqrt (endpointHeight a b ^ 2 - a ^ 2) -
            a ^ 2 * (endpointHeight a b / a - 1)) :=
      gap11 a b ρ₀ ha hb hρ
    _ = b - a *
          Real.sqrt
            ((endpointHeight a b - a) / (endpointHeight a b + a)) :=
      gap12 a b ha hb

theorem gap14 (a b ρ₀ : ℝ) (ha : 0 < a) (hb : 0 < b) (hρ : 0 < ρ₀) :
    yCentroid a b ρ₀ =
      ρ₀ / mass a b ρ₀ *
        ∫ x in (0 : ℝ)..b, height a x * Real.cosh (x / a) := by
  rfl

theorem gap15 (a b ρ₀ : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ρ₀ / mass a b ρ₀ *
        (∫ x in (0 : ℝ)..b, height a x * Real.cosh (x / a)) =
      a * ρ₀ / mass a b ρ₀ *
        ∫ x in (0 : ℝ)..b, Real.cosh (x / a) ^ 2 := by
  have hi :
      (∫ x in (0 : ℝ)..b, height a x * Real.cosh (x / a)) =
        a * ∫ x in (0 : ℝ)..b, Real.cosh (x / a) ^ 2 := by
    calc
      (∫ x in (0 : ℝ)..b, height a x * Real.cosh (x / a)) =
          ∫ x in (0 : ℝ)..b, a * Real.cosh (x / a) ^ 2 := by
        apply intervalIntegral.integral_congr
        intro x hx
        unfold height
        ring
      _ = a * ∫ x in (0 : ℝ)..b, Real.cosh (x / a) ^ 2 := by
        rw [intervalIntegral.integral_const_mul]
  rw [hi]
  ring

theorem gap16 (a b ρ₀ : ℝ) (ha : 0 < a) (hb : 0 < b) (hρ : 0 < ρ₀) :
    yCentroid a b ρ₀ =
      a * ρ₀ / mass a b ρ₀ *
        ∫ x in (0 : ℝ)..b, Real.cosh (x / a) ^ 2 := by
  calc
    yCentroid a b ρ₀ =
        ρ₀ / mass a b ρ₀ *
          ∫ x in (0 : ℝ)..b, height a x * Real.cosh (x / a) :=
      gap14 a b ρ₀ ha hb hρ
    _ = a * ρ₀ / mass a b ρ₀ *
          ∫ x in (0 : ℝ)..b, Real.cosh (x / a) ^ 2 :=
      gap15 a b ρ₀ ha hb

theorem gap17 (a b ρ₀ : ℝ) (ha : 0 < a) (hb : 0 < b) (hρ : 0 < ρ₀) :
    yCentroid a b ρ₀ =
      a * ρ₀ / mass a b ρ₀ *
        ∫ x in (0 : ℝ)..b, (1 + Real.cosh (2 * x / a)) / 2 := by
  have hi :
      (∫ x in (0 : ℝ)..b, Real.cosh (x / a) ^ 2) =
        ∫ x in (0 : ℝ)..b, (1 + Real.cosh (2 * x / a)) / 2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    change Real.cosh (x / a) ^ 2 =
      (1 + Real.cosh (2 * x / a)) / 2
    have harg : 2 * x / a = 2 * (x / a) := by
      ring
    rw [harg, Real.cosh_two_mul]
    nlinarith [Real.cosh_sq_sub_sinh_sq (x / a)]
  rw [gap16 a b ρ₀ ha hb hρ, hi]

theorem gap18 (a b ρ₀ : ℝ) (ha : 0 < a) (hb : 0 < b) (hρ : 0 < ρ₀) :
    a * ρ₀ / mass a b ρ₀ *
        (∫ x in (0 : ℝ)..b, (1 + Real.cosh (2 * x / a)) / 2) =
      yMomentPrimitive a ρ₀ (mass a b ρ₀) b -
        yMomentPrimitive a ρ₀ (mass a b ρ₀) 0 := by
  rw [integral_cosh_double_scaled a b ha]
  simp [yMomentPrimitive]

theorem gap19 (a b ρ₀ : ℝ) (ha : 0 < a) (hb : 0 < b) (hρ : 0 < ρ₀) :
    yCentroid a b ρ₀ =
      yMomentPrimitive a ρ₀ (mass a b ρ₀) b -
        yMomentPrimitive a ρ₀ (mass a b ρ₀) 0 := by
  calc
    yCentroid a b ρ₀ =
        a * ρ₀ / mass a b ρ₀ *
          ∫ x in (0 : ℝ)..b, (1 + Real.cosh (2 * x / a)) / 2 :=
      gap17 a b ρ₀ ha hb hρ
    _ = yMomentPrimitive a ρ₀ (mass a b ρ₀) b -
          yMomentPrimitive a ρ₀ (mass a b ρ₀) 0 :=
      gap18 a b ρ₀ ha hb hρ

theorem gap20 (a b ρ₀ : ℝ) (ha : 0 < a) (hb : 0 < b) (hρ : 0 < ρ₀) :
    yCentroid a b ρ₀ =
      a * ρ₀ / mass a b ρ₀ *
        (b / 2 + a / 4 * Real.sinh (2 * b / a)) := by
  rw [gap19 a b ρ₀ ha hb hρ]
  simp [yMomentPrimitive]

theorem gap21 (a b ρ₀ : ℝ) (ha : 0 < a) (hb : 0 < b) (hρ : 0 < ρ₀) :
    a * ρ₀ / mass a b ρ₀ *
        (b / 2 + a / 4 * Real.sinh (2 * b / a)) =
      a / Real.sqrt (endpointHeight a b ^ 2 - a ^ 2) *
        (b / 2 + endpointHeight a b / 2 *
          (Real.sqrt (endpointHeight a b ^ 2 - a ^ 2) / a)) := by
  have hs : 0 < Real.sinh (b / a) :=
    Real.sinh_pos_iff.mpr (div_pos hb ha)
  have hsqrt :
      Real.sqrt ((a * Real.cosh (b / a)) ^ 2 - a ^ 2) =
        a * Real.sinh (b / a) := by
    simpa [endpointHeight, height] using
      (gap6 a b 1 ha hb.le).symm
  have hdouble :
      Real.sinh (2 * b / a) =
        2 * Real.sinh (b / a) * Real.cosh (b / a) := by
    rw [show 2 * b / a = 2 * (b / a) by ring,
      Real.sinh_two_mul]
  rw [gap7 a b ρ₀ ha hb hρ]
  unfold endpointHeight height
  rw [hsqrt, hdouble]
  field_simp [ha.ne', hρ.ne', hs.ne'] <;> ring

theorem gap22 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a / Real.sqrt (endpointHeight a b ^ 2 - a ^ 2) *
        (b / 2 + endpointHeight a b / 2 *
          (Real.sqrt (endpointHeight a b ^ 2 - a ^ 2) / a)) =
      endpointHeight a b / 2 +
        a * b / (2 * Real.sqrt (endpointHeight a b ^ 2 - a ^ 2)) := by
  have hs : 0 < Real.sinh (b / a) :=
    Real.sinh_pos_iff.mpr (div_pos hb ha)
  have hsqrt :
      Real.sqrt ((a * Real.cosh (b / a)) ^ 2 - a ^ 2) =
        a * Real.sinh (b / a) := by
    simpa [endpointHeight, height] using
      (gap6 a b 1 ha hb.le).symm
  unfold endpointHeight height
  rw [hsqrt]
  field_simp [ha.ne', hs.ne'] <;> ring

theorem gap23 (a b ρ₀ : ℝ) (ha : 0 < a) (hb : 0 < b) (hρ : 0 < ρ₀) :
    yCentroid a b ρ₀ =
      endpointHeight a b / 2 +
        a * b / (2 * Real.sqrt (endpointHeight a b ^ 2 - a ^ 2)) := by
  calc
    yCentroid a b ρ₀ =
        a * ρ₀ / mass a b ρ₀ *
          (b / 2 + a / 4 * Real.sinh (2 * b / a)) :=
      gap20 a b ρ₀ ha hb hρ
    _ = a / Real.sqrt (endpointHeight a b ^ 2 - a ^ 2) *
          (b / 2 + endpointHeight a b / 2 *
            (Real.sqrt (endpointHeight a b ^ 2 - a ^ 2) / a)) :=
      gap21 a b ρ₀ ha hb hρ
    _ = endpointHeight a b / 2 +
          a * b / (2 * Real.sqrt (endpointHeight a b ^ 2 - a ^ 2)) :=
      gap22 a b ha hb

end

end ProofGap.Exercise4243

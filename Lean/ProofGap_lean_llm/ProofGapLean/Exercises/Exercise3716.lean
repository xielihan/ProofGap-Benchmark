import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3716

noncomputable section

open scoped Interval

def integrand (x y : ℝ) : ℝ :=
  Real.log (Real.sqrt (x ^ 2 + y ^ 2))

def integralFunction (y : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, integrand x y

def closedForm (y : ℝ) : ℝ :=
  Real.log (Real.sqrt (1 + y ^ 2)) - 1 +
    y * Real.arctan (1 / y)

def differenceQuotient (y : ℝ) : ℝ :=
  (integralFunction y - integralFunction 0) / y

def modelQuotient (y : ℝ) : ℝ :=
  Real.log (1 + y ^ 2) / (2 * y) + Real.arctan (1 / y)

private lemma hasDerivAt_logSqrt_sq_add_sq (c x : ℝ) (hc : c ≠ 0) :
    HasDerivAt
      (fun z : ℝ => Real.log (Real.sqrt (z ^ 2 + c ^ 2)))
      (x / (x ^ 2 + c ^ 2)) x := by
  have hcpos : 0 < c ^ 2 := sq_pos_of_ne_zero hc
  have hsum : 0 < x ^ 2 + c ^ 2 := by nlinarith [sq_nonneg x]
  have hq : HasDerivAt (fun z : ℝ => z ^ 2 + c ^ 2) (2 * x) x := by
    convert (hasDerivAt_pow 2 x).add_const (c ^ 2) using 1 <;> norm_num
  have hlog :=
    (Real.hasDerivAt_log hsum.ne').comp
      x hq
  have hhalf := hlog.const_mul (1 / 2)
  have heq :
      (fun z : ℝ => Real.log (Real.sqrt (z ^ 2 + c ^ 2))) =
        fun z : ℝ => (1 / 2) * Real.log (z ^ 2 + c ^ 2) := by
    funext z
    rw [Real.log_sqrt (by positivity)]
    ring
  rw [heq]
  convert hhalf using 1 <;> simp [Function.comp_def]
  field_simp

private lemma integralFunction_integrationByParts (y : ℝ) (hy : y ≠ 0) :
    integralFunction y =
      Real.log (Real.sqrt (1 + y ^ 2)) -
        ∫ x in (0 : ℝ)..1, x ^ 2 / (x ^ 2 + y ^ 2) := by
  have hden : ∀ x : ℝ, x ^ 2 + y ^ 2 ≠ 0 := by
    intro x
    nlinarith [sq_nonneg x, sq_pos_of_ne_zero hy]
  have hparts :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (a := (0 : ℝ)) (b := 1)
      (u := fun x : ℝ => x) (u' := fun _ : ℝ => 1)
      (v := fun x : ℝ => Real.log (Real.sqrt (x ^ 2 + y ^ 2)))
      (v' := fun x : ℝ => x / (x ^ 2 + y ^ 2))
      (fun x _ => hasDerivAt_id x)
      (fun x _ => hasDerivAt_logSqrt_sq_add_sq y x hy)
      (intervalIntegrable_const)
      ((continuous_id.div
        ((continuous_id.pow 2).add continuous_const)
        hden).intervalIntegrable (0 : ℝ) 1)
  unfold integralFunction integrand
  have hleft :
      (∫ x in (0 : ℝ)..1, x * (x / (x ^ 2 + y ^ 2))) =
        ∫ x in (0 : ℝ)..1, x ^ 2 / (x ^ 2 + y ^ 2) := by
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [hleft] at hparts
  simp at hparts
  linarith

private lemma integral_y_sq_div_sq_add_sq (y : ℝ) :
    (∫ x in (0 : ℝ)..1, y ^ 2 / (x ^ 2 + y ^ 2)) =
      y * Real.arctan (1 / y) := by
  calc
    (∫ x in (0 : ℝ)..1, y ^ 2 / (x ^ 2 + y ^ 2)) =
        ∫ x in (0 : ℝ)..1, y * (y / (y ^ 2 + x ^ 2)) := by
          apply intervalIntegral.integral_congr
          intro x _
          ring
    _ = y * ∫ x in (0 : ℝ)..1, y / (y ^ 2 + x ^ 2) := by
      rw [intervalIntegral.integral_const_mul]
    _ = y * Real.arctan (1 / y) := by
      rw [integral_div_sq_add_sq]
      simp

private lemma modelFirstTerm_tendsto_zero :
    Filter.Tendsto
      (fun y : ℝ => Real.log (1 + y ^ 2) / (2 * y))
      (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhds 0) := by
  have hinner : HasDerivAt (fun y : ℝ => 1 + y ^ 2) 0 0 := by
    convert (hasDerivAt_pow 2 (0 : ℝ)).const_add 1 using 1 <;> norm_num
  have hlog :
      HasDerivAt (fun y : ℝ => Real.log (1 + y ^ 2)) 0 0 := by
    have hc :=
      (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)).comp_of_eq
        0 hinner (by norm_num : (1 : ℝ) = 1 + 0 ^ 2)
    simpa [Function.comp_def] using hc
  have hslope := hlog.tendsto_slope_zero
  have hhalf := hslope.div_const 2
  have hhalf' :
      Filter.Tendsto
        (fun a : ℝ =>
          a⁻¹ • (Real.log (1 + (0 + a) ^ 2) - Real.log (1 + 0 ^ 2)) / 2)
        (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhds 0) := by
    simpa using hhalf
  apply hhalf'.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hy0 : y ≠ 0 := by simpa using hy
  norm_num [smul_eq_mul]
  field_simp [hy0]

private lemma modelFirstTerm_tendsto_zero_right :
    Filter.Tendsto
      (fun y : ℝ => Real.log (1 + y ^ 2) / (2 * y))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
  modelFirstTerm_tendsto_zero.mono_left (nhdsGT_le_nhdsNE 0)

private lemma modelFirstTerm_tendsto_zero_left :
    Filter.Tendsto
      (fun y : ℝ => Real.log (1 + y ^ 2) / (2 * y))
      (nhdsWithin 0 (Set.Iio 0)) (nhds 0) :=
  modelFirstTerm_tendsto_zero.mono_left (nhdsLT_le_nhdsNE 0)

theorem gap1 (y : ℝ) (hy : y ≠ 0) :
    integralFunction y =
      ∫ x in (0 : ℝ)..1, Real.log (Real.sqrt (x ^ 2 + y ^ 2)) := by
  rfl

theorem gap2 (y : ℝ) (hy : y ≠ 0) :
    integralFunction y =
      Real.log (Real.sqrt (1 + y ^ 2)) -
        ∫ x in (0 : ℝ)..1, x ^ 2 / (x ^ 2 + y ^ 2) :=
  integralFunction_integrationByParts y hy

theorem gap3 (y : ℝ) (hy : y ≠ 0) :
    integralFunction y =
      Real.log (Real.sqrt (1 + y ^ 2)) -
        ∫ x in (0 : ℝ)..1, x ^ 2 / (x ^ 2 + y ^ 2) :=
  gap2 y hy

theorem gap4 (y : ℝ) (hy : y ≠ 0) :
    integralFunction y =
      Real.log (Real.sqrt (1 + y ^ 2)) -
        ∫ x in (0 : ℝ)..1, (1 - y ^ 2 / (x ^ 2 + y ^ 2)) := by
  rw [gap3 y hy]
  have hint :
      (∫ x in (0 : ℝ)..1, x ^ 2 / (x ^ 2 + y ^ 2)) =
        ∫ x in (0 : ℝ)..1, (1 - y ^ 2 / (x ^ 2 + y ^ 2)) := by
    apply intervalIntegral.integral_congr
    intro x _
    have hden : x ^ 2 + y ^ 2 ≠ 0 := by
      nlinarith [sq_nonneg x, sq_pos_of_ne_zero hy]
    field_simp
    ring
  rw [hint]

theorem gap5 (y : ℝ) (hy : y ≠ 0) :
    Real.log (Real.sqrt (1 + y ^ 2)) -
        (∫ x in (0 : ℝ)..1, (1 - y ^ 2 / (x ^ 2 + y ^ 2))) =
      closedForm y := by
  have hcont :
      Continuous (fun x : ℝ => y ^ 2 / (x ^ 2 + y ^ 2)) := by
    have hden : ∀ x : ℝ, x ^ 2 + y ^ 2 ≠ 0 := by
      intro x
      nlinarith [sq_nonneg x, sq_pos_of_ne_zero hy]
    apply continuous_const.div
      ((continuous_id.pow 2).add continuous_const)
    exact hden
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    (hcont.intervalIntegrable (0 : ℝ) 1)]
  rw [integral_one, integral_y_sq_div_sq_add_sq]
  simp [closedForm]
  ring

theorem gap6 (y : ℝ) (hy : y ≠ 0) :
    integralFunction y = closedForm y := by
  rw [gap4 y hy, gap5 y hy]

theorem gap7 :
    integralFunction 0 = ∫ x in (0 : ℝ)..1, Real.log x := by
  unfold integralFunction integrand
  apply intervalIntegral.integral_congr
  intro x hx
  have hx0 : 0 ≤ x := by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    exact hx.1
  simp [Real.sqrt_sq_eq_abs, abs_of_nonneg hx0]

theorem gap8 :
    (∫ x in (0 : ℝ)..1, Real.log x) =
      0 - ∫ x in (0 : ℝ)..1, (1 : ℝ) := by
  rw [integral_log]
  norm_num

theorem gap9 :
    0 - (∫ x in (0 : ℝ)..1, (1 : ℝ)) = -1 := by
  rw [integral_one]
  norm_num

theorem gap10 :
    integralFunction 0 = -1 := by
  rw [gap7, gap8, gap9]

theorem gap11 (y : ℝ) (hy : 0 < y) :
    differenceQuotient y = modelQuotient y := by
  rw [differenceQuotient, gap10, gap6 y hy.ne', modelQuotient, closedForm]
  rw [Real.log_sqrt (by positivity : 0 ≤ 1 + y ^ 2)]
  field_simp
  ring

theorem gap12 :
    Filter.Tendsto modelQuotient (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Real.pi / 2)) := by
  have hatan :
      Filter.Tendsto (fun y : ℝ => Real.arctan (1 / y))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.pi / 2)) := by
    simpa [one_div] using
      (tendsto_nhds_of_tendsto_nhdsWithin
        (Real.tendsto_arctan_atTop.comp tendsto_inv_nhdsGT_zero))
  change Filter.Tendsto
    (fun y : ℝ =>
      Real.log (1 + y ^ 2) / (2 * y) + Real.arctan (1 / y))
    (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.pi / 2))
  simpa only [zero_add] using modelFirstTerm_tendsto_zero_right.add hatan

theorem gap13 :
    Filter.Tendsto differenceQuotient (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Real.pi / 2)) := by
  apply gap12.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (gap11 y hy).symm

theorem gap14 (y : ℝ) (hy : y < 0) :
    differenceQuotient y = modelQuotient y := by
  rw [differenceQuotient, gap10, gap6 y hy.ne, modelQuotient, closedForm]
  rw [Real.log_sqrt (by positivity : 0 ≤ 1 + y ^ 2)]
  field_simp [hy.ne]
  ring

theorem gap15 :
    Filter.Tendsto modelQuotient (nhdsWithin 0 (Set.Iio 0))
      (nhds (-Real.pi / 2)) := by
  have hatan :
      Filter.Tendsto (fun y : ℝ => Real.arctan (1 / y))
        (nhdsWithin 0 (Set.Iio 0)) (nhds (-Real.pi / 2)) := by
    convert
      (tendsto_nhds_of_tendsto_nhdsWithin
        (Real.tendsto_arctan_atBot.comp tendsto_inv_nhdsLT_zero))
      using 1 <;> simp [Function.comp_def, one_div] <;> ring
  change Filter.Tendsto
    (fun y : ℝ =>
      Real.log (1 + y ^ 2) / (2 * y) + Real.arctan (1 / y))
    (nhdsWithin 0 (Set.Iio 0)) (nhds (-Real.pi / 2))
  simpa only [zero_add] using modelFirstTerm_tendsto_zero_left.add hatan

theorem gap16 :
    Filter.Tendsto differenceQuotient (nhdsWithin 0 (Set.Iio 0))
      (nhds (-Real.pi / 2)) := by
  apply gap15.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (gap14 y hy).symm

theorem gap17 :
    ¬ DifferentiableAt ℝ integralFunction 0 := by
  intro hdiff
  have hderiv := hdiff.hasDerivAt
  have hright :
      Filter.Tendsto differenceQuotient (nhdsWithin 0 (Set.Ioi 0))
        (nhds (deriv integralFunction 0)) := by
    have hs := hderiv.tendsto_slope_zero_right
    apply hs.congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy0 : y ≠ 0 := hy.ne'
    simp only [zero_add, differenceQuotient, smul_eq_mul]
    rw [div_eq_mul_inv, mul_comm]
  have hleft :
      Filter.Tendsto differenceQuotient (nhdsWithin 0 (Set.Iio 0))
        (nhds (deriv integralFunction 0)) := by
    have hs := hderiv.tendsto_slope_zero_left
    apply hs.congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy0 : y ≠ 0 := hy.ne
    simp only [zero_add, differenceQuotient, smul_eq_mul]
    rw [div_eq_mul_inv, mul_comm]
  have h₁ : deriv integralFunction 0 = Real.pi / 2 :=
    tendsto_nhds_unique hright gap13
  have h₂ : deriv integralFunction 0 = -Real.pi / 2 :=
    tendsto_nhds_unique hleft gap16
  nlinarith [Real.pi_pos]

theorem gap18 (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y => integrand x y) 0 0 := by
  simpa [integrand, add_comm] using
    (hasDerivAt_logSqrt_sq_add_sq x 0 hx.ne')

theorem gap19 :
    (∫ _x in (0 : ℝ)..1, (0 : ℝ)) = 0 := by
  simp

theorem gap20 :
    Real.pi / 2 ≠ 0 := by
  positivity

theorem gap21 :
    -Real.pi / 2 ≠ 0 := by
  intro h
  apply gap20
  linarith

end

end ProofGap.Exercise3716

import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise2437
noncomputable section

open scoped Interval

def s (a : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..a, Real.sqrt (1 + Real.tan x ^ 2)

theorem gap1 (a : ℝ) :
    s a = ∫ x in (0 : ℝ)..a, Real.sqrt (1 + Real.tan x ^ 2) := by
  rfl

theorem gap2 (a : ℝ) (ha₀ : 0 ≤ a) (ha₁ : a < Real.pi / 2) :
    (∫ x in (0 : ℝ)..a, Real.sqrt (1 + Real.tan x ^ 2)) =
      ∫ x in (0 : ℝ)..a, 1 / Real.cos x := by
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x ∈ Set.Icc (0 : ℝ) a := by
    simpa [Set.uIcc_of_le ha₀] using hx
  have hxcos : 0 < Real.cos x := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · nlinarith [hx'.1, Real.pi_pos]
    · exact lt_of_le_of_lt hx'.2 ha₁
  have hsq : 1 + Real.tan x ^ 2 = (1 / Real.cos x) ^ 2 := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp [ne_of_gt hxcos]
    nlinarith [Real.sin_sq_add_cos_sq x]
  calc
    Real.sqrt (1 + Real.tan x ^ 2) = Real.sqrt ((1 / Real.cos x) ^ 2) := by rw [hsq]
    _ = |1 / Real.cos x| := Real.sqrt_sq_eq_abs _
    _ = 1 / Real.cos x := abs_of_pos (one_div_pos.mpr hxcos)

theorem gap3 (a : ℝ) (ha₀ : 0 ≤ a) (ha₁ : a < Real.pi / 2) :
    (∫ x in (0 : ℝ)..a, 1 / Real.cos x) =
      Real.log (Real.tan (Real.pi / 4 + a / 2)) := by
  let F : ℝ → ℝ := fun x =>
    Real.log (Real.tan (Real.pi / 4 + x / 2))
  have hcont : ContinuousOn (fun x : ℝ => 1 / Real.cos x) (Set.uIcc 0 a) := by
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) a := by
      simpa [Set.uIcc_of_le ha₀] using hx
    have hxcos : 0 < Real.cos x := by
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · nlinarith [hx'.1, Real.pi_pos]
      · exact lt_of_le_of_lt hx'.2 ha₁
    exact
      (continuousAt_const.div Real.continuous_cos.continuousAt
        (ne_of_gt hxcos)).continuousWithinAt
  have hderiv :
      ∀ x ∈ Set.uIcc (0 : ℝ) a,
        HasDerivAt F (1 / Real.cos x) x := by
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) a := by
      simpa [Set.uIcc_of_le ha₀] using hx
    have hxcos : 0 < Real.cos x := by
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · nlinarith [hx'.1, Real.pi_pos]
      · exact lt_of_le_of_lt hx'.2 ha₁
    let y : ℝ := Real.pi / 4 + x / 2
    have hypos : 0 < y := by
      dsimp [y]
      nlinarith [hx'.1, Real.pi_pos]
    have hyupper : y < Real.pi / 2 := by
      dsimp [y]
      nlinarith [hx'.2, ha₁]
    have hycos : 0 < Real.cos y := by
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · nlinarith [Real.pi_pos, hypos]
      · exact hyupper
    have hysin : 0 < Real.sin y := by
      apply Real.sin_pos_of_pos_of_lt_pi hypos
      nlinarith [Real.pi_pos, hyupper]
    have hytan : 0 < Real.tan y := by
      rw [Real.tan_eq_sin_div_cos]
      exact div_pos hysin hycos
    have hangle : 2 * y = Real.pi / 2 + x := by
      dsimp [y]
      ring
    have hdouble : 2 * Real.sin y * Real.cos y = Real.cos x := by
      calc
        2 * Real.sin y * Real.cos y = Real.sin (2 * y) := by
          rw [Real.sin_two_mul]
        _ = Real.sin (Real.pi / 2 + x) := by rw [hangle]
        _ = Real.cos x := by
          rw [Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two]
          ring
    have hinner :
        HasDerivAt (fun z : ℝ => Real.pi / 4 + z / 2) (1 / 2) x := by
      simpa only [zero_add] using
        (hasDerivAt_const x (Real.pi / 4)).add
          ((hasDerivAt_id x).div_const 2)
    have htan :
        HasDerivAt (fun z : ℝ => Real.tan (Real.pi / 4 + z / 2))
          ((1 / Real.cos y ^ 2) * (1 / 2)) x := by
      simpa [y] using
        (Real.hasDerivAt_tan (ne_of_gt hycos)).comp x hinner
    have hcomp :
        HasDerivAt F
          ((Real.tan y)⁻¹ * ((1 / Real.cos y ^ 2) * (1 / 2))) x := by
      simpa [F, y] using
        (Real.hasDerivAt_log (ne_of_gt hytan)).comp x htan
    have hcoef :
        (Real.tan y)⁻¹ * ((1 / Real.cos y ^ 2) * (1 / 2)) =
          1 / Real.cos x := by
      calc
        (Real.tan y)⁻¹ * ((1 / Real.cos y ^ 2) * (1 / 2)) =
            1 / (2 * Real.sin y * Real.cos y) := by
          rw [Real.tan_eq_sin_div_cos]
          field_simp [ne_of_gt hysin, ne_of_gt hycos]
          <;> ring
        _ = 1 / Real.cos x := by rw [hdouble]
    rw [hcoef] at hcomp
    exact hcomp
  calc
    (∫ x in (0 : ℝ)..a, 1 / Real.cos x) = F a - F 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
        hcont.intervalIntegrable
    _ = Real.log (Real.tan (Real.pi / 4 + a / 2)) := by
      simp [F, Real.tan_pi_div_four]

theorem gap4 (a : ℝ) (ha₀ : 0 ≤ a) (ha₁ : a < Real.pi / 2) :
    s a = Real.log (Real.tan (Real.pi / 4 + a / 2)) := by
  calc
    s a = ∫ x in (0 : ℝ)..a, Real.sqrt (1 + Real.tan x ^ 2) := gap1 a
    _ = ∫ x in (0 : ℝ)..a, 1 / Real.cos x := gap2 a ha₀ ha₁
    _ = Real.log (Real.tan (Real.pi / 4 + a / 2)) := gap3 a ha₀ ha₁

end
end ProofGap.Exercise2437

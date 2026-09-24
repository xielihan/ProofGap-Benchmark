import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise2401
noncomputable section

open scoped Interval

def antiderivative (x : ℝ) : ℝ :=
  x / 2 - (1 / 4 : ℝ) * Real.sin (2 * x)

theorem gap1 :
    (∫ x in (0 : ℝ)..Real.pi, x + Real.sin x ^ 2 - x) =
      antiderivative Real.pi - antiderivative 0 := by
  have hderiv : ∀ x : ℝ, HasDerivAt antiderivative (Real.sin x ^ 2) x := by
    intro x
    have hlin : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
      simpa using (hasDerivAt_id x).const_mul 2
    have hsin : HasDerivAt (fun y : ℝ => Real.sin (2 * y))
        (2 * Real.cos (2 * x)) x := by
      convert (Real.hasDerivAt_sin (2 * x)).comp x hlin using 1 <;> ring
    unfold antiderivative
    convert ((hasDerivAt_id x).div_const 2).sub
      (hsin.const_mul (1 / 4 : ℝ)) using 1
    rw [Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hint : IntervalIntegrable (fun x : ℝ => Real.sin x ^ 2)
      MeasureTheory.volume 0 Real.pi :=
    (Real.continuous_sin.pow 2).intervalIntegrable 0 Real.pi
  have hFTC :
      (∫ x in (0 : ℝ)..Real.pi, Real.sin x ^ 2) =
        antiderivative Real.pi - antiderivative 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0 : ℝ)) (b := Real.pi) (fun x _ => hderiv x) hint
  simpa only [add_sub_cancel_left] using hFTC

theorem gap2 :
    antiderivative Real.pi - antiderivative 0 = Real.pi / 2 := by
  unfold antiderivative
  rw [show (2 : ℝ) * Real.pi = Real.pi + Real.pi by ring]
  simp [Real.sin_add]

theorem gap3 :
    (∫ x in (0 : ℝ)..Real.pi, x + Real.sin x ^ 2 - x) =
      Real.pi / 2 := by
  calc
    (∫ x in (0 : ℝ)..Real.pi, x + Real.sin x ^ 2 - x) =
        antiderivative Real.pi - antiderivative 0 := gap1
    _ = Real.pi / 2 := gap2

end
end ProofGap.Exercise2401

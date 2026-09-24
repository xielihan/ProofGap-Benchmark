import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3719

noncomputable section

open scoped Interval

def integralFunction (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..x, (x + y) * f y

def firstDerivative (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  2 * x * f x + ∫ y in (0 : ℝ)..x, f y

def expandedSecondDerivative (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  2 * f x + 2 * x * deriv f x + f x

def closedSecondDerivative (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  3 * f x + 2 * x * deriv f x

theorem gap1 (f : ℝ → ℝ) (hf : Differentiable ℝ f) :
    ∀ x : ℝ, deriv (integralFunction f) x = firstDerivative f x := by
  intro x
  have hcont : Continuous f := hf.continuous
  have hfun :
      integralFunction f =
        fun t =>
          t * (∫ y in (0 : ℝ)..t, f y) +
            ∫ y in (0 : ℝ)..t, y * f y := by
    funext t
    have htf_cont : Continuous (fun y : ℝ => t * f y) :=
      continuous_const.mul hcont
    have hyf_cont : Continuous (fun y : ℝ => y * f y) :=
      continuous_id.mul hcont
    have htf_int :
        IntervalIntegrable (fun y : ℝ => t * f y) MeasureTheory.volume 0 t :=
      htf_cont.intervalIntegrable 0 t
    have hyf_int :
        IntervalIntegrable (fun y : ℝ => y * f y) MeasureTheory.volume 0 t :=
      hyf_cont.intervalIntegrable 0 t
    unfold integralFunction
    calc
      (∫ y in (0 : ℝ)..t, (t + y) * f y) =
          ∫ y in (0 : ℝ)..t, t * f y + y * f y := by
            apply intervalIntegral.integral_congr
            intro y hy
            ring
      _ = (∫ y in (0 : ℝ)..t, t * f y) +
            ∫ y in (0 : ℝ)..t, y * f y :=
          intervalIntegral.integral_add htf_int hyf_int
      _ = t * (∫ y in (0 : ℝ)..t, f y) +
            ∫ y in (0 : ℝ)..t, y * f y := by
          rw [intervalIntegral.integral_const_mul]
  rw [hfun]
  have hF :
      HasDerivAt (fun t : ℝ => ∫ y in (0 : ℝ)..t, f y) (f x) x :=
    intervalIntegral.integral_hasDerivAt_right
      (hcont.intervalIntegrable 0 x)
      hcont.stronglyMeasurable.stronglyMeasurableAtFilter
      (hf x).continuousAt
  have hyf_cont : Continuous (fun y : ℝ => y * f y) :=
    continuous_id.mul hcont
  have hG :
      HasDerivAt (fun t : ℝ => ∫ y in (0 : ℝ)..t, y * f y) (x * f x) x :=
    intervalIntegral.integral_hasDerivAt_right
      (hyf_cont.intervalIntegrable 0 x)
      hyf_cont.stronglyMeasurable.stronglyMeasurableAtFilter
      (continuousAt_id.mul (hf x).continuousAt)
  unfold firstDerivative
  convert ((((hasDerivAt_id x).mul hF).add hG).deriv) using 1 <;>
    simp [id] <;> ring

theorem gap2 (f : ℝ → ℝ) (hf : Differentiable ℝ f) :
    ∀ x : ℝ,
      deriv (deriv (integralFunction f)) x =
        expandedSecondDerivative f x := by
  intro x
  have hcont : Continuous f := hf.continuous
  have hderiv : deriv (integralFunction f) = firstDerivative f :=
    funext (gap1 f hf)
  rw [hderiv]
  have hF :
      HasDerivAt (fun t : ℝ => ∫ y in (0 : ℝ)..t, f y) (f x) x :=
    intervalIntegral.integral_hasDerivAt_right
      (hcont.intervalIntegrable 0 x)
      hcont.stronglyMeasurable.stronglyMeasurableAtFilter
      (hf x).continuousAt
  have hmain :
      HasDerivAt (fun t : ℝ => 2 * t * f t)
        (2 * f x + 2 * x * deriv f x) x := by
    convert (((hasDerivAt_id x).const_mul 2).mul (hf x).hasDerivAt) using 1 <;>
      simp [id] <;> ring
  simpa [firstDerivative, expandedSecondDerivative] using (hmain.add hF).deriv

theorem gap3 (f : ℝ → ℝ) :
    ∀ x : ℝ,
      expandedSecondDerivative f x = closedSecondDerivative f x := by
  intro x
  unfold expandedSecondDerivative closedSecondDerivative
  ring

theorem gap4 (f : ℝ → ℝ) (hf : Differentiable ℝ f) :
    ∀ x : ℝ,
      deriv (deriv (integralFunction f)) x =
        closedSecondDerivative f x := by
  intro x
  calc
    deriv (deriv (integralFunction f)) x = expandedSecondDerivative f x :=
      gap2 f hf x
    _ = closedSecondDerivative f x := gap3 f x

end

end ProofGap.Exercise3719

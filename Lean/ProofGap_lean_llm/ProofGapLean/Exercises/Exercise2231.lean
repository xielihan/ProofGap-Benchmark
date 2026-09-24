import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Defs.Filter

open scoped Interval

namespace ProofGap.Exercise2231

noncomputable section

def integral (a b : ℝ) : ℝ :=
  ∫ t in a..b, Real.sin (t ^ 2)

private theorem integral_endpoint_derivs (x c : ℝ) :
    deriv (fun u : ℝ => integral u c) x = -Real.sin (x ^ 2) ∧
      deriv (fun u : ℝ => integral c u) x = Real.sin (x ^ 2) := by
  have hcontinuous : Continuous (fun t : ℝ => Real.sin (t ^ 2)) :=
    Real.continuous_sin.comp (continuous_id.pow 2)
  have hint_left : IntervalIntegrable (fun t : ℝ => Real.sin (t ^ 2))
      MeasureTheory.volume x c :=
    hcontinuous.continuousOn.intervalIntegrable
  have hint_right : IntervalIntegrable (fun t : ℝ => Real.sin (t ^ 2))
      MeasureTheory.volume c x :=
    hcontinuous.continuousOn.intervalIntegrable
  have hmeas (z : ℝ) :
      StronglyMeasurableAtFilter (fun t : ℝ => Real.sin (t ^ 2))
        (nhds z) MeasureTheory.volume :=
    hcontinuous.stronglyMeasurable.stronglyMeasurableAtFilter
  constructor
  · unfold integral
    exact (intervalIntegral.integral_hasDerivAt_left hint_left
      (hmeas x) hcontinuous.continuousAt).deriv
  · unfold integral
    exact (intervalIntegral.integral_hasDerivAt_right hint_right
      (hmeas x) hcontinuous.continuousAt).deriv

theorem gap1 (a b x : ℝ) :
    deriv (fun _ : ℝ => integral a b) x = 0 := by
  simpa using (hasDerivAt_const (x := x) (c := integral a b)).deriv

theorem gap2 (a b : ℝ) :
    deriv (fun u : ℝ => integral u b) a =
      -deriv (fun u : ℝ => integral b u) a := by
  rw [(integral_endpoint_derivs a b).1,
    (integral_endpoint_derivs a b).2]

theorem gap3 (a b : ℝ) :
    -deriv (fun u : ℝ => integral b u) a =
      -Real.sin (a ^ 2) := by
  rw [(integral_endpoint_derivs a b).2]

theorem gap4 (a b : ℝ) :
    deriv (fun u : ℝ => integral u b) a =
      -Real.sin (a ^ 2) := by
  calc
    deriv (fun u : ℝ => integral u b) a =
        -deriv (fun u : ℝ => integral b u) a := gap2 a b
    _ = -Real.sin (a ^ 2) := gap3 a b

theorem gap5 (a b : ℝ) :
    deriv (fun u : ℝ => integral a u) b =
      Real.sin (b ^ 2) := by
  exact (integral_endpoint_derivs b a).2

end

end ProofGap.Exercise2231

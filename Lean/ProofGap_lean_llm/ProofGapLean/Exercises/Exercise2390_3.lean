import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise2390_3
noncomputable section

open Filter
open scoped Interval

def symmetricIntegral (b : ℝ) : ℝ :=
  ∫ x in (-b)..b, Real.sin x

theorem gap1 (b : ℝ) :
    symmetricIntegral b = -Real.cos b + Real.cos b := by
  unfold symmetricIntegral
  calc
    (∫ x in (-b)..b, Real.sin x) =
        (-Real.cos b) - (-Real.cos (-b)) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro x hx
        simpa only [neg_neg] using (Real.hasDerivAt_cos x).neg
      · exact Real.continuous_sin.intervalIntegrable _ _
    _ = -Real.cos b + Real.cos b := by
      simp [Real.cos_neg]

theorem gap2 (b : ℝ) :
    -Real.cos b + Real.cos b = 0 := by
  simp

theorem gap3 (b : ℝ) :
    symmetricIntegral b = 0 := by
  calc
    symmetricIntegral b = -Real.cos b + Real.cos b := gap1 b
    _ = 0 := gap2 b

theorem gap4 :
    Tendsto symmetricIntegral atTop (nhds 0) := by
  have hs : symmetricIntegral = fun _ : ℝ => 0 := by
    funext b
    exact gap3 b
  rw [hs]
  exact tendsto_const_nhds

end
end ProofGap.Exercise2390_3

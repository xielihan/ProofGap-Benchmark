import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open scoped Interval

namespace ProofGap.Exercise2468

noncomputable section

def ellipseArea (a z : ℝ) : ℝ := Real.pi * a * z

def volume (a : ℝ) : ℝ := ∫ z in 0..a, ellipseArea a z

theorem gap1 (a z : ℝ) :
    ellipseArea a z = Real.pi * a * z := by
  rfl

theorem gap2 (a V : ℝ) (hV : V = volume a) :
    V = ∫ z in 0..a, ellipseArea a z := by
  simpa [volume] using hV

theorem gap3 (a V : ℝ) (hV : V = volume a) :
    V = Real.pi * a * ∫ z in 0..a, z := by
  calc
    V = ∫ z in 0..a, ellipseArea a z := gap2 a V hV
    _ = Real.pi * a * ∫ z in 0..a, z := by
      simp only [ellipseArea]
      rw [intervalIntegral.integral_const_mul]

theorem gap4 (a : ℝ) :
    Real.pi * a * (∫ z in 0..a, z) = Real.pi * a ^ 3 / 2 := by
  rw [integral_id]
  ring

theorem gap5 (a V : ℝ) (hV : V = volume a) :
    V = Real.pi * a ^ 3 / 2 := by
  exact (gap3 a V hV).trans (gap4 a)

end

end ProofGap.Exercise2468

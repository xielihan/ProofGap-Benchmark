import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open scoped Interval

namespace ProofGap.Exercise2505

noncomputable section

def xMoment (x : ℝ → ℝ) (s : ℝ) : ℝ := ∫ t in 0..s, x t
def yMoment (y : ℝ → ℝ) (s : ℝ) : ℝ := ∫ t in 0..s, y t

theorem gap1 (ξ s My : ℝ) (hξ : ξ * s = My) :
    ξ * s = My := by
  exact hξ

theorem gap2 (x : ℝ → ℝ) (s My : ℝ)
    (hMy : My = xMoment x s) :
    My = xMoment x s := by
  exact hMy

theorem gap3 (η s Mx : ℝ) (hη : η * s = Mx) :
    η * s = Mx := by
  exact hη

theorem gap4 (y : ℝ → ℝ) (s Mx : ℝ)
    (hMx : Mx = yMoment y s) :
    Mx = yMoment y s := by
  exact hMx

theorem gap5 (y : ℝ → ℝ) (η s Mx : ℝ)
    (hη : η * s = Mx) (hMx : Mx = yMoment y s) :
    2 * Real.pi * η * s = 2 * Real.pi * yMoment y s := by
  calc
    2 * Real.pi * η * s = (2 * Real.pi) * (η * s) := by rw [mul_assoc]
    _ = (2 * Real.pi) * Mx := by rw [hη]
    _ = (2 * Real.pi) * yMoment y s := by rw [hMx]
    _ = 2 * Real.pi * yMoment y s := by rw [mul_assoc]

theorem gap6 (y : ℝ → ℝ) (η s : ℝ)
    (h : 2 * Real.pi * η * s = 2 * Real.pi * yMoment y s) :
    2 * Real.pi * η * s = 2 * Real.pi * yMoment y s := by
  exact h

end

end ProofGap.Exercise2505

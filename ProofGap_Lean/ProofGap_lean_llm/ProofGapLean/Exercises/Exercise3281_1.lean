import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3281_1

noncomputable section

def partialXOrder (n : ℕ) (f : ℝ → ℝ → ℝ)
    (x y : ℝ) : ℝ :=
  (deriv^[n]) (fun t => f t y) x

def partialYOrder (n : ℕ) (f : ℝ → ℝ → ℝ)
    (x y : ℝ) : ℝ :=
  (deriv^[n]) (fun t => f x t) y

def laplacian (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  partialXOrder 2 f x y + partialYOrder 2 f x y

def u (x y : ℝ) : ℝ :=
  Real.sin x * Real.cosh y

theorem gap1 (x y : ℝ) :
    partialXOrder 2 u x y = -Real.sin x * Real.cosh y := by
  change
    deriv (deriv (fun t : ℝ => Real.sin t * Real.cosh y)) x =
      -Real.sin x * Real.cosh y
  have hfirst :
      deriv (fun t : ℝ => Real.sin t * Real.cosh y) =
        fun t : ℝ => Real.cos t * Real.cosh y := by
    funext t
    exact ((Real.hasDerivAt_sin t).mul_const (Real.cosh y)).deriv
  rw [hfirst]
  exact ((Real.hasDerivAt_cos x).mul_const (Real.cosh y)).deriv

theorem gap2 (x y : ℝ) :
    partialYOrder 2 u x y = Real.sin x * Real.cosh y := by
  change
    deriv (deriv (fun t : ℝ => Real.sin x * Real.cosh t)) y =
      Real.sin x * Real.cosh y
  have hfirst :
      deriv (fun t : ℝ => Real.sin x * Real.cosh t) =
        fun t : ℝ => Real.sin x * Real.sinh t := by
    funext t
    exact ((Real.hasDerivAt_cosh t).const_mul (Real.sin x)).deriv
  rw [hfirst]
  exact ((Real.hasDerivAt_sinh y).const_mul (Real.sin x)).deriv

theorem gap3 (x y : ℝ) :
    laplacian u x y =
      -Real.sin x * Real.cosh y + Real.sin x * Real.cosh y := by
  simp only [laplacian, gap1, gap2]

theorem gap4 (x y : ℝ) :
    -Real.sin x * Real.cosh y + Real.sin x * Real.cosh y = 0 := by
  ring

theorem gap5 (x y : ℝ) :
    laplacian u x y = 0 := by
  calc
    laplacian u x y =
        -Real.sin x * Real.cosh y + Real.sin x * Real.cosh y := gap3 x y
    _ = 0 := gap4 x y

end

end ProofGap.Exercise3281_1

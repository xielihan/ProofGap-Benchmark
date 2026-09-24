import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

namespace ProofGap.Exercise1182

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def y (C₁ C₂ x : ℝ) : ℝ := C₁ * Real.cosh x + C₂ * Real.sinh x

theorem gap1 (C₁ C₂ x : ℝ) :
    iterDeriv 1 (y C₁ C₂) x = C₁ * Real.sinh x + C₂ * Real.cosh x := by
  change
    deriv (fun z : ℝ => C₁ * Real.cosh z + C₂ * Real.sinh z) x =
      C₁ * Real.sinh x + C₂ * Real.cosh x
  simpa using
    ((((Real.hasDerivAt_cosh x).const_mul C₁).add
      ((Real.hasDerivAt_sinh x).const_mul C₂)).deriv)

theorem gap2 (C₁ C₂ x : ℝ) :
    iterDeriv 2 (y C₁ C₂) x = C₁ * Real.cosh x + C₂ * Real.sinh x := by
  change
    deriv (deriv (y C₁ C₂)) x =
      C₁ * Real.cosh x + C₂ * Real.sinh x
  have hfun :
      deriv (y C₁ C₂) =
        fun z : ℝ => C₁ * Real.sinh z + C₂ * Real.cosh z :=
    funext (gap1 C₁ C₂)
  rw [hfun]
  simpa using
    ((((Real.hasDerivAt_sinh x).const_mul C₁).add
      ((Real.hasDerivAt_cosh x).const_mul C₂)).deriv)

theorem gap3 (C₁ C₂ x : ℝ) :
    C₁ * Real.cosh x + C₂ * Real.sinh x = y C₁ C₂ x := by
  rfl

theorem gap4 (C₁ C₂ x : ℝ) :
    iterDeriv 2 (y C₁ C₂) x = y C₁ C₂ x := by
  simpa only [y] using gap2 C₁ C₂ x

theorem gap5 (C₁ C₂ x : ℝ) :
    iterDeriv 2 (y C₁ C₂) x - y C₁ C₂ x = 0 := by
  rw [gap4 C₁ C₂ x]
  exact sub_self (y C₁ C₂ x)

theorem gap6 (C₁ C₂ x : ℝ) :
    iterDeriv 2 (y C₁ C₂) x - y C₁ C₂ x = 0 := by
  exact gap5 C₁ C₂ x

end

end ProofGap.Exercise1182

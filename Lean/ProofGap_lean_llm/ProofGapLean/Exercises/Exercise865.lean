import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise865

noncomputable section

def y (n : ℕ) (x : ℝ) : ℝ :=
  Real.sin x ^ n * Real.cos ((n : ℝ) * x)

def expandedDerivative (n : ℕ) (x : ℝ) : ℝ :=
  (n : ℝ) * Real.sin x ^ (n - 1) * Real.cos x *
      Real.cos ((n : ℝ) * x) -
    (n : ℝ) * Real.sin x ^ n * Real.sin ((n : ℝ) * x)

def factoredDerivative (n : ℕ) (x : ℝ) : ℝ :=
  (n : ℝ) * Real.sin x ^ (n - 1) *
    (Real.cos x * Real.cos ((n : ℝ) * x) -
      Real.sin x * Real.sin ((n : ℝ) * x))

def finalDerivative (n : ℕ) (x : ℝ) : ℝ :=
  (n : ℝ) * Real.sin x ^ (n - 1) *
    Real.cos (((n : ℝ) + 1) * x)

/-- Exercise 865, gap 1. -/
theorem gap1 (n : ℕ) (x : ℝ) :
    deriv (y n) x = expandedDerivative n x := by
  unfold y expandedDerivative
  have hlin : HasDerivAt (fun t : ℝ => (n : ℝ) * t) (n : ℝ) x := by
    simpa using
      (hasDerivAt_const x (n : ℝ)).mul (hasDerivAt_id x)
  have hprod :=
    ((Real.hasDerivAt_sin x).pow n).mul
      ((Real.hasDerivAt_cos ((n : ℝ) * x)).comp x hlin)
  convert hprod.deriv using 1 <;>
    simp only [Function.comp_apply, Pi.pow_apply] <;>
    ring

/-- Exercise 865, gap 2. -/
theorem gap2 (n : ℕ) (x : ℝ) :
    expandedDerivative n x = factoredDerivative n x := by
  cases n with
  | zero =>
      simp [expandedDerivative, factoredDerivative]
  | succ n =>
      simp [expandedDerivative, factoredDerivative, pow_succ] <;> ring

/-- Exercise 865, gap 3. -/
theorem gap3 (n : ℕ) (x : ℝ) :
    factoredDerivative n x = finalDerivative n x := by
  unfold factoredDerivative finalDerivative
  have harg : x + (n : ℝ) * x = ((n : ℝ) + 1) * x := by
    ring
  rw [← Real.cos_add, harg]

/-- Exercise 865, gap 4. -/
theorem gap4 (n : ℕ) (x : ℝ) :
    deriv (y n) x = finalDerivative n x := by
  calc
    deriv (y n) x = expandedDerivative n x := gap1 n x
    _ = factoredDerivative n x := gap2 n x
    _ = finalDerivative n x := gap3 n x

end

end ProofGap.Exercise865

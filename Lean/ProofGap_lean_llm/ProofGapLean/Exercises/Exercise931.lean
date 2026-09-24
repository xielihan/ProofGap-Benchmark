import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise931

noncomputable section

def y (x : ℝ) : ℝ :=
  Real.log (1 + Real.sin x ^ 2) -
    2 * Real.sin x * Real.arctan (Real.sin x)

def expandedDerivative (x : ℝ) : ℝ :=
  Real.sin (2 * x) / (1 + Real.sin x ^ 2) -
    2 * Real.cos x * Real.arctan (Real.sin x) -
    Real.sin (2 * x) / (1 + Real.sin x ^ 2)

def finalDerivative (x : ℝ) : ℝ :=
  -2 * Real.cos x * Real.arctan (Real.sin x)

/-- Source: `proof_gap/exercise_931/1.txt`; `1 + sin² x` is positive for
every real `x`. -/
theorem gap1 (x : ℝ) :
    HasDerivAt y (expandedDerivative x) x := by
  have hsin : HasDerivAt Real.sin (Real.cos x) x := by
    exact Real.hasDerivAt_sin x
  have hinner :
      HasDerivAt (fun t : ℝ => 1 + Real.sin t ^ 2)
        (2 * Real.sin x * Real.cos x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).add (hsin.pow 2) using 1 <;> ring
  have hpos : 0 < 1 + Real.sin x ^ 2 := by
    positivity
  have hne : 1 + Real.sin x ^ 2 ≠ 0 := ne_of_gt hpos
  have hlog :
      HasDerivAt (fun t : ℝ => Real.log (1 + Real.sin t ^ 2))
        (2 * Real.sin x * Real.cos x / (1 + Real.sin x ^ 2)) x := by
    convert (Real.hasDerivAt_log hne).comp x hinner using 1 <;>
      simp only [div_eq_mul_inv] <;> ring
  have hatan :
      HasDerivAt (fun t : ℝ => Real.arctan (Real.sin t))
        (Real.cos x / (1 + Real.sin x ^ 2)) x := by
    convert (Real.hasDerivAt_arctan (Real.sin x)).comp x hsin using 1 <;>
      simp only [div_eq_mul_inv] <;> ring
  have hprod :
      HasDerivAt
        (fun t : ℝ => 2 * Real.sin t * Real.arctan (Real.sin t))
        (2 * Real.cos x * Real.arctan (Real.sin x) +
          2 * Real.sin x * (Real.cos x / (1 + Real.sin x ^ 2))) x := by
    convert (hsin.const_mul 2).mul hatan using 1 <;> ring
  have hderiv :
      2 * Real.sin x * Real.cos x / (1 + Real.sin x ^ 2) -
          (2 * Real.cos x * Real.arctan (Real.sin x) +
            2 * Real.sin x * (Real.cos x / (1 + Real.sin x ^ 2))) =
        expandedDerivative x := by
    simp only [expandedDerivative, Real.sin_two_mul]
    ring
  simpa only [y, hderiv] using hlog.sub hprod

/-- Source: `proof_gap/exercise_931/2.txt`. -/
theorem gap2 (x : ℝ) :
    expandedDerivative x = finalDerivative x := by
  unfold expandedDerivative finalDerivative
  ring

/-- Source: `proof_gap/exercise_931/3.txt`. -/
theorem gap3 (x : ℝ) :
    HasDerivAt y (finalDerivative x) x := by
  rw [← gap2 x]
  exact gap1 x

end

end ProofGap.Exercise931

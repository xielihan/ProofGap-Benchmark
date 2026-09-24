import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise911

noncomputable section

def y (x : ℝ) : ℝ :=
  x * (Real.sin (Real.log x) - Real.cos (Real.log x))

def expandedDerivative (x : ℝ) : ℝ :=
  Real.sin (Real.log x) - Real.cos (Real.log x) +
    x * (1 / x * Real.cos (Real.log x) + 1 / x * Real.sin (Real.log x))

def finalDerivative (x : ℝ) : ℝ :=
  2 * Real.sin (Real.log x)

/-- Source: `proof_gap/exercise_911/1.txt`; the logarithm is differentiated
on its positive real domain. -/
theorem gap1 (x : ℝ) (hx : 0 < x) :
    HasDerivAt y (expandedDerivative x) x := by
  have hlog : HasDerivAt Real.log (1 / x) x := by
    simpa [one_div] using Real.hasDerivAt_log hx.ne'
  have hsin :
      HasDerivAt (fun t : ℝ => Real.sin (Real.log t))
        (1 / x * Real.cos (Real.log x)) x := by
    convert (Real.hasDerivAt_sin (Real.log x)).comp x hlog using 1 <;> ring
  have hcos :
      HasDerivAt (fun t : ℝ => Real.cos (Real.log t))
        (-(1 / x * Real.sin (Real.log x))) x := by
    convert (Real.hasDerivAt_cos (Real.log x)).comp x hlog using 1 <;> ring
  have hdiff :
      HasDerivAt
        (fun t : ℝ => Real.sin (Real.log t) - Real.cos (Real.log t))
        (1 / x * Real.cos (Real.log x) + 1 / x * Real.sin (Real.log x)) x := by
    convert hsin.sub hcos using 1 <;> ring
  have hprod := (hasDerivAt_id x).mul hdiff
  simpa only [y, expandedDerivative, id_eq, one_mul] using hprod

/-- Source: `proof_gap/exercise_911/2.txt`; the cancellation uses `x ≠ 0`,
supplied by positivity. -/
theorem gap2 (x : ℝ) (hx : 0 < x) :
    expandedDerivative x = finalDerivative x := by
  unfold expandedDerivative finalDerivative
  field_simp [hx.ne'] <;> ring

/-- Source: `proof_gap/exercise_911/3.txt`; retain the logarithm's positive
domain in the final derivative statement. -/
theorem gap3 (x : ℝ) (hx : 0 < x) :
    HasDerivAt y (finalDerivative x) x := by
  rw [← gap2 x hx]
  exact gap1 x hx

end

end ProofGap.Exercise911

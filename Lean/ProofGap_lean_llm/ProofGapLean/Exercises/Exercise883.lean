import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise883

noncomputable section

def y (x : ℝ) : ℝ :=
  Real.exp x + Real.exp (Real.exp x) +
    Real.exp (Real.exp (Real.exp x))

theorem gap1 (x : ℝ) :
    deriv y x =
      Real.exp x *
        (1 + Real.exp (Real.exp x) *
          (1 + Real.exp (Real.exp (Real.exp x)))) := by
  have h1 : HasDerivAt (fun t : ℝ => Real.exp t) (Real.exp x) x := by
    simpa using (hasDerivAt_id x).exp
  have h2 : HasDerivAt
      (fun t : ℝ => Real.exp (Real.exp t))
      (Real.exp (Real.exp x) * Real.exp x) x :=
    h1.exp
  have h3 : HasDerivAt
      (fun t : ℝ => Real.exp (Real.exp (Real.exp t)))
      (Real.exp (Real.exp (Real.exp x)) *
        (Real.exp (Real.exp x) * Real.exp x)) x :=
    h2.exp
  have hsum : HasDerivAt y
      (Real.exp x + Real.exp (Real.exp x) * Real.exp x +
        Real.exp (Real.exp (Real.exp x)) *
          (Real.exp (Real.exp x) * Real.exp x)) x := by
    simpa [y] using (h1.add h2).add h3
  rw [hsum.deriv]
  ring

end

end ProofGap.Exercise883

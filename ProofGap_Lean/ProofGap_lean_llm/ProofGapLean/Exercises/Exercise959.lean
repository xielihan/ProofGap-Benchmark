import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise959

noncomputable section

def y (m x : ℝ) : ℝ :=
  Real.exp (m * Real.arcsin x) *
    (Real.cos (m * Real.arcsin x) + Real.sin (m * Real.arcsin x))

def expandedDerivative (m x : ℝ) : ℝ :=
  Real.exp (m * Real.arcsin x) *
    (m / Real.sqrt (1 - x ^ 2) *
        (Real.cos (m * Real.arcsin x) + Real.sin (m * Real.arcsin x)) +
      m / Real.sqrt (1 - x ^ 2) *
        (Real.cos (m * Real.arcsin x) - Real.sin (m * Real.arcsin x)))

def finalDerivative (m x : ℝ) : ℝ :=
  2 * m / Real.sqrt (1 - x ^ 2) *
    Real.exp (m * Real.arcsin x) * Real.cos (m * Real.arcsin x)

theorem gap1 (m x : ℝ) (hx : |x| < 1) :
    HasDerivAt (y m) (expandedDerivative m x) x := by
  have hx' : x ∈ Set.Ioo (-1 : ℝ) 1 := abs_lt.mp hx
  have hxne_neg_one : x ≠ (-1 : ℝ) := ne_of_gt hx'.1
  have hxne_one : x ≠ (1 : ℝ) := ne_of_lt hx'.2
  have harcsin :
      HasDerivAt Real.arcsin (1 / Real.sqrt (1 - x ^ 2)) x :=
    Real.hasDerivAt_arcsin hxne_neg_one hxne_one
  have hinner :
      HasDerivAt (fun z : ℝ => m * Real.arcsin z)
        (m / Real.sqrt (1 - x ^ 2)) x := by
    simpa [div_eq_mul_inv] using harcsin.const_mul m
  have hproduct :=
    ((Real.hasDerivAt_exp (m * Real.arcsin x)).comp x hinner).mul
      (((Real.hasDerivAt_cos (m * Real.arcsin x)).comp x hinner).add
        ((Real.hasDerivAt_sin (m * Real.arcsin x)).comp x hinner))
  convert hproduct using 1 <;>
    simp only [y, expandedDerivative, Function.comp_apply, Pi.mul_apply,
      Pi.add_apply, div_eq_mul_inv] <;>
    ring

theorem gap2 (m x : ℝ) (hx : |x| < 1) :
    expandedDerivative m x = finalDerivative m x := by
  unfold expandedDerivative finalDerivative
  ring

theorem gap3 (m x : ℝ) (hx : |x| < 1) :
    HasDerivAt (y m) (finalDerivative m x) x := by
  simpa only [gap2 m x hx] using (gap1 m x hx)

end

end ProofGap.Exercise959

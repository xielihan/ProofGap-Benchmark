import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1113

noncomputable section

def y (x : ℝ) : ℝ := Real.exp (-x ^ 2)

def secondDeriv (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (fun t => deriv f t) x

private theorem hasDerivAt_neg_sq (x : ℝ) :
    HasDerivAt (fun t : ℝ => -t ^ 2) (-2 * x) x := by
  have hmul : HasDerivAt (fun t : ℝ => t * t) (x + x) x := by
    simpa [id] using (hasDerivAt_id x).mul (hasDerivAt_id x)
  have hfun :
      (-(fun t : ℝ => t * t)) = (fun t : ℝ => -(t * t)) := by
    funext t
    rfl
  have hneg : HasDerivAt (fun t : ℝ => -(t * t)) (-(x + x)) x := by
    rw [← hfun]
    exact hmul.neg
  simpa only [pow_two, neg_mul, two_mul] using hneg

theorem gap1 (x : ℝ) :
    deriv y x = -2 * x * Real.exp (-x ^ 2) := by
  change deriv (fun t : ℝ => Real.exp (-t ^ 2)) x =
    -2 * x * Real.exp (-x ^ 2)
  have hcomp :
      HasDerivAt (fun t : ℝ => Real.exp (-t ^ 2))
        (Real.exp (-x ^ 2) * (-2 * x)) x := by
    simpa only [Function.comp_apply] using
      ((Real.hasDerivAt_exp (-x ^ 2)).comp x (hasDerivAt_neg_sq x))
  calc
    deriv (fun t : ℝ => Real.exp (-t ^ 2)) x =
        Real.exp (-x ^ 2) * (-2 * x) := hcomp.deriv
    _ = -2 * x * Real.exp (-x ^ 2) := by ring

theorem gap2 (x : ℝ) :
    secondDeriv y x = 2 * Real.exp (-x ^ 2) * (2 * x ^ 2 - 1) := by
  unfold secondDeriv
  have hderiv :
      (fun t : ℝ => deriv y t) =
        (fun t : ℝ => -2 * t * Real.exp (-t ^ 2)) := by
    funext t
    exact gap1 t
  rw [hderiv]
  have hexp :
      HasDerivAt (fun t : ℝ => Real.exp (-t ^ 2))
        (Real.exp (-x ^ 2) * (-2 * x)) x := by
    simpa only [Function.comp_apply] using
      ((Real.hasDerivAt_exp (-x ^ 2)).comp x (hasDerivAt_neg_sq x))
  have hlinear :
      HasDerivAt (fun t : ℝ => -2 * t) (-2) x := by
    convert ((hasDerivAt_const x (-2 : ℝ)).mul (hasDerivAt_id x)) using 1 <;>
      simp [id]
  have hproduct :
      HasDerivAt
        (fun t : ℝ => (-2 * t) * Real.exp (-t ^ 2))
        ((-2) * Real.exp (-x ^ 2) +
          (-2 * x) * (Real.exp (-x ^ 2) * (-2 * x))) x := by
    exact hlinear.mul hexp
  calc
    deriv (fun t : ℝ => -2 * t * Real.exp (-t ^ 2)) x =
        (-2) * Real.exp (-x ^ 2) +
          (-2 * x) * (Real.exp (-x ^ 2) * (-2 * x)) := hproduct.deriv
    _ = 2 * Real.exp (-x ^ 2) * (2 * x ^ 2 - 1) := by ring

end

end ProofGap.Exercise1113

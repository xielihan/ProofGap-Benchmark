import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1029

noncomputable section

def S (R : ℝ → ℝ) (t : ℝ) : ℝ := Real.pi * R t ^ 2

theorem gap1 (R : ℝ → ℝ) (t : ℝ) :
    S R t = Real.pi * R t ^ 2 := by
  rfl

theorem gap2 (R : ℝ → ℝ) (t : ℝ) (hR : HasDerivAt R 2 t) :
    HasDerivAt (S R) (2 * Real.pi * R t * deriv R t) t := by
  have hprod :
      HasDerivAt (fun x => R x * R x) (2 * R t + R t * 2) t :=
    hR.mul hR
  have hscaled := hprod.const_mul Real.pi
  have hcoeff :
      Real.pi * (2 * R t + R t * 2) =
        2 * Real.pi * R t * deriv R t := by
    rw [hR.deriv]
    ring
  rw [← hcoeff]
  change HasDerivAt (fun y => Real.pi * R y ^ 2)
    (Real.pi * (2 * R t + R t * 2)) t
  simpa only [pow_two] using hscaled

theorem gap3 (R : ℝ → ℝ) (t : ℝ)
    (hR : HasDerivAt R 2 t) (hvalue : R t = 10) :
    HasDerivAt (S R) (40 * Real.pi) t := by
  have h := gap2 R t hR
  have hcoeff : 2 * Real.pi * R t * deriv R t = 40 * Real.pi := by
    rw [hvalue, hR.deriv]
    ring
  rw [hcoeff] at h
  exact h

end

end ProofGap.Exercise1029

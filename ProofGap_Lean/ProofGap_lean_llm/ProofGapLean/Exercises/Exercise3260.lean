import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3260

noncomputable section

def u (x y z : ℝ) : ℝ :=
  Real.exp (x * y * z)

def partialX (g : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => g t y z) x

def partialXY (g : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partialX g x t z) y

def partialXYZ (g : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partialXY g x y t) z

def expandedThird (x y z : ℝ) : ℝ :=
  Real.exp (x * y * z) +
    x * y * z * Real.exp (x * y * z) +
    2 * x * y * z * Real.exp (x * y * z) +
    x ^ 2 * y ^ 2 * z ^ 2 * Real.exp (x * y * z)

def factoredThird (x y z : ℝ) : ℝ :=
  Real.exp (x * y * z) *
    (1 + 3 * x * y * z + x ^ 2 * y ^ 2 * z ^ 2)

theorem gap1 :
    ∀ x y z, partialX u x y z =
      y * z * Real.exp (x * y * z) := by
  intro x y z
  unfold partialX u
  have harg : HasDerivAt (fun t : ℝ => t * y * z) (y * z) x := by
    convert ((hasDerivAt_id x).mul_const y).mul_const z using 1 <;> ring
  convert ((Real.hasDerivAt_exp (x * y * z)).comp x harg).deriv using 1 <;> ring

theorem gap2 :
    ∀ x y z, partialXY u x y z =
      z * Real.exp (x * y * z) +
        x * y * z ^ 2 * Real.exp (x * y * z) := by
  intro x y z
  unfold partialXY
  have hrewrite :
      (fun t : ℝ => partialX u x t z) =
        (fun t => t * z * Real.exp (x * t * z)) := by
    funext t
    exact gap1 x t z
  rw [hrewrite]
  have hlinear : HasDerivAt (fun t : ℝ => t * z) z y := by
    convert (hasDerivAt_id y).mul_const z using 1 <;> ring
  have harg : HasDerivAt (fun t : ℝ => x * t * z) (x * z) y := by
    convert ((hasDerivAt_const y x).mul (hasDerivAt_id y)).mul_const z using 1 <;> ring
  have hexp :
      HasDerivAt (fun t : ℝ => Real.exp (x * t * z))
        (Real.exp (x * y * z) * (x * z)) y := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_exp (x * y * z)).comp y harg
  have hprod :
      HasDerivAt (fun t : ℝ => (t * z) * Real.exp (x * t * z))
        (z * Real.exp (x * y * z) +
          (y * z) * (Real.exp (x * y * z) * (x * z))) y :=
    hlinear.mul hexp
  convert hprod.deriv using 1 <;> ring

theorem gap3 :
    ∀ x y z, partialXYZ u x y z = expandedThird x y z := by
  intro x y z
  unfold partialXYZ
  have hrewrite :
      (fun t : ℝ => partialXY u x y t) =
        (fun t => t * Real.exp (x * y * t) +
          x * y * t ^ 2 * Real.exp (x * y * t)) := by
    funext t
    exact gap2 x y t
  rw [hrewrite]
  unfold expandedThird
  have harg : HasDerivAt (fun t : ℝ => x * y * t) (x * y) z := by
    convert (hasDerivAt_const z (x * y)).mul (hasDerivAt_id z) using 1 <;> ring
  have hexp :
      HasDerivAt (fun t : ℝ => Real.exp (x * y * t))
        (Real.exp (x * y * z) * (x * y)) z := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_exp (x * y * z)).comp z harg
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * z) z := by
    simpa [pow_two, two_mul] using
      (hasDerivAt_id z).mul (hasDerivAt_id z)
  have hcoef :
      HasDerivAt (fun t : ℝ => x * y * t ^ 2) ((x * y) * (2 * z)) z := by
    simpa [mul_assoc] using hsq.const_mul (x * y)
  have hfirst :
      HasDerivAt (fun t : ℝ => t * Real.exp (x * y * t))
        (Real.exp (x * y * z) +
          z * (Real.exp (x * y * z) * (x * y))) z := by
    simpa using (hasDerivAt_id z).mul hexp
  have hsecond :
      HasDerivAt (fun t : ℝ => x * y * t ^ 2 * Real.exp (x * y * t))
        (((x * y) * (2 * z)) * Real.exp (x * y * z) +
          (x * y * z ^ 2) * (Real.exp (x * y * z) * (x * y))) z := by
    simpa using hcoef.mul hexp
  have hsum := hfirst.add hsecond
  convert hsum.deriv using 1 <;> ring

theorem gap4 :
    ∀ x y z, expandedThird x y z = factoredThird x y z := by
  intro x y z
  unfold expandedThird factoredThird
  ring

theorem gap5 :
    ∀ x y z, partialXYZ u x y z = factoredThird x y z := by
  intro x y z
  calc
    partialXYZ u x y z = expandedThird x y z := gap3 x y z
    _ = factoredThird x y z := gap4 x y z

end

end ProofGap.Exercise3260

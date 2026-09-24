import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise937

noncomputable section

def y (x : ℝ) : ℝ :=
  x * Real.arcsin x ^ 2 +
    2 * Real.sqrt (1 - x ^ 2) * Real.arcsin x - 2 * x

def expandedDerivative (x : ℝ) : ℝ :=
  Real.arcsin x ^ 2 +
    2 * x * Real.arcsin x / Real.sqrt (1 - x ^ 2) -
    2 * x * Real.arcsin x / Real.sqrt (1 - x ^ 2) + 2 - 2

def finalDerivative (x : ℝ) : ℝ :=
  Real.arcsin x ^ 2

/-- Source: `proof_gap/exercise_937/1.txt`; restrict square root and inverse
sine to the common open interval `(-1,1)`. -/
theorem gap1 (x : ℝ) (hx : |x| < 1) :
    HasDerivAt y (expandedDerivative x) x := by
  have hbounds : -1 < x ∧ x < 1 := abs_lt.mp hx
  have hprod : 0 < (1 - x) * (1 + x) :=
    mul_pos (sub_pos.mpr hbounds.2) (by linarith [hbounds.1])
  have hpos : 0 < 1 - x ^ 2 := by
    nlinarith [hprod]
  have hs : Real.sqrt (1 - x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hpos)
  have hid : HasDerivAt (fun t : ℝ => t) 1 x := hasDerivAt_id x
  have hasin :
      HasDerivAt Real.arcsin (1 / Real.sqrt (1 - x ^ 2)) x :=
    Real.hasDerivAt_arcsin (ne_of_gt hbounds.1) (ne_of_lt hbounds.2)
  have hinner :
      HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-2 * x) x := by
    convert
      (hasDerivAt_const (x := x) (c := (1 : ℝ))).sub (hid.pow 2)
      using 1 <;> ring
  have hsqrt :
      HasDerivAt (fun t : ℝ => Real.sqrt (1 - t ^ 2))
        (-x / Real.sqrt (1 - x ^ 2)) x := by
    convert hinner.sqrt (ne_of_gt hpos) using 1 <;>
      field_simp [hs] <;>
      ring
  have hterm1 :
      HasDerivAt (fun t : ℝ => t * Real.arcsin t ^ 2)
        (Real.arcsin x ^ 2 +
          2 * x * Real.arcsin x / Real.sqrt (1 - x ^ 2)) x := by
    convert hid.mul (hasin.pow 2) using 1 <;>
      simp only [Pi.pow_apply] <;>
      field_simp [hs] <;>
      ring
  have hterm2 :
      HasDerivAt
        (fun t : ℝ =>
          2 * Real.sqrt (1 - t ^ 2) * Real.arcsin t)
        (-2 * x * Real.arcsin x / Real.sqrt (1 - x ^ 2) + 2) x := by
    convert (hsqrt.const_mul 2).mul hasin using 1 <;>
      field_simp [hs] <;>
      ring
  unfold y expandedDerivative
  convert (hterm1.add hterm2).sub (hid.const_mul 2) using 1 <;> ring

/-- Source: `proof_gap/exercise_937/2.txt`; the strict-domain hypothesis makes
the repeated square-root denominator nonzero. -/
theorem gap2 (x : ℝ) (hx : |x| < 1) :
    expandedDerivative x = finalDerivative x := by
  unfold expandedDerivative finalDerivative
  ring

/-- Source: `proof_gap/exercise_937/3.txt`; retain the nonsingular open domain
in the final derivative statement. -/
theorem gap3 (x : ℝ) (hx : |x| < 1) :
    HasDerivAt y (finalDerivative x) x := by
  rw [← gap2 x hx]
  exact gap1 x hx

end

end ProofGap.Exercise937

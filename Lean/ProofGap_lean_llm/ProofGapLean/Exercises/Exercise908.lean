import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise908

noncomputable section

def y (x : ℝ) : ℝ :=
  1 / (4 * x ^ 4) * Real.log (1 / x) - 1 / (16 * x ^ 4)

def expandedDerivative (x : ℝ) : ℝ :=
  -1 / x ^ 5 * Real.log (1 / x) - 1 / (4 * x ^ 5) + 1 / (4 * x ^ 5)

def finalDerivative (x : ℝ) : ℝ :=
  1 / x ^ 5 * Real.log x

/-- Source: `proof_gap/exercise_908/1.txt`; logarithms and displayed
denominators require `x > 0`. -/
theorem gap1 (x : ℝ) (hx : 0 < x) :
    HasDerivAt y (expandedDerivative x) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hden4 : 4 * x ^ 4 ≠ 0 := by
    exact mul_ne_zero (by norm_num) (pow_ne_zero 4 hx0)
  have hden16 : 16 * x ^ 4 ≠ 0 := by
    exact mul_ne_zero (by norm_num) (pow_ne_zero 4 hx0)
  have hinv : 1 / x ≠ 0 := div_ne_zero one_ne_zero hx0
  have hA :
      HasDerivAt (fun t : ℝ => 1 / (4 * t ^ 4)) (-1 / x ^ 5) x := by
    simpa only [one_div] using
      (show HasDerivAt (fun t : ℝ => (4 * t ^ 4)⁻¹) (-1 / x ^ 5) x by
        convert
          ((hasDerivAt_const x (4 : ℝ)).mul
            ((hasDerivAt_id x).pow 4)).inv hden4 using 1 <;>
          simp only [Pi.mul_apply, Pi.pow_apply, id_eq] <;>
          field_simp [hx0] <;> ring)
  have hquot :
      HasDerivAt (fun t : ℝ => 1 / t) (-1 / x ^ 2) x := by
    simpa only [one_div] using
      (show HasDerivAt (fun t : ℝ => t⁻¹) (-1 / x ^ 2) x by
        convert (hasDerivAt_id x).inv hx0 using 1 <;>
          field_simp [hx0] <;> ring)
  have hB :
      HasDerivAt (fun t : ℝ => Real.log (1 / t)) (-1 / x) x := by
    convert (Real.hasDerivAt_log hinv).comp x hquot using 1 <;>
      field_simp [hx0] <;> ring
  have hC :
      HasDerivAt (fun t : ℝ => 1 / (16 * t ^ 4))
        (-1 / (4 * x ^ 5)) x := by
    simpa only [one_div] using
      (show HasDerivAt (fun t : ℝ => (16 * t ^ 4)⁻¹)
          (-1 / (4 * x ^ 5)) x by
        convert
          ((hasDerivAt_const x (16 : ℝ)).mul
            ((hasDerivAt_id x).pow 4)).inv hden16 using 1 <;>
          simp only [Pi.mul_apply, Pi.pow_apply, id_eq] <;>
          field_simp [hx0] <;> ring)
  have h :
      HasDerivAt y
        ((-1 / x ^ 5) * Real.log (1 / x) +
          (1 / (4 * x ^ 4)) * (-1 / x) -
          (-1 / (4 * x ^ 5))) x := by
    simpa only [y] using (hA.mul hB).sub hC
  convert h using 1
  unfold expandedDerivative
  field_simp [hx0]
  ring

/-- Source: `proof_gap/exercise_908/2.txt`; `log (1/x) = -log x` is used on
the positive real domain. -/
theorem gap2 (x : ℝ) (hx : 0 < x) :
    expandedDerivative x = finalDerivative x := by
  unfold expandedDerivative finalDerivative
  rw [show 1 / x = x⁻¹ by simp, Real.log_inv]
  ring

/-- Source: `proof_gap/exercise_908/3.txt`; retain the positive domain of the
source logarithm. -/
theorem gap3 (x : ℝ) (hx : 0 < x) :
    HasDerivAt y (finalDerivative x) x := by
  rw [← gap2 x hx]
  exact gap1 x hx

end

end ProofGap.Exercise908

import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise1672

noncomputable section

def integrand (x : ℝ) : ℝ := 1 / Real.cosh (x / 2) ^ 2
def primitive (x : ℝ) : ℝ := 2 * Real.tanh (x / 2)

theorem gap1 (x : ℝ) :
    HasDerivAt primitive (integrand x) x := by
  have hp :
      primitive =
        (fun y : ℝ => 2 * (Real.sinh (y / 2) / Real.cosh (y / 2))) := by
    funext y
    simp only [primitive, Real.tanh_eq_sinh_div_cosh]
  rw [hp]
  unfold integrand
  have hn : Real.cosh (x / 2) ≠ 0 := (Real.cosh_pos (x / 2)).ne'
  have hs :
      HasDerivAt (fun y : ℝ => Real.sinh (y / 2))
        (Real.cosh (x / 2) * (1 / 2)) x := by
    simpa only [Function.comp_def, id_eq] using
      ((Real.hasDerivAt_sinh (x / 2)).comp x
        ((hasDerivAt_id x).div_const 2))
  have hc :
      HasDerivAt (fun y : ℝ => Real.cosh (y / 2))
        (Real.sinh (x / 2) * (1 / 2)) x := by
    simpa only [Function.comp_def, id_eq] using
      ((Real.hasDerivAt_cosh (x / 2)).comp x
        ((hasDerivAt_id x).div_const 2))
  convert (hs.div hc hn).const_mul 2 using 1
  field_simp [hn]
  simpa using (Real.cosh_sq_sub_sinh_sq (x / 2)).symm

end

end ProofGap.Exercise1672

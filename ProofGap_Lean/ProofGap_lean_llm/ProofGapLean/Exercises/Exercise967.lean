import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise967

noncomputable section

def y (x : ℝ) : ℝ :=
  Real.log (Real.cosh x) + 1 / (2 * Real.cosh x ^ 2)

def expandedDerivative (x : ℝ) : ℝ :=
  Real.tanh x - Real.sinh x / Real.cosh x ^ 3

def finalDerivative (x : ℝ) : ℝ := Real.tanh x ^ 3

theorem gap1 (x : ℝ) : HasDerivAt y (expandedDerivative x) x := by
  have hneg :
      HasDerivAt (fun z : ℝ => Real.exp (-z)) (-Real.exp (-x)) x := by
    convert (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x) using 1 <;>
      ring
  have hexp :
      HasDerivAt (fun z : ℝ => (Real.exp z + Real.exp (-z)) / 2)
        ((Real.exp x - Real.exp (-x)) / 2) x := by
    convert ((Real.hasDerivAt_exp x).add hneg).div_const 2 using 1 <;>
      ring
  have hc : HasDerivAt (fun z : ℝ => Real.cosh z) (Real.sinh x) x := by
    simpa only [Real.cosh_eq, Real.sinh_eq] using hexp
  have hcosh : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  have hlog :
      HasDerivAt (fun z : ℝ => Real.log (Real.cosh z)) (Real.tanh x) x := by
    simpa only [Real.tanh_eq_sinh_div_cosh] using hc.log hcosh
  have hsq :
      HasDerivAt (fun z : ℝ => Real.cosh z ^ 2)
        (2 * Real.cosh x * Real.sinh x) x := by
    convert hc.pow 2 using 1 <;> ring
  have hden :
      HasDerivAt (fun z : ℝ => 2 * Real.cosh z ^ 2)
        (4 * Real.cosh x * Real.sinh x) x := by
    convert (hasDerivAt_const x (2 : ℝ)).mul hsq using 1 <;> ring
  have hden_ne : 2 * Real.cosh x ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 hcosh)
  have hterm0 := (hasDerivAt_const x (1 : ℝ)).div hden hden_ne
  have hterm :
      HasDerivAt (fun z : ℝ => 1 / (2 * Real.cosh z ^ 2))
        (-(Real.sinh x / Real.cosh x ^ 3)) x := by
    convert hterm0 using 1 <;>
      field_simp [hcosh] <;>
      ring
  simpa only [y, expandedDerivative, sub_eq_add_neg] using hlog.add hterm

theorem gap2 (x : ℝ) : expandedDerivative x = finalDerivative x := by
  unfold expandedDerivative finalDerivative
  simp only [Real.tanh_eq_sinh_div_cosh]
  have hcosh : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  have hsquare : Real.cosh x ^ 2 - 1 = Real.sinh x ^ 2 := by
    linarith [Real.cosh_sq_sub_sinh_sq x]
  calc
    Real.sinh x / Real.cosh x - Real.sinh x / Real.cosh x ^ 3 =
        Real.sinh x * (Real.cosh x ^ 2 - 1) / Real.cosh x ^ 3 := by
      field_simp [hcosh]
    _ = Real.sinh x * Real.sinh x ^ 2 / Real.cosh x ^ 3 := by
      rw [hsquare]
    _ = (Real.sinh x / Real.cosh x) ^ 3 := by
      field_simp [hcosh]

theorem gap3 (x : ℝ) : HasDerivAt y (finalDerivative x) x := by
  rw [← gap2 x]
  exact gap1 x

end

end ProofGap.Exercise967

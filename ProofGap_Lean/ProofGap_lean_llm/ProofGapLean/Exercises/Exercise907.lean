import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise907

noncomputable section

def polynomial (x : ℝ) : ℝ :=
  Real.log x ^ 3 + 3 * Real.log x ^ 2 + 6 * Real.log x + 6

def y (x : ℝ) : ℝ := (1 / x) * polynomial x

def expandedDerivative (x : ℝ) : ℝ :=
  -(1 / x ^ 2) * polynomial x +
    (1 / x) *
      ((3 / x) * Real.log x ^ 2 +
        (6 / x) * Real.log x + 6 / x)

def finalDerivative (x : ℝ) : ℝ := -(Real.log x ^ 3 / x ^ 2)

theorem gap1 (x : ℝ) (hx : 0 < x) :
    deriv y x = expandedDerivative x := by
  have hlog : HasDerivAt Real.log (1 / x) x := by
    simpa only [one_div] using Real.hasDerivAt_log (ne_of_gt hx)
  have hinv : HasDerivAt (fun z : ℝ => 1 / z) (-(1 / x ^ 2)) x := by
    convert (hasDerivAt_const x (1 : ℝ)).div (hasDerivAt_id x) (ne_of_gt hx) using 1 <;>
      simp only [id_eq] <;> ring
  have hpoly :
      HasDerivAt polynomial
        ((3 / x) * Real.log x ^ 2 +
          (6 / x) * Real.log x + 6 / x) x := by
    unfold polynomial
    convert
      (((hlog.pow 3).add ((hlog.pow 2).const_mul 3)).add
        (hlog.const_mul 6)).add_const 6 using 1 <;>
      ring
  have hy : HasDerivAt y (expandedDerivative x) x := by
    simpa only [y, expandedDerivative] using hinv.mul hpoly
  exact hy.deriv

theorem gap2 (x : ℝ) (hx : 0 < x) :
    expandedDerivative x = finalDerivative x := by
  unfold expandedDerivative finalDerivative polynomial
  field_simp [hx.ne']
  ring

theorem gap3 (x : ℝ) (hx : 0 < x) :
    deriv y x = finalDerivative x := by
  exact (gap1 x hx).trans (gap2 x hx)

end

end ProofGap.Exercise907

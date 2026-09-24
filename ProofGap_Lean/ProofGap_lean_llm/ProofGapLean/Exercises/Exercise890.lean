import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise890

noncomputable section

def y (x : ℝ) : ℝ :=
  (1 / 4 : ℝ) * Real.log ((x ^ 2 - 1) / (x ^ 2 + 1))

def logDifference (x : ℝ) : ℝ :=
  Real.log (x ^ 2 - 1) - Real.log (x ^ 2 + 1)

def expandedDerivative (x : ℝ) : ℝ :=
  (1 / 4 : ℝ) * (2 * x / (x ^ 2 - 1) - 2 * x / (x ^ 2 + 1))

def finalDerivative (x : ℝ) : ℝ := x / (x ^ 4 - 1)

private theorem derivative_data (x : ℝ) (hx : 1 < x ^ 2) :
    HasDerivAt y (finalDerivative x) x ∧
      HasDerivAt logDifference
        (2 * x / (x ^ 2 - 1) - 2 * x / (x ^ 2 + 1)) x := by
  have hm : x ^ 2 - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hx)
  have hp_pos : 0 < x ^ 2 + 1 := by
    nlinarith [sq_nonneg x]
  have hp : x ^ 2 + 1 ≠ 0 := ne_of_gt hp_pos
  have hfour : x ^ 4 - 1 ≠ 0 := by
    rw [show x ^ 4 - 1 = (x ^ 2 - 1) * (x ^ 2 + 1) by ring]
    exact mul_ne_zero hm hp
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_id x).pow 2
  have hm' : HasDerivAt (fun t : ℝ => t ^ 2 - 1) (2 * x) x := by
    exact hsq.sub_const (1 : ℝ)
  have hp' : HasDerivAt (fun t : ℝ => t ^ 2 + 1) (2 * x) x := by
    exact hsq.add_const (1 : ℝ)
  have hlm : HasDerivAt (fun t : ℝ => Real.log (t ^ 2 - 1))
      (2 * x / (x ^ 2 - 1)) x := by
    simpa [div_eq_mul_inv, mul_comm] using
      (Real.hasDerivAt_log hm).comp x hm'
  have hlp : HasDerivAt (fun t : ℝ => Real.log (t ^ 2 + 1))
      (2 * x / (x ^ 2 + 1)) x := by
    simpa [div_eq_mul_inv, mul_comm] using
      (Real.hasDerivAt_log hp).comp x hp'
  have hld : HasDerivAt logDifference
      (2 * x / (x ^ 2 - 1) - 2 * x / (x ^ 2 + 1)) x := by
    simpa [logDifference] using hlm.sub hlp
  have hqne : (x ^ 2 - 1) / (x ^ 2 + 1) ≠ 0 := div_ne_zero hm hp
  have hlogq :
      HasDerivAt
        (Real.log ∘ fun t : ℝ => (t ^ 2 - 1) / (t ^ 2 + 1))
        (4 * x / (x ^ 4 - 1)) x := by
    convert
      (Real.hasDerivAt_log hqne).comp x (hm'.div hp' hp) using 1 <;>
      field_simp [hm, hp, hfour] <;>
      ring
  have hy : HasDerivAt y (finalDerivative x) x := by
    convert
      ((hasDerivAt_const x (1 / 4 : ℝ)).mul hlogq) using 1 <;>
      simp [y, finalDerivative, Function.comp_def] <;>
      ring
  exact ⟨hy, hld⟩

theorem gap1 (x : ℝ) (hx : 1 < x ^ 2) :
    deriv y x = (1 / 4 : ℝ) * deriv logDifference x := by
  have hm : x ^ 2 - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hx)
  have hp_pos : 0 < x ^ 2 + 1 := by
    nlinarith [sq_nonneg x]
  have hp : x ^ 2 + 1 ≠ 0 := ne_of_gt hp_pos
  have hfour : x ^ 4 - 1 ≠ 0 := by
    rw [show x ^ 4 - 1 = (x ^ 2 - 1) * (x ^ 2 + 1) by ring]
    exact mul_ne_zero hm hp
  have hy := (derivative_data x hx).1.deriv
  have hlog := (derivative_data x hx).2.deriv
  rw [hy, hlog]
  unfold finalDerivative
  field_simp [hm, hp, hfour]
  <;> ring

theorem gap2 (x : ℝ) (hx : 1 < x ^ 2) :
    (1 / 4 : ℝ) * deriv logDifference x = expandedDerivative x := by
  rw [(derivative_data x hx).2.deriv]
  rfl

theorem gap3 (x : ℝ) (hx : 1 < x ^ 2) :
    expandedDerivative x = finalDerivative x := by
  have hm : x ^ 2 - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hx)
  have hp_pos : 0 < x ^ 2 + 1 := by
    nlinarith [sq_nonneg x]
  have hp : x ^ 2 + 1 ≠ 0 := ne_of_gt hp_pos
  have hfour : x ^ 4 - 1 ≠ 0 := by
    rw [show x ^ 4 - 1 = (x ^ 2 - 1) * (x ^ 2 + 1) by ring]
    exact mul_ne_zero hm hp
  unfold expandedDerivative finalDerivative
  field_simp [hm, hp, hfour]
  <;> ring

theorem gap4 (x : ℝ) (hx : 1 < x ^ 2) :
    deriv y x = finalDerivative x := by
  calc
    deriv y x = (1 / 4 : ℝ) * deriv logDifference x := gap1 x hx
    _ = expandedDerivative x := gap2 x hx
    _ = finalDerivative x := gap3 x hx

end

end ProofGap.Exercise890

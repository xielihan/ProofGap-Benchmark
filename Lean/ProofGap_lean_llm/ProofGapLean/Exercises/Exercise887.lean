import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise887

noncomputable section

def y (x : ℝ) : ℝ := Real.log (Real.log (Real.log x))

theorem gap1 (x : ℝ) (hx : 0 < x) (hlogx : 0 < Real.log x)
    (hloglogx : 0 < Real.log (Real.log x)) :
    deriv y x =
      1 / (x * Real.log x * Real.log (Real.log x)) := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hlogx0 : Real.log x ≠ 0 := ne_of_gt hlogx
  have hloglogx0 : Real.log (Real.log x) ≠ 0 := ne_of_gt hloglogx
  have hx_deriv : HasDerivAt Real.log x⁻¹ x :=
    Real.hasDerivAt_log hx0
  have hlogx_deriv :
      HasDerivAt Real.log (Real.log x)⁻¹ (Real.log x) :=
    Real.hasDerivAt_log hlogx0
  have hloglogx_deriv :
      HasDerivAt Real.log (Real.log (Real.log x))⁻¹
        (Real.log (Real.log x)) :=
    Real.hasDerivAt_log hloglogx0
  have hinner :
      HasDerivAt (fun z : ℝ => Real.log (Real.log z))
        ((Real.log x)⁻¹ * x⁻¹) x := by
    simpa only [Function.comp_apply] using (hlogx_deriv.comp x hx_deriv)
  have hall :
      HasDerivAt (fun z : ℝ => Real.log (Real.log (Real.log z)))
        ((Real.log (Real.log x))⁻¹ * ((Real.log x)⁻¹ * x⁻¹)) x := by
    simpa only [Function.comp_apply] using (hloglogx_deriv.comp x hinner)
  calc
    deriv y x =
        (Real.log (Real.log x))⁻¹ * ((Real.log x)⁻¹ * x⁻¹) := by
      simpa [y] using hall.deriv
    _ = 1 / (x * Real.log x * Real.log (Real.log x)) := by
      field_simp [hx0, hlogx0, hloglogx0] <;> ring

end

end ProofGap.Exercise887

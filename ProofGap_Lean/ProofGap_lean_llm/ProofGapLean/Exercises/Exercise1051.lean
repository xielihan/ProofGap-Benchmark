import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise1051

theorem gap1 (a : ℝ) (y : ℝ → ℝ)
    (hcurve : ∀ x, Real.sqrt x + Real.sqrt (y x) = Real.sqrt a)
    (hdiff : Differentiable ℝ y) (x : ℝ) (hx : 0 < x)
    (hy : 0 < y x) :
    1 / (2 * Real.sqrt x) +
      (1 / (2 * Real.sqrt (y x))) * deriv y x = 0 := by
  have hsqrt_x :
      HasDerivAt Real.sqrt (1 / (2 * Real.sqrt x)) x :=
    Real.hasDerivAt_sqrt (ne_of_gt hx)
  have hsqrt_y :
      HasDerivAt (fun z => Real.sqrt (y z))
        ((1 / (2 * Real.sqrt (y x))) * deriv y x) x :=
    (Real.hasDerivAt_sqrt (ne_of_gt hy)).comp x ((hdiff x).hasDerivAt)
  have hsum :
      HasDerivAt (fun z => Real.sqrt z + Real.sqrt (y z))
        (1 / (2 * Real.sqrt x) +
          (1 / (2 * Real.sqrt (y x))) * deriv y x) x :=
    hsqrt_x.add hsqrt_y
  have hfun :
      (fun z : ℝ => Real.sqrt z + Real.sqrt (y z)) =
        (fun _ : ℝ => Real.sqrt a) := by
    funext z
    exact hcurve z
  rw [hfun] at hsum
  exact hsum.unique (hasDerivAt_const x (Real.sqrt a))

theorem gap2 (a : ℝ) (y : ℝ → ℝ)
    (hcurve : ∀ x, Real.sqrt x + Real.sqrt (y x) = Real.sqrt a)
    (hdiff : Differentiable ℝ y) (x : ℝ) (hx : 0 < x)
    (hy : 0 < y x) :
    deriv y x = -Real.sqrt (y x / x) := by
  have h := gap1 a y hcurve hdiff x hx hy
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hsy : 0 < Real.sqrt (y x) := Real.sqrt_pos.2 hy
  field_simp [ne_of_gt hsx, ne_of_gt hsy] at h
  have hd : deriv y x = -Real.sqrt (y x) / Real.sqrt x := by
    apply (eq_div_iff (ne_of_gt hsx)).2
    linarith
  calc
    deriv y x = -Real.sqrt (y x) / Real.sqrt x := hd
    _ = -(Real.sqrt (y x) / Real.sqrt x) := neg_div _ _
    _ = -Real.sqrt (y x / x) := by
      rw [Real.sqrt_div (le_of_lt hy)]

end ProofGap.Exercise1051

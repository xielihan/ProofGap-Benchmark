import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1053

private theorem composeRealHasDerivAt
    (f g : ℝ → ℝ) (f' g' x : ℝ)
    (hg : HasDerivAt g g' (f x))
    (hf : HasDerivAt f f' x) :
    HasDerivAt (fun z => g (f z)) (g' * f') x := by
  exact hg.comp x hf

theorem gap1 (y : ℝ → ℝ)
    (hcurve : ∀ x,
      Real.arctan (y x / x) = Real.log (Real.sqrt (x ^ 2 + y x ^ 2)))
    (hdiff : Differentiable ℝ y) (x : ℝ) (hx : x ≠ 0)
    (hr : 0 < x ^ 2 + y x ^ 2) :
    (1 / (1 + y x ^ 2 / x ^ 2)) *
        ((x * deriv y x - y x) / x ^ 2) =
      (x + y x * deriv y x) / (x ^ 2 + y x ^ 2) := by
  have hy : HasDerivAt y (deriv y x) x := (hdiff x).hasDerivAt
  have hquot :
      HasDerivAt (fun z : ℝ => y z / z)
        ((x * deriv y x - y x) / x ^ 2) x := by
    convert hy.div (hasDerivAt_id x) hx using 1 <;> simp [id] <;> ring
  have hleft0 :
      HasDerivAt (fun z : ℝ => Real.arctan (y z / z))
        ((1 / (1 + (y x / x) ^ 2)) *
          ((x * deriv y x - y x) / x ^ 2)) x := by
    exact composeRealHasDerivAt
      (f := fun z : ℝ => y z / z) (g := Real.arctan)
      (f' := (x * deriv y x - y x) / x ^ 2)
      (g' := 1 / (1 + (y x / x) ^ 2)) (x := x)
      (Real.hasDerivAt_arctan (y x / x)) hquot
  have hleft :
      HasDerivAt (fun z : ℝ => Real.arctan (y z / z))
        ((1 / (1 + y x ^ 2 / x ^ 2)) *
          ((x * deriv y x - y x) / x ^ 2)) x := by
    simpa only [div_pow] using hleft0
  have hinner :
      HasDerivAt (fun z : ℝ => z ^ 2 + y z ^ 2)
        (2 * (x + y x * deriv y x)) x := by
    convert ((hasDerivAt_id x).pow 2).add (hy.pow 2) using 1 <;>
      simp [id] <;> ring
  have hq0 : x ^ 2 + y x ^ 2 ≠ 0 := ne_of_gt hr
  have hs0 : Real.sqrt (x ^ 2 + y x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hr)
  have hs_sq :
      Real.sqrt (x ^ 2 + y x ^ 2) ^ 2 = x ^ 2 + y x ^ 2 :=
    Real.sq_sqrt (le_of_lt hr)
  have hs_mul := congrArg
    (fun z : ℝ => z * (x + y x * deriv y x)) hs_sq
  have hright :
      HasDerivAt
        (fun z : ℝ => Real.log (Real.sqrt (z ^ 2 + y z ^ 2)))
        ((x + y x * deriv y x) / (x ^ 2 + y x ^ 2)) x := by
    convert
      (Real.hasDerivAt_log hs0).comp x
        ((Real.hasDerivAt_sqrt hq0).comp x hinner) using 1
    field_simp [hs0, hq0]
    nlinarith [hs_mul]
  have hderiv :
      deriv (fun z : ℝ => Real.arctan (y z / z)) x =
        deriv (fun z : ℝ => Real.log (Real.sqrt (z ^ 2 + y z ^ 2))) x :=
    congrArg (fun f : ℝ → ℝ => deriv f x) (funext hcurve)
  calc
    (1 / (1 + y x ^ 2 / x ^ 2)) *
          ((x * deriv y x - y x) / x ^ 2) =
        deriv (fun z : ℝ => Real.arctan (y z / z)) x := hleft.deriv.symm
    _ = deriv (fun z : ℝ => Real.log (Real.sqrt (z ^ 2 + y z ^ 2))) x := hderiv
    _ = (x + y x * deriv y x) / (x ^ 2 + y x ^ 2) := hright.deriv

theorem gap2 (y : ℝ → ℝ)
    (hcurve : ∀ x,
      Real.arctan (y x / x) = Real.log (Real.sqrt (x ^ 2 + y x ^ 2)))
    (hdiff : Differentiable ℝ y) (x : ℝ) (hx : x ≠ 0)
    (hr : 0 < x ^ 2 + y x ^ 2) (hxy : x ≠ y x) :
    deriv y x = (x + y x) / (x - y x) := by
  have h := gap1 y hcurve hdiff x hx hr
  have hq0 : x ^ 2 + y x ^ 2 ≠ 0 := ne_of_gt hr
  have hratio :
      1 + y x ^ 2 / x ^ 2 =
        (x ^ 2 + y x ^ 2) / x ^ 2 := by
    field_simp [hx] <;> ring
  have hsimp :
      (1 / (1 + y x ^ 2 / x ^ 2)) *
          ((x * deriv y x - y x) / x ^ 2) =
        (x * deriv y x - y x) / (x ^ 2 + y x ^ 2) := by
    rw [hratio]
    field_simp [hx, hq0] <;> ring
  rw [hsimp] at h
  field_simp [hq0] at h
  apply (eq_div_iff (sub_ne_zero.mpr hxy)).2
  linarith

end ProofGap.Exercise1053

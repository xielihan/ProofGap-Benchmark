import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1667

noncomputable section

def cot (x : ℝ) : ℝ := Real.cos x / Real.sin x
def integrand (x : ℝ) : ℝ := 1 / Real.sin (2 * x + Real.pi / 4) ^ 2
def primitive (x : ℝ) : ℝ := -(1 / 2 : ℝ) * cot (2 * x + Real.pi / 4)
def domain : Set ℝ := {x | Real.sin (2 * x + Real.pi / 4) ≠ 0}

theorem gap1 (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt primitive (integrand x) x := by
  have hsin_ne : Real.sin (2 * x + Real.pi / 4) ≠ 0 := by
    simpa [domain] using hx
  have hu : HasDerivAt (fun y : ℝ => 2 * y + Real.pi / 4) 2 x := by
    simpa using ((hasDerivAt_id x).const_mul 2).add_const (Real.pi / 4)
  have hcos_raw :=
    (Real.hasDerivAt_cos (2 * x + Real.pi / 4)).comp x hu
  have hcos :
      HasDerivAt (fun y : ℝ => Real.cos (2 * y + Real.pi / 4))
        (-Real.sin (2 * x + Real.pi / 4) * 2) x := by
    simpa only [Function.comp_apply] using hcos_raw
  have hsin_raw :=
    (Real.hasDerivAt_sin (2 * x + Real.pi / 4)).comp x hu
  have hsin :
      HasDerivAt (fun y : ℝ => Real.sin (2 * y + Real.pi / 4))
        (Real.cos (2 * x + Real.pi / 4) * 2) x := by
    simpa only [Function.comp_apply] using hsin_raw
  have hnum :
      (-Real.sin (2 * x + Real.pi / 4) * 2) *
            Real.sin (2 * x + Real.pi / 4) -
          Real.cos (2 * x + Real.pi / 4) *
            (Real.cos (2 * x + Real.pi / 4) * 2) =
        -2 := by
    calc
      _ = -2 *
          (Real.sin (2 * x + Real.pi / 4) ^ 2 +
            Real.cos (2 * x + Real.pi / 4) ^ 2) := by ring
      _ = -2 := by
        rw [Real.sin_sq_add_cos_sq]
        ring
  have hcoef :
      -(1 / 2 : ℝ) *
          (((-Real.sin (2 * x + Real.pi / 4) * 2) *
                Real.sin (2 * x + Real.pi / 4) -
              Real.cos (2 * x + Real.pi / 4) *
                (Real.cos (2 * x + Real.pi / 4) * 2)) /
            Real.sin (2 * x + Real.pi / 4) ^ 2) =
        integrand x := by
    unfold integrand
    rw [hnum]
    ring
  rw [← hcoef]
  simpa only [primitive, cot] using
    (hcos.div hsin hsin_ne).const_mul (-(1 / 2 : ℝ))

end

end ProofGap.Exercise1667

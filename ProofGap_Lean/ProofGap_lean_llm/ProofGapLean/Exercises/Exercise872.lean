import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise872

noncomputable section

def sec (x : ℝ) : ℝ := 1 / Real.cos x

def y (x : ℝ) : ℝ :=
  Real.tan x - (1 / 3 : ℝ) * Real.tan x ^ 3 +
    (1 / 5 : ℝ) * Real.tan x ^ 5

def expandedDerivative (x : ℝ) : ℝ :=
  sec x ^ 2 - Real.tan x ^ 2 * sec x ^ 2 +
    Real.tan x ^ 4 * sec x ^ 2

def finalDerivative (x : ℝ) : ℝ := 1 + Real.tan x ^ 6

/-- Exercise 872, gap 1; restrict to points where tangent
is defined. -/
theorem gap1 (x : ℝ) (hcos : Real.cos x ≠ 0) :
    deriv y x = expandedDerivative x := by
  have ht0 :
      HasDerivAt (fun z : ℝ => Real.sin z / Real.cos z)
        ((Real.cos x * Real.cos x - Real.sin x * (-Real.sin x)) /
          Real.cos x ^ 2) x := by
    exact (Real.hasDerivAt_sin x).div (Real.hasDerivAt_cos x) hcos
  have hcoef :
      (Real.cos x * Real.cos x - Real.sin x * (-Real.sin x)) /
          Real.cos x ^ 2 =
        1 / Real.cos x ^ 2 := by
    calc
      (Real.cos x * Real.cos x - Real.sin x * (-Real.sin x)) /
            Real.cos x ^ 2 =
          (Real.sin x ^ 2 + Real.cos x ^ 2) / Real.cos x ^ 2 := by ring
      _ = 1 / Real.cos x ^ 2 := by rw [Real.sin_sq_add_cos_sq]
  have ht : HasDerivAt Real.tan (1 / Real.cos x ^ 2) x := by
    change HasDerivAt (fun z : ℝ => Real.tan z) (1 / Real.cos x ^ 2) x
    rw [← hcoef]
    simpa only [Real.tan_eq_sin_div_cos] using ht0
  have hy :
      HasDerivAt y
        (1 / Real.cos x ^ 2 -
            (1 / 3 : ℝ) *
              ((3 : ℝ) * Real.tan x ^ (3 - 1) * (1 / Real.cos x ^ 2)) +
          (1 / 5 : ℝ) *
            ((5 : ℝ) * Real.tan x ^ (5 - 1) * (1 / Real.cos x ^ 2))) x := by
    unfold y
    simpa only using
      (ht.sub ((ht.pow 3).const_mul (1 / 3 : ℝ))).add
        ((ht.pow 5).const_mul (1 / 5 : ℝ))
  calc
    deriv y x =
        1 / Real.cos x ^ 2 -
            (1 / 3 : ℝ) *
              ((3 : ℝ) * Real.tan x ^ (3 - 1) * (1 / Real.cos x ^ 2)) +
          (1 / 5 : ℝ) *
            ((5 : ℝ) * Real.tan x ^ (5 - 1) * (1 / Real.cos x ^ 2)) := hy.deriv
    _ = expandedDerivative x := by
      unfold expandedDerivative sec
      field_simp [hcos]

/-- Exercise 872, gap 2; the identity uses
`sec² x = 1 + tan² x` on tangent's domain. -/
theorem gap2 (x : ℝ) (hcos : Real.cos x ≠ 0) :
    expandedDerivative x = finalDerivative x := by
  have hsec : sec x ^ 2 = 1 + Real.tan x ^ 2 := by
    unfold sec
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hcos] <;>
      nlinarith [Real.sin_sq_add_cos_sq x]
  unfold expandedDerivative finalDerivative
  rw [hsec]
  ring

/-- Exercise 872, gap 3; restrict to the source function's
domain. -/
theorem gap3 (x : ℝ) (hcos : Real.cos x ≠ 0) :
    deriv y x = finalDerivative x := by
  calc
    deriv y x = expandedDerivative x := gap1 x hcos
    _ = finalDerivative x := gap2 x hcos

end

end ProofGap.Exercise872

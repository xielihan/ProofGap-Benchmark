import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise875

noncomputable section

def sec (x : ℝ) : ℝ := 1 / Real.cos x
def y (x : ℝ) : ℝ := Real.sin (Real.cos (Real.tan x ^ 3) ^ 2)

def expandedDerivative (x : ℝ) : ℝ :=
  Real.cos (Real.cos (Real.tan x ^ 3) ^ 2) * (-2) *
    Real.cos (Real.tan x ^ 3) * Real.sin (Real.tan x ^ 3) *
      3 * Real.tan x ^ 2 * sec x ^ 2

def finalDerivative (x : ℝ) : ℝ :=
  -3 * Real.tan x ^ 2 * sec x ^ 2 *
    Real.sin (2 * Real.tan x ^ 3) *
      Real.cos (Real.cos (Real.tan x ^ 3) ^ 2)

theorem gap1 (x : ℝ) (hcos : Real.cos x ≠ 0) :
    deriv y x = expandedDerivative x := by
  have htanBase : HasDerivAt Real.tan
      ((Real.cos x * Real.cos x - Real.sin x * -Real.sin x) /
        Real.cos x ^ 2) x := by
    convert ((hasDerivAt_id x).sin).div ((hasDerivAt_id x).cos) hcos using 1
    · exact funext fun z => Real.tan_eq_sin_div_cos z
    · simp
  have hnum :
      Real.cos x * Real.cos x - Real.sin x * -Real.sin x = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hcoeff :
      (Real.cos x * Real.cos x - Real.sin x * -Real.sin x) /
          Real.cos x ^ 2 = sec x ^ 2 := by
    rw [hnum]
    unfold sec
    field_simp [hcos] <;> ring
  rw [hcoeff] at htanBase
  have htan3 : HasDerivAt (fun z => Real.tan z ^ 3)
      (3 * Real.tan x ^ 2 * sec x ^ 2) x := by
    simpa using htanBase.pow 3
  have hcos3 : HasDerivAt (fun z => Real.cos (Real.tan z ^ 3))
      (-Real.sin (Real.tan x ^ 3) *
        (3 * Real.tan x ^ 2 * sec x ^ 2)) x := by
    simpa using htan3.cos
  have hcosSq :
      HasDerivAt (fun z => Real.cos (Real.tan z ^ 3) ^ 2)
        (2 * Real.cos (Real.tan x ^ 3) *
          (-Real.sin (Real.tan x ^ 3) *
            (3 * Real.tan x ^ 2 * sec x ^ 2))) x := by
    simpa using hcos3.pow 2
  have hy : HasDerivAt y
      (Real.cos (Real.cos (Real.tan x ^ 3) ^ 2) *
        (2 * Real.cos (Real.tan x ^ 3) *
          (-Real.sin (Real.tan x ^ 3) *
            (3 * Real.tan x ^ 2 * sec x ^ 2)))) x := by
    unfold y
    simpa using hcosSq.sin
  rw [hy.deriv]
  unfold expandedDerivative
  ring

theorem gap2 (x : ℝ) (hcos : Real.cos x ≠ 0) :
    deriv y x = finalDerivative x := by
  rw [gap1 x hcos]
  unfold expandedDerivative finalDerivative
  rw [Real.sin_two_mul]
  ring

end

end ProofGap.Exercise875

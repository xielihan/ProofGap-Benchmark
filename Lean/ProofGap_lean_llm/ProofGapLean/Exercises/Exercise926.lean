import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise926

noncomputable section

def arccot (x : ℝ) : ℝ :=
  Real.pi / 2 - Real.arctan x

def y (x : ℝ) : ℝ :=
  arccot ((Real.sin x + Real.cos x) / (Real.sin x - Real.cos x))

def expandedDerivative (x : ℝ) : ℝ :=
  (-1 / (1 + ((Real.sin x + Real.cos x) /
      (Real.sin x - Real.cos x)) ^ 2)) *
    (((Real.cos x - Real.sin x) * (Real.sin x - Real.cos x) -
      (Real.cos x + Real.sin x) ^ 2) /
      (Real.sin x - Real.cos x) ^ 2)

def finalDerivative (_x : ℝ) : ℝ :=
  1

/-- Source: `proof_gap/exercise_926/1.txt`; exclude zeros of the quotient's
trigonometric denominator. -/
theorem gap1 (x : ℝ) (hx : Real.sin x - Real.cos x ≠ 0) :
    HasDerivAt y (expandedDerivative x) x := by
  have hs : HasDerivAt Real.sin (Real.cos x) x :=
    Real.hasDerivAt_sin x
  have hc : HasDerivAt Real.cos (-Real.sin x) x :=
    Real.hasDerivAt_cos x
  let q' : ℝ :=
    (((Real.cos x + -Real.sin x) * (Real.sin x - Real.cos x) -
        (Real.sin x + Real.cos x) * (Real.cos x - -Real.sin x)) /
      (Real.sin x - Real.cos x) ^ 2)
  have hq :
      HasDerivAt
        (fun t : ℝ =>
          (Real.sin t + Real.cos t) / (Real.sin t - Real.cos t))
        q' x := by
    simpa [q'] using (hs.add hc).div (hs.sub hc) hx
  have hraw :
      HasDerivAt y
        (-((1 / (1 + ((Real.sin x + Real.cos x) /
            (Real.sin x - Real.cos x)) ^ 2)) * q')) x := by
    simpa [y, arccot] using
      ((Real.hasDerivAt_arctan
          ((Real.sin x + Real.cos x) /
            (Real.sin x - Real.cos x))).comp x hq).const_sub
        (Real.pi / 2)
  have hq' :
      q' =
        (((Real.cos x - Real.sin x) * (Real.sin x - Real.cos x) -
            (Real.cos x + Real.sin x) ^ 2) /
          (Real.sin x - Real.cos x) ^ 2) := by
    dsimp [q']
    field_simp [hx]
    ring
  have hderiv :
      -((1 / (1 + ((Real.sin x + Real.cos x) /
          (Real.sin x - Real.cos x)) ^ 2)) * q') =
        expandedDerivative x := by
    rw [hq']
    unfold expandedDerivative
    ring
  rw [hderiv] at hraw
  exact hraw

/-- Source: `proof_gap/exercise_926/2.txt`; the simplification is valid on
each component of the quotient's domain. -/
theorem gap2 (x : ℝ) (hx : Real.sin x - Real.cos x ≠ 0) :
    expandedDerivative x = finalDerivative x := by
  unfold expandedDerivative finalDerivative
  have hden :
      1 + ((Real.sin x + Real.cos x) /
        (Real.sin x - Real.cos x)) ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg
      ((Real.sin x + Real.cos x) / (Real.sin x - Real.cos x))]
  field_simp [hx, hden] <;> ring

/-- Source: `proof_gap/exercise_926/3.txt`; retain the omitted rational
trigonometric poles in the final derivative statement. -/
theorem gap3 (x : ℝ) (hx : Real.sin x - Real.cos x ≠ 0) :
    HasDerivAt y (finalDerivative x) x := by
  rw [← gap2 x hx]
  exact gap1 x hx

end

end ProofGap.Exercise926

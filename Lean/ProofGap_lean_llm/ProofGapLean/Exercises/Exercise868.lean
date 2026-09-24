import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise868

noncomputable section

def y (x : ℝ) : ℝ := Real.cos x / (2 * Real.sin x ^ 2)

def expandedDerivative (x : ℝ) : ℝ :=
  (-2 * Real.sin x ^ 3 - 4 * Real.sin x * Real.cos x ^ 2) /
    (4 * Real.sin x ^ 4)

def finalDerivative (x : ℝ) : ℝ :=
  -(1 + Real.cos x ^ 2) / (2 * Real.sin x ^ 3)

/-- Source: `proof_gap/exercise_868/1.txt`; restrict to the domain of the
quotient. -/
theorem gap1 (x : ℝ) (hsin : Real.sin x ≠ 0) :
    deriv y x = expandedDerivative x := by
  unfold y expandedDerivative
  have hden :
      HasDerivAt (fun z : ℝ => 2 * Real.sin z ^ 2)
        (4 * Real.sin x * Real.cos x) x := by
    convert ((Real.hasDerivAt_sin x).pow 2).const_mul 2 using 1 <;> ring
  have hden_ne : 2 * Real.sin x ^ 2 ≠ 0 :=
    mul_ne_zero two_ne_zero (pow_ne_zero 2 hsin)
  have hquot :
      HasDerivAt (fun z : ℝ => Real.cos z / (2 * Real.sin z ^ 2))
        (((-Real.sin x) * (2 * Real.sin x ^ 2) -
            Real.cos x * (4 * Real.sin x * Real.cos x)) /
          (2 * Real.sin x ^ 2) ^ 2) x :=
    (Real.hasDerivAt_cos x).div hden hden_ne
  rw [hquot.deriv]
  field_simp [hsin]
  ring

/-- Source: `proof_gap/exercise_868/2.txt`; retain the source function's
domain while simplifying its derivative. -/
theorem gap2 (x : ℝ) (hsin : Real.sin x ≠ 0) :
    expandedDerivative x = finalDerivative x := by
  unfold expandedDerivative finalDerivative
  have hnum :
      -2 * Real.sin x ^ 3 - 4 * Real.sin x * Real.cos x ^ 2 =
        -2 * Real.sin x * (1 + Real.cos x ^ 2) := by
    calc
      -2 * Real.sin x ^ 3 - 4 * Real.sin x * Real.cos x ^ 2 =
          -2 * Real.sin x *
            (Real.sin x ^ 2 + Real.cos x ^ 2 + Real.cos x ^ 2) := by
              ring
      _ = -2 * Real.sin x * (1 + Real.cos x ^ 2) := by
        rw [Real.sin_sq_add_cos_sq]
  rw [hnum]
  field_simp [hsin] <;> ring

/-- Source: `proof_gap/exercise_868/3.txt`; restrict to the domain of the
source function. -/
theorem gap3 (x : ℝ) (hsin : Real.sin x ≠ 0) :
    deriv y x = finalDerivative x := by
  calc
    deriv y x = expandedDerivative x := gap1 x hsin
    _ = finalDerivative x := gap2 x hsin

end

end ProofGap.Exercise868

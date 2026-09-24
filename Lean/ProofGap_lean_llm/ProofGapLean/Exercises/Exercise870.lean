import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise870

noncomputable section

def denominator (x : ℝ) : ℝ := Real.cos x + x * Real.sin x

def y (x : ℝ) : ℝ :=
  (Real.sin x - x * Real.cos x) / denominator x

def expandedDerivative (x : ℝ) : ℝ :=
  (((x * Real.sin x - Real.cos x + Real.cos x) * denominator x) -
      ((Real.sin x - Real.sin x + x * Real.cos x) *
        (Real.sin x - x * Real.cos x))) /
    denominator x ^ 2

def finalDerivative (x : ℝ) : ℝ := x ^ 2 / denominator x ^ 2

/-- Source: `proof_gap/exercise_870/1.txt`; restrict to the domain of the
quotient. -/
theorem gap1 (x : ℝ) (hden : denominator x ≠ 0) :
    deriv y x = expandedDerivative x := by
  have hnum :
      HasDerivAt (fun z : ℝ => Real.sin z - z * Real.cos z)
        (x * Real.sin x) x := by
    convert (Real.hasDerivAt_sin x).sub
      ((hasDerivAt_id x).mul (Real.hasDerivAt_cos x)) using 1 <;>
      simp [id] <;> ring
  have hden' : HasDerivAt denominator (x * Real.cos x) x := by
    unfold denominator
    convert (Real.hasDerivAt_cos x).add
      ((hasDerivAt_id x).mul (Real.hasDerivAt_sin x)) using 1 <;>
      simp [id] <;> ring
  unfold y expandedDerivative
  convert (hnum.div hden' hden).deriv using 1 <;> ring

/-- Source: `proof_gap/exercise_870/2.txt`; retain the source function's
domain while simplifying its derivative. -/
theorem gap2 (x : ℝ) (hden : denominator x ≠ 0) :
    expandedDerivative x = finalDerivative x := by
  unfold expandedDerivative finalDerivative denominator
  have hnum :
      ((x * Real.sin x - Real.cos x + Real.cos x) *
          (Real.cos x + x * Real.sin x) -
        (Real.sin x - Real.sin x + x * Real.cos x) *
          (Real.sin x - x * Real.cos x)) = x ^ 2 := by
    calc
      _ = x ^ 2 * (Real.sin x ^ 2 + Real.cos x ^ 2) := by ring
      _ = x ^ 2 := by rw [Real.sin_sq_add_cos_sq, mul_one]
  rw [hnum]

/-- Source: `proof_gap/exercise_870/3.txt`; restrict to the domain of the
source function. -/
theorem gap3 (x : ℝ) (hden : denominator x ≠ 0) :
    deriv y x = finalDerivative x := by
  exact (gap1 x hden).trans (gap2 x hden)

end

end ProofGap.Exercise870

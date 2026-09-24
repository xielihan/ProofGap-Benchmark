import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise913

noncomputable section

def y (x : ℝ) : ℝ :=
  Real.arcsin (x / 2)

def expandedDerivative (x : ℝ) : ℝ :=
  1 / Real.sqrt (1 - (x / 2) ^ 2) * (1 / 2)

def finalDerivative (x : ℝ) : ℝ :=
  1 / Real.sqrt (4 - x ^ 2)

/-- Source: `proof_gap/exercise_913/1.txt`; the inverse sine is
differentiated strictly inside its real domain. -/
theorem gap1 (x : ℝ) (hx : |x| < 2) :
    HasDerivAt y (expandedDerivative x) x := by
  have hx' : x / 2 ∈ Set.Ioo (-1) 1 := by
    have hbounds := abs_lt.mp hx
    constructor <;> nlinarith
  have hlin : HasDerivAt (fun z : ℝ => z / 2) (1 / 2) x := by
    simpa [div_eq_mul_inv, mul_comm] using
      ((hasDerivAt_id x).const_mul ((2 : ℝ)⁻¹))
  have hne_neg : x / 2 ≠ -1 := ne_of_gt hx'.1
  have hne_pos : x / 2 ≠ 1 := ne_of_lt hx'.2
  simpa [y, expandedDerivative] using
    (Real.hasDerivAt_arcsin hne_neg hne_pos).comp x hlin

/-- Source: `proof_gap/exercise_913/2.txt`; the strict interior hypothesis
makes both square-root denominators positive. -/
theorem gap2 (x : ℝ) (hx : |x| < 2) :
    expandedDerivative x = finalDerivative x := by
  have hxm : -2 < x := (abs_lt.mp hx).1
  have hxp : x < 2 := (abs_lt.mp hx).2
  have hprod : 0 < (2 - x) * (2 + x) :=
    mul_pos (sub_pos.mpr hxp) (by linarith)
  have hB : 0 < 4 - x ^ 2 := by
    nlinarith [hprod]
  have hA : 0 < 1 - (x / 2) ^ 2 := by
    nlinarith [hB]
  have hsa : 0 < Real.sqrt (1 - (x / 2) ^ 2) :=
    Real.sqrt_pos.2 hA
  have hsb : 0 < Real.sqrt (4 - x ^ 2) :=
    Real.sqrt_pos.2 hB
  have hs :
      Real.sqrt (4 - x ^ 2) =
        2 * Real.sqrt (1 - (x / 2) ^ 2) := by
    have hfactor :
        (Real.sqrt (4 - x ^ 2) -
            2 * Real.sqrt (1 - (x / 2) ^ 2)) *
          (Real.sqrt (4 - x ^ 2) +
            2 * Real.sqrt (1 - (x / 2) ^ 2)) = 0 := by
      nlinarith [Real.sq_sqrt (le_of_lt hA),
        Real.sq_sqrt (le_of_lt hB)]
    rcases mul_eq_zero.mp hfactor with h | h
    · nlinarith
    · nlinarith
  unfold expandedDerivative finalDerivative
  rw [hs]
  field_simp [ne_of_gt hsa]

/-- Source: `proof_gap/exercise_913/3.txt`; retain the nonsingular inverse
trigonometric domain. -/
theorem gap3 (x : ℝ) (hx : |x| < 2) :
    HasDerivAt y (finalDerivative x) x := by
  rw [← gap2 x hx]
  exact gap1 x hx

end

end ProofGap.Exercise913

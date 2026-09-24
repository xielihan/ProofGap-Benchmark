import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise1115

noncomputable section

def y (x : ℝ) : ℝ := (1 + x ^ 2) * Real.arctan x

def secondDeriv (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (fun t => deriv f t) x

theorem gap1 (x : ℝ) :
    deriv y x = 1 + 2 * x * Real.arctan x := by
  have hx : 1 + x ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg x]
  have h :=
    (((hasDerivAt_const x (1 : ℝ)).add ((hasDerivAt_id x).pow 2)).mul
      (Real.hasDerivAt_arctan x))
  have hd : deriv y x = 2 * x * Real.arctan x + 1 := by
    simpa [y, hx, div_eq_mul_inv] using h.deriv
  linarith

theorem gap2 (x : ℝ) :
    secondDeriv y x = 2 * Real.arctan x + 2 * x / (1 + x ^ 2) := by
  unfold secondDeriv
  have hy : (fun t => deriv y t) = fun t => 1 + 2 * t * Real.arctan t := by
    funext t
    exact gap1 t
  rw [hy]
  have hx : 1 + x ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg x]
  have h :
      HasDerivAt (fun t : ℝ => 1 + 2 * t * Real.arctan t)
        (2 * Real.arctan x + 2 * x / (1 + x ^ 2)) x := by
    simpa [hx, div_eq_mul_inv, mul_add, mul_assoc] using
      ((((hasDerivAt_id x).mul (Real.hasDerivAt_arctan x)).const_mul 2).const_add 1)
  exact h.deriv

end

end ProofGap.Exercise1115

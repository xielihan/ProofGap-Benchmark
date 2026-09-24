import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise869

noncomputable section

def y (n : ℕ) (x : ℝ) : ℝ := 1 / Real.cos x ^ n

def expandedDerivative (n : ℕ) (x : ℝ) : ℝ :=
  (-1 / Real.cos x ^ (2 * n)) * (-(n : ℝ)) *
    Real.cos x ^ (n - 1) * Real.sin x

def finalDerivative (n : ℕ) (x : ℝ) : ℝ :=
  (n : ℝ) * Real.sin x / Real.cos x ^ (n + 1)

/-- Exercise 869, gap 1; restrict to the domain of the
reciprocal power. -/
theorem gap1 (n : ℕ) (x : ℝ) (hcos : Real.cos x ≠ 0) :
    deriv (y n) x = expandedDerivative n x := by
  have hcosPow : Real.cos x ^ n ≠ 0 := pow_ne_zero n hcos
  have hy : y n = (Real.cos ^ n)⁻¹ := by
    funext z
    simp [y]
  rw [hy]
  have hderiv :
      deriv ((Real.cos ^ n)⁻¹) x =
        (-((n : ℝ) * Real.cos x ^ (n - 1) * (-Real.sin x)) /
          (Real.cos x ^ n) ^ 2) := by
    simpa [one_div] using
      (((Real.hasDerivAt_cos x).pow n).inv hcosPow).deriv
  rw [hderiv]
  unfold expandedDerivative
  rw [Nat.mul_comm 2 n, pow_mul]
  ring_nf

/-- Exercise 869, gap 2; retain the source function's
domain while simplifying its derivative. -/
theorem gap2 (n : ℕ) (x : ℝ) (hcos : Real.cos x ≠ 0) :
    expandedDerivative n x = finalDerivative n x := by
  cases n with
  | zero =>
      simp [expandedDerivative, finalDerivative]
  | succ k =>
      have hpow :
          Real.cos x ^ (2 * Nat.succ k) =
            Real.cos x ^ k * Real.cos x ^ (Nat.succ k + 1) := by
        have hexp : 2 * Nat.succ k = k + (Nat.succ k + 1) := by
          omega
        rw [hexp, pow_add]
      unfold expandedDerivative finalDerivative
      simp only [Nat.succ_sub_one]
      rw [hpow]
      field_simp [hcos]

/-- Exercise 869, gap 3; restrict to the domain of the
source function. -/
theorem gap3 (n : ℕ) (x : ℝ) (hcos : Real.cos x ≠ 0) :
    deriv (y n) x = finalDerivative n x := by
  calc
    deriv (y n) x = expandedDerivative n x := gap1 n x hcos
    _ = finalDerivative n x := gap2 n x hcos

end

end ProofGap.Exercise869

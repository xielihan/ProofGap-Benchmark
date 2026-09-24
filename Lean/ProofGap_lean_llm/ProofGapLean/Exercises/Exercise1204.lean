import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1204

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def y (x : ℝ) : ℝ :=
  (x ^ 2 + 2 * x + 2) * Real.exp (-x)

private theorem iterDeriv_closed (n : ℕ) (x : ℝ) :
    iterDeriv n y x =
      (-1 : ℝ) ^ n * Real.exp (-x) *
        (x ^ 2 + (2 - 2 * (n : ℝ)) * x +
          ((n : ℝ) ^ 2 - 3 * (n : ℝ) + 2)) := by
  induction n generalizing x with
  | zero =>
      simp [iterDeriv, y] <;> ring
  | succ n ih =>
      have hfun : iterDeriv n y =
          (fun t : ℝ =>
            (-1 : ℝ) ^ n * Real.exp (-t) *
              (t ^ 2 + (2 - 2 * (n : ℝ)) * t +
                ((n : ℝ) ^ 2 - 3 * (n : ℝ) + 2))) := by
        funext t
        exact ih t
      have hstep : iterDeriv (Nat.succ n) y x = deriv (iterDeriv n y) x := by
        simp only [iterDeriv, Function.iterate_succ_apply']
      have hexp : HasDerivAt (fun t : ℝ => Real.exp (-t))
          (-Real.exp (-x)) x := by
        simpa using
          (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg
      have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
        simpa [pow_two, two_mul] using
          (hasDerivAt_id x).mul (hasDerivAt_id x)
      have hlin : HasDerivAt
          (fun t : ℝ => (2 - 2 * (n : ℝ)) * t)
          (2 - 2 * (n : ℝ)) x := by
        simpa using
          (hasDerivAt_const x (2 - 2 * (n : ℝ))).mul
            (hasDerivAt_id x)
      have hpoly : HasDerivAt
          (fun t : ℝ =>
            t ^ 2 + (2 - 2 * (n : ℝ)) * t +
              ((n : ℝ) ^ 2 - 3 * (n : ℝ) + 2))
          (2 * x + (2 - 2 * (n : ℝ))) x := by
        simpa only [Pi.add_apply, add_zero] using
          (hsq.add hlin).add
            (hasDerivAt_const x
              ((n : ℝ) ^ 2 - 3 * (n : ℝ) + 2))
      have hwhole :=
        ((hasDerivAt_const x ((-1 : ℝ) ^ n)).mul hexp).mul hpoly
      rw [hstep, hfun]
      convert hwhole.deriv using 1 <;>
        simp only [Pi.mul_apply, Nat.cast_succ, pow_succ] <;>
        ring

theorem gap1 (n : ℕ) (x : ℝ) :
    iterDeriv n y x =
      (-1 : ℝ) ^ n * (x ^ 2 + 2 * x + 2) * Real.exp (-x) +
        2 * (-1 : ℝ) ^ (n - 1) * (x + 1) * Real.exp (-x) * (n : ℝ) +
        (-1 : ℝ) ^ (n - 2) * (n : ℝ) *
          ((n - 1 : ℕ) : ℝ) * Real.exp (-x) := by
  rw [iterDeriv_closed]
  cases n with
  | zero =>
      norm_num <;> ring
  | succ n =>
      cases n with
      | zero =>
          norm_num <;> ring
      | succ n =>
          simp only [Nat.cast_succ, Nat.succ_sub_succ_eq_sub,
            Nat.sub_zero, pow_succ]
          ring

theorem gap2 (n : ℕ) (x : ℝ) (hn : 1 ≤ n) :
    iterDeriv n y x =
      (-1 : ℝ) ^ n * Real.exp (-x) *
        (x ^ 2 - 2 * ((n - 1 : ℕ) : ℝ) * x +
          ((n - 1 : ℕ) : ℝ) * ((n - 2 : ℕ) : ℝ)) := by
  rw [iterDeriv_closed]
  cases n with
  | zero =>
      norm_num at hn
  | succ n =>
      cases n with
      | zero =>
          norm_num
      | succ n =>
          simp only [Nat.cast_succ, Nat.succ_sub_succ_eq_sub,
            Nat.sub_zero, pow_succ]
          ring

end

end ProofGap.Exercise1204

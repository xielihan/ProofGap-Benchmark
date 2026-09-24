import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1201

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def y (x : ℝ) : ℝ :=
  Real.sin x ^ 4 + Real.cos x ^ 4

private theorem hasDerivAt_scaled_cos (a c x : ℝ) :
    HasDerivAt (fun t : ℝ => a * Real.cos (4 * t + c))
      (4 * a * Real.cos (4 * x + c + Real.pi / 2)) x := by
  have hlin : HasDerivAt (fun t : ℝ => 4 * t + c) 4 x := by
    convert (((hasDerivAt_const x (4 : ℝ)).mul (hasDerivAt_id x)).add
      (hasDerivAt_const x c)) using 1 <;> ring
  have hcos :=
    (Real.hasDerivAt_cos (4 * x + c)).comp x hlin
  have h :=
    (hasDerivAt_const x a).mul hcos
  convert h using 1 <;>
    simp [Real.cos_add] <;> ring

private theorem iterDeriv_succ_formula
    (hy : ∀ x : ℝ,
      y x = (3 / 4 : ℝ) + (1 / 4 : ℝ) * Real.cos (4 * x))
    (k : ℕ) (x : ℝ) :
    iterDeriv (Nat.succ k) y x =
      (4 : ℝ) ^ k *
        Real.cos (4 * x + (Nat.succ k : ℝ) / 2 * Real.pi) := by
  induction k generalizing x with
  | zero =>
      have hyfun :
          y = fun t : ℝ =>
            (3 / 4 : ℝ) + (1 / 4 : ℝ) * Real.cos (4 * t + 0) := by
        funext t
        simpa using hy t
      simp only [iterDeriv, Function.iterate_one, pow_zero, one_mul,
        Nat.cast_one]
      rw [hyfun]
      have h :=
        (hasDerivAt_const x (3 / 4 : ℝ)).add
          (hasDerivAt_scaled_cos (1 / 4 : ℝ) 0 x)
      convert h.deriv using 1 <;> ring
  | succ k ih =>
      have hfun :
          (deriv^[Nat.succ k]) y = fun t : ℝ =>
            (4 : ℝ) ^ k *
              Real.cos (4 * t + (Nat.succ k : ℝ) / 2 * Real.pi) := by
        funext t
        exact ih t
      rw [iterDeriv, Function.iterate_succ_apply', hfun]
      have hd :=
        hasDerivAt_scaled_cos ((4 : ℝ) ^ k)
          ((Nat.succ k : ℝ) / 2 * Real.pi) x
      convert hd.deriv using 1 <;>
        simp only [Nat.cast_succ, pow_succ] <;> ring

theorem gap1 (x : ℝ) :
    y x =
      (Real.sin x ^ 2 + Real.cos x ^ 2) ^ 2 -
        2 * Real.sin x ^ 2 * Real.cos x ^ 2 := by
  unfold y
  ring

theorem gap2 (x : ℝ) :
    (Real.sin x ^ 2 + Real.cos x ^ 2) ^ 2 -
        2 * Real.sin x ^ 2 * Real.cos x ^ 2 =
      1 - (1 / 2 : ℝ) * Real.sin (2 * x) ^ 2 := by
  rw [Real.sin_sq_add_cos_sq, Real.sin_two_mul]
  ring

theorem gap3 (x : ℝ) :
    1 - (1 / 2 : ℝ) * Real.sin (2 * x) ^ 2 =
      1 - (1 / 4 : ℝ) * (1 - Real.cos (4 * x)) := by
  have hcos :
      Real.cos (4 * x) = 2 * Real.cos (2 * x) ^ 2 - 1 := by
    convert Real.cos_two_mul (2 * x) using 1 <;> ring
  nlinarith [Real.sin_sq_add_cos_sq (2 * x), hcos]

theorem gap4 (x : ℝ) :
    1 - (1 / 4 : ℝ) * (1 - Real.cos (4 * x)) =
      (3 / 4 : ℝ) + (1 / 4 : ℝ) * Real.cos (4 * x) := by
  ring

theorem gap5 (x : ℝ) :
    y x = (3 / 4 : ℝ) + (1 / 4 : ℝ) * Real.cos (4 * x) := by
  calc
    y x =
        (Real.sin x ^ 2 + Real.cos x ^ 2) ^ 2 -
          2 * Real.sin x ^ 2 * Real.cos x ^ 2 := gap1 x
    _ = 1 - (1 / 2 : ℝ) * Real.sin (2 * x) ^ 2 := gap2 x
    _ = 1 - (1 / 4 : ℝ) * (1 - Real.cos (4 * x)) := gap3 x
    _ = (3 / 4 : ℝ) + (1 / 4 : ℝ) * Real.cos (4 * x) := gap4 x

theorem gap6 (n : ℕ) (x : ℝ) (hn : 1 ≤ n) :
    iterDeriv n y x =
      (4 : ℝ) ^ (n - 1) *
        Real.cos (4 * x + (n : ℝ) / 2 * Real.pi) := by
  cases n with
  | zero => simp at hn
  | succ k =>
      simpa using iterDeriv_succ_formula gap5 k x

end

end ProofGap.Exercise1201

import ProofGapLean.Prelude.Discrete
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace ProofGap.Exercise3262

noncomputable section

def u (x₀ y₀ : ℝ) (p q : ℕ) (x y : ℝ) : ℝ :=
  (x - x₀) ^ p * (y - y₀) ^ q

def partialXOrder (n : ℕ) (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  (deriv^[n]) (fun t => g t y) x

def partialYOrder (n : ℕ) (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  (deriv^[n]) (fun t => g x t) y

def mixedOrder (p q : ℕ) (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  partialYOrder q (fun a b => partialXOrder p g a b) x y

private theorem iterDerivSubPowMul (a : ℝ) :
    ∀ (n : ℕ) (c x : ℝ),
      (deriv^[n]) (fun t : ℝ => (t - a) ^ n * c) x =
        (Nat.factorial n : ℝ) * c := by
  intro n
  induction n with
  | zero =>
      intro c x
      simp
  | succ n ih =>
      intro c x
      rw [Function.iterate_succ_apply]
      have h :
          deriv (fun t : ℝ => (t - a) ^ (n + 1) * c) =
            fun t : ℝ => (t - a) ^ n * ((n.succ : ℝ) * c) := by
        funext t
        have ht :=
          (((hasDerivAt_id t).sub_const a).pow (n + 1)).mul_const c
        simpa [Nat.succ_eq_add_one, mul_comm, mul_left_comm, mul_assoc] using
          ht.deriv
      rw [h]
      simpa [Nat.factorial_succ, Nat.cast_mul, Nat.succ_eq_add_one,
        mul_comm, mul_left_comm, mul_assoc] using
        (ih ((n.succ : ℝ) * c) x)

theorem gap1 (x₀ y₀ : ℝ) (p q : ℕ) :
    ∀ x y, partialXOrder p (u x₀ y₀ p q) x y =
      (Nat.factorial p : ℝ) * (y - y₀) ^ q := by
  intro x y
  simpa [partialXOrder, u] using
    (iterDerivSubPowMul x₀ p ((y - y₀) ^ q) x)

theorem gap2 (x₀ y₀ : ℝ) (p q : ℕ) :
    ∀ x y, mixedOrder p q (u x₀ y₀ p q) x y =
      (Nat.factorial p : ℝ) * (Nat.factorial q : ℝ) := by
  intro x y
  unfold mixedOrder partialYOrder
  have h :
      (fun t : ℝ => partialXOrder p (u x₀ y₀ p q) x t) =
        fun t : ℝ => (t - y₀) ^ q * (Nat.factorial p : ℝ) := by
    funext t
    simpa [mul_comm] using (gap1 x₀ y₀ p q x t)
  rw [h]
  simpa [mul_comm] using
    (iterDerivSubPowMul y₀ q (Nat.factorial p : ℝ) y)

end

end ProofGap.Exercise3262

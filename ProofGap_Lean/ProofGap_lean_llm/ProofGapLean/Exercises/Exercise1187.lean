import ProofGapLean.Prelude.Finite
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise1187

noncomputable section

open scoped BigOperators

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def P (n : ℕ) (c : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), c k * x ^ (n - k)

def firstClosed (n : ℕ) (c : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n,
    c k * (n - k : ℕ) * x ^ (n - k - 1)

def secondClosed (n : ℕ) (c : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n - 1),
    c k * (n - k : ℕ) * (n - k - 1 : ℕ) * x ^ (n - k - 2)

def y (n : ℕ) (c : ℕ → ℝ) (a b x : ℝ) : ℝ :=
  P n c (a * x + b)

private theorem hasDerivAt_P (n : ℕ) (c : ℕ → ℝ) (x : ℝ) :
    HasDerivAt (P n c)
      (∑ k ∈ Finset.range (n + 1),
        c k * (n - k : ℕ) * x ^ (n - k - 1)) x := by
  unfold P
  have h :
      HasDerivAt
        (∑ k ∈ Finset.range (n + 1),
          fun z : ℝ => c k * z ^ (n - k))
        (∑ k ∈ Finset.range (n + 1),
          c k * (n - k : ℕ) * x ^ (n - k - 1)) x := by
    apply HasDerivAt.sum
    intro k hk
    simpa [mul_assoc] using
      (((hasDerivAt_id x).pow (n - k)).const_mul (c k))
  have hfun :
      (fun z : ℝ => ∑ k ∈ Finset.range (n + 1),
        c k * z ^ (n - k)) =
      (∑ k ∈ Finset.range (n + 1),
        fun z : ℝ => c k * z ^ (n - k)) := by
    funext z
    simp only [Finset.sum_apply]
  rw [hfun]
  exact h

private theorem firstClosed_eq_P_pred (n : ℕ) (c : ℕ → ℝ) :
    firstClosed n c = P (n - 1) (fun k => c k * (n - k : ℕ)) := by
  funext x
  cases n with
  | zero => simp [firstClosed, P]
  | succ n =>
      simp only [firstClosed, P, Nat.succ_sub_one]
      apply Finset.sum_congr rfl
      intro k hk
      have hpow : n + 1 - k - 1 = n - k := by omega
      rw [hpow]

private theorem firstClosed_pred_eq_second
    (n : ℕ) (c : ℕ → ℝ) (x : ℝ) :
    firstClosed (n - 1) (fun k => c k * (n - k : ℕ)) x =
      secondClosed n c x := by
  unfold firstClosed secondClosed
  apply Finset.sum_congr rfl
  intro k hk
  have h₁ : n - 1 - k = n - k - 1 := by omega
  have h₂ : n - 1 - k - 1 = n - k - 2 := by omega
  rw [h₂, h₁]

private theorem iterDeriv_succ (n : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    iterDeriv (n + 1) f x = iterDeriv n (deriv f) x := by
  simp only [iterDeriv, Function.iterate_succ_apply]

private theorem deriv_affine_P_succ
    (n : ℕ) (c : ℕ → ℝ) (a b x : ℝ) :
    deriv (fun z : ℝ => P (n + 1) c (a * z + b)) x =
      P n (fun k => c k * (n + 1 - k : ℕ) * a) (a * x + b) := by
  have haff : HasDerivAt (fun z : ℝ => a * z + b) a x := by
    simpa using ((hasDerivAt_id x).const_mul a).add_const b
  have hcomp :=
    (hasDerivAt_P (n + 1) c (a * x + b)).comp x haff
  have hd :
      deriv (fun z : ℝ => P (n + 1) c (a * z + b)) x =
        (∑ k ∈ Finset.range ((n + 1) + 1),
          c k * (n + 1 - k : ℕ) *
            (a * x + b) ^ (n + 1 - k - 1)) * a := by
    simpa [Function.comp_def] using hcomp.deriv
  rw [hd]
  calc
    (∑ k ∈ Finset.range ((n + 1) + 1),
        c k * (n + 1 - k : ℕ) *
          (a * x + b) ^ (n + 1 - k - 1)) * a =
        (∑ k ∈ Finset.range (n + 1),
          c k * (n + 1 - k : ℕ) *
            (a * x + b) ^ (n + 1 - k - 1)) * a := by
          rw [Finset.sum_range_succ]
          simp
    _ = ∑ k ∈ Finset.range (n + 1),
          (c k * (n + 1 - k : ℕ) *
            (a * x + b) ^ (n + 1 - k - 1)) * a := by
          rw [Finset.sum_mul]
    _ = P n (fun k => c k * (n + 1 - k : ℕ) * a) (a * x + b) := by
          unfold P
          apply Finset.sum_congr rfl
          intro k hk
          have hpow : n + 1 - k - 1 = n - k := by omega
          rw [hpow]
          ring

private theorem iterDeriv_affine_P_closed
    (n : ℕ) (c : ℕ → ℝ) (a b x : ℝ) :
    iterDeriv n (fun z : ℝ => P n c (a * z + b)) x =
      a ^ n * (Nat.factorial n : ℝ) * c 0 := by
  induction n generalizing c with
  | zero =>
      simp [iterDeriv, P]
  | succ n ih =>
      rw [iterDeriv_succ]
      have hfun :
          deriv (fun z : ℝ => P (n + 1) c (a * z + b)) =
            fun z : ℝ =>
              P n (fun k => c k * (n + 1 - k : ℕ) * a) (a * z + b) := by
        funext z
        exact deriv_affine_P_succ n c a b z
      rw [hfun]
      rw [ih (fun k => c k * (n + 1 - k : ℕ) * a)]
      simp only [Nat.sub_zero, Nat.factorial_succ, Nat.cast_mul, pow_succ]
      ring

theorem gap1 (n : ℕ) (c : ℕ → ℝ) (x : ℝ) :
    iterDeriv 1 (P n c) x = firstClosed n c x := by
  simpa [iterDeriv, firstClosed, Finset.sum_range_succ] using
    (hasDerivAt_P n c x).deriv

theorem gap2 (n : ℕ) (c : ℕ → ℝ) (x : ℝ) :
    iterDeriv 2 (P n c) x = secondClosed n c x := by
  change deriv (deriv (P n c)) x = secondClosed n c x
  have hderiv : deriv (P n c) = firstClosed n c := by
    funext z
    simpa [iterDeriv] using (gap1 n c z)
  calc
    deriv (deriv (P n c)) x = deriv (firstClosed n c) x := by rw [hderiv]
    _ = deriv (P (n - 1) (fun k => c k * (n - k : ℕ))) x := by
      rw [firstClosed_eq_P_pred]
    _ = firstClosed (n - 1) (fun k => c k * (n - k : ℕ)) x := by
      simpa [iterDeriv] using
        (gap1 (n - 1) (fun k => c k * (n - k : ℕ)) x)
    _ = secondClosed n c x := firstClosed_pred_eq_second n c x

theorem gap3 (n : ℕ) (c : ℕ → ℝ) (x : ℝ) :
    iterDeriv n (P n c) x = (Nat.factorial n : ℝ) * c 0 := by
  simpa using (iterDeriv_affine_P_closed n c 1 0 x)

theorem gap4 (n : ℕ) (c : ℕ → ℝ) (a b x : ℝ) :
    iterDeriv n (y n c a b) x =
      iterDeriv n (fun z : ℝ => P n c (a * z + b)) x := by
  rfl

theorem gap5 (n : ℕ) (c : ℕ → ℝ) (a b x : ℝ) :
    iterDeriv n (fun z : ℝ => P n c (a * z + b)) x =
      a ^ n * iterDeriv n (P n c) (a * x + b) := by
  simpa [gap3, mul_assoc] using
    (iterDeriv_affine_P_closed n c a b x)

theorem gap6 (n : ℕ) (c : ℕ → ℝ) (a b x : ℝ) :
    a ^ n * iterDeriv n (P n c) (a * x + b) =
      a ^ n * (Nat.factorial n : ℝ) * c 0 := by
  simp [gap3, mul_assoc]

theorem gap7 (n : ℕ) (c : ℕ → ℝ) (a b x : ℝ) :
    iterDeriv n (y n c a b) x =
      a ^ n * (Nat.factorial n : ℝ) * c 0 := by
  simpa [y] using (iterDeriv_affine_P_closed n c a b x)

theorem gap8 (n : ℕ) (c : ℕ → ℝ) (a b x : ℝ) :
    iterDeriv n (y n c a b) x =
      (Nat.factorial n : ℝ) * c 0 * a ^ n := by
  rw [gap7]
  ring

end

end ProofGap.Exercise1187

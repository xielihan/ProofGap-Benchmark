import ProofGapLean.Prelude.Finite
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise1024_2

noncomputable section

open scoped BigOperators

def Pbar (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, x ^ (k + 1)

def P (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, (k + 1 : ℝ) * x ^ k

def Qbar (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, (k + 1 : ℝ) * x ^ (k + 1)

def Q (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, (k + 1 : ℝ) ^ 2 * x ^ k

def closedP (n : ℕ) (x : ℝ) : ℝ :=
  (1 - (n + 1 : ℝ) * x ^ n + (n : ℝ) * x ^ (n + 1)) /
    (1 - x) ^ 2

def explicitDerivativeP (n : ℕ) (x : ℝ) : ℝ :=
  ((-(n : ℝ) * (n + 1 : ℝ) * x ^ (n - 1) +
        (n : ℝ) * (n + 1 : ℝ) * x ^ n) *
        (1 - x) ^ 2 +
      2 * (1 - x) *
        (1 - (n + 1 : ℝ) * x ^ n + (n : ℝ) * x ^ (n + 1))) /
    (1 - x) ^ 4

def closedQ (n : ℕ) (x : ℝ) : ℝ :=
  (1 + x - (n + 1 : ℝ) ^ 2 * x ^ n +
      (2 * (n : ℝ) ^ 2 + 2 * n - 1) * x ^ (n + 1) -
      (n : ℝ) ^ 2 * x ^ (n + 2)) /
    (1 - x) ^ 3

private theorem p_eq_closed (n : ℕ) (x : ℝ) (hx : x ≠ 1) :
    P n x = closedP n x := by
  induction n with
  | zero =>
      norm_num [P, closedP]
  | succ n ih =>
      have hstep :
          P (n + 1) x = P n x + (n + 1 : ℝ) * x ^ n := by
        simp [P, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
      rw [hstep, ih]
      unfold closedP
      field_simp [sub_ne_zero.mpr (Ne.symm hx)]
      simp only [Nat.cast_add, Nat.cast_one, pow_succ]
      ring

theorem gap1 (n : ℕ) (x : ℝ) :
    HasDerivAt (Pbar n) (P n x) x := by
  induction n with
  | zero =>
      simpa [Pbar, P] using (hasDerivAt_const x (0 : ℝ))
  | succ n ih =>
      have hfun :
          Pbar (n + 1) = Pbar n + fun y : ℝ => y ^ (n + 1) := by
        funext y
        simp [Pbar, Finset.sum_range_succ]
      rw [hfun]
      simpa [P, Finset.sum_range_succ, Nat.cast_add,
        Nat.cast_one] using
          ih.add (hasDerivAt_pow (n + 1) x)

theorem gap2 (n : ℕ) (x : ℝ) :
    (∑ k ∈ Finset.range n, (k + 1 : ℝ) * x ^ k) = P n x := by
  rfl

theorem gap3 (n : ℕ) (x : ℝ) :
    HasDerivAt (Pbar n) (P n x) x := by
  exact gap1 n x

theorem gap4 (n : ℕ) (x : ℝ) :
    HasDerivAt (Qbar n) (Q n x) x := by
  induction n with
  | zero =>
      simpa [Qbar, Q] using (hasDerivAt_const x (0 : ℝ))
  | succ n ih =>
      have hfun :
          Qbar (n + 1) =
            Qbar n + fun y : ℝ => (n + 1 : ℝ) * y ^ (n + 1) := by
        funext y
        simp [Qbar, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
      rw [hfun]
      simpa [Q, Finset.sum_range_succ, Nat.cast_add,
        Nat.cast_one, pow_two, mul_assoc] using
          ih.add ((hasDerivAt_pow (n + 1) x).const_mul (n + 1 : ℝ))

theorem gap5 (n : ℕ) (x : ℝ) :
    (∑ k ∈ Finset.range n, (k + 1 : ℝ) ^ 2 * x ^ k) = Q n x := by
  rfl

theorem gap6 (n : ℕ) (x : ℝ) :
    HasDerivAt (Qbar n) (Q n x) x := by
  exact gap4 n x

theorem gap7 (n : ℕ) (x : ℝ) :
    Qbar n x = x * P n x := by
  unfold Qbar P
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp [pow_succ, mul_assoc, mul_comm]

theorem gap8 (n : ℕ) (x : ℝ) :
    x * (∑ k ∈ Finset.range n, (k + 1 : ℝ) * x ^ k) =
      x * P n x := by
  rw [gap2]

theorem gap9 (n : ℕ) (x : ℝ) :
    Qbar n x = x * P n x := by
  exact gap7 n x

theorem gap10 (n : ℕ) (x : ℝ) :
    HasDerivAt (fun z => z * P n z) (Q n x) x := by
  have hfun : Qbar n = (fun z : ℝ => z * P n z) :=
    funext (gap9 n)
  rw [← hfun]
  exact gap6 n x

theorem gap11 (n : ℕ) (x : ℝ) :
    P n x + x * deriv (P n) x = Q n x := by
  have hP : DifferentiableAt ℝ (P n) x := by
    induction n with
    | zero =>
        change DifferentiableAt ℝ (fun _ : ℝ => 0) x
        exact (hasDerivAt_const x (0 : ℝ)).differentiableAt
    | succ n ih =>
        have hfun :
            P (n + 1) = P n + fun y : ℝ => (n + 1 : ℝ) * y ^ n := by
          funext y
          simp [P, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
        rw [hfun]
        exact ih.add
          ((hasDerivAt_pow n x).const_mul (n + 1 : ℝ)).differentiableAt
  have hprod :
      HasDerivAt (fun z : ℝ => z * P n z)
        (P n x + x * deriv (P n) x) x := by
    simpa using (hasDerivAt_id x).mul hP.hasDerivAt
  exact hprod.unique (gap10 n x)

theorem gap12 (n : ℕ) (x : ℝ) (hx : x ≠ 1) :
    deriv (P n) x = deriv (closedP n) x := by
  have h : P n =ᶠ[nhds x] closedP n :=
    (eventually_ne_nhds hx).mono (fun y hy => p_eq_closed n y hy)
  exact h.deriv_eq

theorem gap13 (n : ℕ) (x : ℝ) (hx : x ≠ 1) :
    deriv (P n) x = explicitDerivativeP n x := by
  have hnum :
      HasDerivAt
        (fun z : ℝ =>
          1 - (n + 1 : ℝ) * z ^ n + (n : ℝ) * z ^ (n + 1))
        (-(n : ℝ) * (n + 1 : ℝ) * x ^ (n - 1) +
          (n : ℝ) * (n + 1 : ℝ) * x ^ n) x := by
    convert
      (((hasDerivAt_const x (1 : ℝ)).sub
          ((hasDerivAt_pow n x).const_mul (n + 1 : ℝ))).add
        ((hasDerivAt_pow (n + 1) x).const_mul (n : ℝ))) using 1 <;>
      try rfl
    simp only [Nat.cast_add, Nat.cast_one]
    simp [Nat.add_comm] <;> ring
  have hden :
      HasDerivAt (fun z : ℝ => (1 - z) ^ 2) (-2 * (1 - x)) x := by
    convert
      (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).pow 2) using 1 <;>
      try rfl
    norm_num [pow_succ]
  have hclosed :
      HasDerivAt (closedP n) (explicitDerivativeP n x) x := by
    change HasDerivAt
      (fun z : ℝ =>
        (1 - (n + 1 : ℝ) * z ^ n + (n : ℝ) * z ^ (n + 1)) /
          (1 - z) ^ 2)
      (explicitDerivativeP n x) x
    convert hnum.div hden
      (pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm hx))) using 1 <;>
      try rfl
    unfold explicitDerivativeP
    ring
  calc
    deriv (P n) x = deriv (closedP n) x := gap12 n x hx
    _ = explicitDerivativeP n x := hclosed.deriv

theorem gap14 (n : ℕ) (x : ℝ) (hx : x ≠ 1) :
    Q n x = closedQ n x := by
  have h1 : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  calc
    Q n x = P n x + x * deriv (P n) x := (gap11 n x).symm
    _ = closedP n x + x * explicitDerivativeP n x := by
      rw [p_eq_closed n x hx, gap13 n x hx]
    _ = closedQ n x := by
      cases n with
      | zero =>
          norm_num [closedP, explicitDerivativeP, closedQ] <;> ring
      | succ n =>
          unfold closedP explicitDerivativeP closedQ
          field_simp [h1] <;>
            simp [Nat.cast_succ, pow_succ] <;> ring

end

end ProofGap.Exercise1024_2

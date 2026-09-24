import ProofGapLean.Prelude.Finite
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1024_1

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

def geometricForm (n : ℕ) (x : ℝ) : ℝ :=
  x * (1 - x ^ n) / (1 - x)

def closedP (n : ℕ) (x : ℝ) : ℝ :=
  (1 - (n + 1 : ℝ) * x ^ n + (n : ℝ) * x ^ (n + 1)) /
    (1 - x) ^ 2

private theorem weightedGeometricClosed (n : ℕ) (x : ℝ) (hx : x ≠ 1) :
    P n x = closedP n x := by
  have hx' : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  induction n with
  | zero =>
      simp [P, closedP]
  | succ n ih =>
      rw [P, Finset.sum_range_succ]
      change P n x + (n + 1 : ℝ) * x ^ n = closedP (n + 1) x
      rw [ih]
      unfold closedP
      field_simp [hx']
      simp [pow_succ]
      ring

private theorem hasDerivAtGeometricClosed (n : ℕ) (x : ℝ) (hx : x ≠ 1) :
    HasDerivAt (geometricForm n) (closedP n x) x := by
  cases n with
  | zero =>
      have hf : geometricForm 0 = fun _ : ℝ => 0 := by
        funext y
        simp [geometricForm]
      have hc : closedP 0 x = 0 := by
        simp [closedP]
      rw [hf, hc]
      exact hasDerivAt_const x (0 : ℝ)
  | succ n =>
      have hx' : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
      have h :=
        (((hasDerivAt_id x).mul
          ((hasDerivAt_const x (1 : ℝ)).sub
            (hasDerivAt_pow (n + 1) x))).div
          ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)) hx')
      convert h using 1 <;> try rfl
      unfold closedP
      field_simp [hx'] <;> simp [pow_succ] <;> ring

theorem gap1 (n : ℕ) (x : ℝ) :
    HasDerivAt (Pbar n) (P n x) x := by
  induction n with
  | zero =>
      simpa [Pbar, P] using (hasDerivAt_const x (0 : ℝ))
  | succ n ih =>
      have hp : HasDerivAt (fun y : ℝ => y ^ (n + 1))
          ((n + 1 : ℝ) * x ^ n) x := by
        simpa using (hasDerivAt_pow (n + 1) x)
      have hfun : Pbar (n + 1) = Pbar n + fun y : ℝ => y ^ (n + 1) := by
        funext y
        simp [Pbar, Finset.sum_range_succ]
      rw [hfun]
      simpa [P, Finset.sum_range_succ] using ih.add hp

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
      have hp : HasDerivAt (fun y : ℝ => y ^ (n + 1))
          ((n + 1 : ℝ) * x ^ n) x := by
        simpa using (hasDerivAt_pow (n + 1) x)
      have hc : HasDerivAt (fun _ : ℝ => (n + 1 : ℝ)) 0 x :=
        hasDerivAt_const x (n + 1 : ℝ)
      have hterm :
          HasDerivAt (fun y : ℝ => (n + 1 : ℝ) * y ^ (n + 1))
            ((n + 1 : ℝ) ^ 2 * x ^ n) x := by
        simpa [pow_two, mul_assoc] using hc.mul hp
      have hfun :
          Qbar (n + 1) = Qbar n +
            fun y : ℝ => (n + 1 : ℝ) * y ^ (n + 1) := by
        funext y
        simp [Qbar, Finset.sum_range_succ]
      rw [hfun]
      simpa [Q, Finset.sum_range_succ] using ih.add hterm

theorem gap5 (n : ℕ) (x : ℝ) :
    (∑ k ∈ Finset.range n, (k + 1 : ℝ) ^ 2 * x ^ k) = Q n x := by
  rfl

theorem gap6 (n : ℕ) (x : ℝ) :
    HasDerivAt (Qbar n) (Q n x) x := by
  exact gap4 n x

theorem gap7 (n : ℕ) (x : ℝ) (hx : x ≠ 1) :
    Pbar n x = geometricForm n x := by
  have hx' : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  induction n with
  | zero =>
      simp [Pbar, geometricForm]
  | succ n ih =>
      rw [Pbar, Finset.sum_range_succ]
      change Pbar n x + x ^ (n + 1) = geometricForm (n + 1) x
      rw [ih]
      unfold geometricForm
      field_simp [hx']
      rw [pow_succ]
      ring

theorem gap8 (n : ℕ) (x : ℝ) (hx : x ≠ 1) :
    HasDerivAt (geometricForm n) (P n x) x := by
  have hp := weightedGeometricClosed n x hx
  rw [hp]
  exact hasDerivAtGeometricClosed n x hx

theorem gap9 (n : ℕ) (x : ℝ) (hx : x ≠ 1) :
    P n x = closedP n x := by
  exact weightedGeometricClosed n x hx

end

end ProofGap.Exercise1024_1

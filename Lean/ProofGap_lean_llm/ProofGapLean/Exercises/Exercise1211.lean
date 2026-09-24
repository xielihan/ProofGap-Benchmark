import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import ProofGapLean.Prelude.Finite
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise1211

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ := (deriv^[n]) f
def y (n : ℕ) (x : ℝ) : ℝ := x ^ n * Real.exp x

def closedForm (n : ℕ) (x : ℝ) : ℝ :=
  Real.exp x *
    ∑ k ∈ Finset.range (n + 1),
      (Nat.choose n k : ℝ) *
        ((Nat.factorial n : ℝ) / (Nat.factorial (n - k) : ℝ)) * x ^ (n - k)

def nthDifferential (n : ℕ) (f : ℝ → ℝ) (x dx : ℝ) : ℝ :=
  iterDeriv n f x * dx ^ n

private theorem iterDeriv_y_closedForm (n : ℕ) (x : ℝ) :
    iterDeriv n (y n) x = closedForm n x := by
  classical
  let A (k : ℕ) (z : ℝ) : ℝ :=
    (Nat.factorial n : ℝ) / (Nat.factorial (n - k) : ℝ) * z ^ (n - k)
  let F (m : ℕ) (z : ℝ) : ℝ :=
    Real.exp z *
      ∑ k ∈ Finset.range (m + 1), (Nat.choose m k : ℝ) * A k z
  have hbin (m : ℕ) (a : ℕ → ℝ) :
      (∑ k ∈ Finset.range (m + 2), (Nat.choose (m + 1) k : ℝ) * a k) =
        (∑ k ∈ Finset.range (m + 1), (Nat.choose m k : ℝ) * a k) +
          ∑ k ∈ Finset.range (m + 1), (Nat.choose m k : ℝ) * a (k + 1) := by
    have hU :
        (∑ k ∈ Finset.range (m + 1),
            (Nat.choose m (k + 1) : ℝ) * a (k + 1)) =
          ∑ k ∈ Finset.range m,
            (Nat.choose m (k + 1) : ℝ) * a (k + 1) := by
      rw [Finset.sum_range_succ]
      simp
    have hS :
        (∑ k ∈ Finset.range (m + 1), (Nat.choose m k : ℝ) * a k) =
          a 0 + ∑ k ∈ Finset.range m,
            (Nat.choose m (k + 1) : ℝ) * a (k + 1) := by
      rw [Finset.sum_range_succ']
      simp [add_comm]
    have hpas :
        (∑ k ∈ Finset.range (m + 1),
            (Nat.choose (m + 1) (k + 1) : ℝ) * a (k + 1)) =
          ∑ k ∈ Finset.range (m + 1),
            ((Nat.choose m k : ℝ) + (Nat.choose m (k + 1) : ℝ)) *
              a (k + 1) := by
      apply Finset.sum_congr rfl
      intro k hk
      simp [Nat.choose_succ_succ]
    rw [Finset.sum_range_succ']
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul]
    rw [hpas]
    simp only [add_mul, Finset.sum_add_distrib]
    rw [hU, hS]
    ring
  have hpow (q : ℕ) (z : ℝ) :
      HasDerivAt (fun w : ℝ => w ^ q) ((q : ℝ) * z ^ (q - 1)) z := by
    induction q with
    | zero =>
        simpa using (hasDerivAt_const (x := z) (c := (1 : ℝ)))
    | succ q ih =>
        cases q with
        | zero =>
            simpa using (hasDerivAt_id z)
        | succ q =>
            have hp := ih.mul (hasDerivAt_id z)
            convert hp using 1 <;> simp [pow_succ] <;> ring
  have hA (k : ℕ) (hk : k < n) (z : ℝ) :
      HasDerivAt (A k) (A (k + 1) z) z := by
    have hsub : n - k = n - (k + 1) + 1 := by omega
    have hexp : n - k - 1 = n - (k + 1) := by omega
    have hcoef :
        ((Nat.factorial n : ℝ) / (Nat.factorial (n - k) : ℝ)) *
            (((n - k : ℕ) : ℝ)) =
          (Nat.factorial n : ℝ) /
            (Nat.factorial (n - (k + 1)) : ℝ) := by
      rw [hsub, Nat.factorial_succ]
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      field_simp
    have hp := hpow (n - k) z
    have hc := hp.const_mul
      ((Nat.factorial n : ℝ) / (Nat.factorial (n - k) : ℝ))
    dsimp [A]
    convert hc using 1
    rw [hexp, ← mul_assoc, hcoef]
  have hF (m : ℕ) (hm : m < n) : deriv (F m) = F (m + 1) := by
    funext z
    have hs0 :
        HasDerivAt
          (∑ k ∈ Finset.range (m + 1),
            fun w : ℝ => (Nat.choose m k : ℝ) * A k w)
          (∑ k ∈ Finset.range (m + 1),
            (Nat.choose m k : ℝ) * A (k + 1) z) z := by
      apply HasDerivAt.sum
      intro k hk
      exact (hA k (by
        have hk' : k < m + 1 := Finset.mem_range.mp hk
        omega) z).const_mul (Nat.choose m k : ℝ)
    have hfun :
        (∑ k ∈ Finset.range (m + 1),
            fun w : ℝ => (Nat.choose m k : ℝ) * A k w) =
          (fun w : ℝ => ∑ k ∈ Finset.range (m + 1),
            (Nat.choose m k : ℝ) * A k w) := by
      funext w
      simp
    have hs :
        HasDerivAt
          (fun w => ∑ k ∈ Finset.range (m + 1),
            (Nat.choose m k : ℝ) * A k w)
          (∑ k ∈ Finset.range (m + 1),
            (Nat.choose m k : ℝ) * A (k + 1) z) z := by
      rw [← hfun]
      exact hs0
    have hp := (Real.hasDerivAt_exp z).mul hs
    calc
      deriv (F m) z =
          Real.exp z *
              (∑ k ∈ Finset.range (m + 1),
                (Nat.choose m k : ℝ) * A k z) +
            Real.exp z *
              ∑ k ∈ Finset.range (m + 1),
                (Nat.choose m k : ℝ) * A (k + 1) z := by
            simpa [F] using hp.deriv
      _ = F (m + 1) z := by
            dsimp [F]
            rw [hbin m (fun k => A k z)]
            ring
  have hiter : ∀ m : ℕ, m ≤ n → (deriv^[m]) (y n) = F m := by
    intro m hm
    induction m with
    | zero =>
        funext z
        simp [F, A, y, Nat.factorial_ne_zero, mul_comm]
    | succ m ih =>
        rw [Function.iterate_succ_apply']
        rw [ih (Nat.le_of_succ_le hm)]
        exact hF m (Nat.lt_of_succ_le hm)
  have h := congrFun (hiter n le_rfl) x
  simpa [iterDeriv, closedForm, F, A, mul_assoc] using h

theorem gap1 (n : ℕ) (x dx : ℝ) :
    nthDifferential n (y n) x dx = iterDeriv n (y n) x * dx ^ n := by
  rfl

theorem gap2 (n : ℕ) (x dx : ℝ) :
    iterDeriv n (y n) x * dx ^ n = closedForm n x * dx ^ n := by
  rw [iterDeriv_y_closedForm n x]

theorem gap3 (n : ℕ) (x dx : ℝ) :
    nthDifferential n (y n) x dx = closedForm n x * dx ^ n := by
  rw [gap1, gap2]

end

end ProofGap.Exercise1211

import ProofGapLean.Prelude.Analysis
import ProofGapLean.Exercises.Exercise1230
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2874_1

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def exponentialIncrementTerm (x h : ℝ) (n : ℕ) : ℝ :=
  (2 * x * h + h ^ 2) ^ (n + 1) / (Nat.factorial (n + 1) : ℝ)

def rawTaylorCoefficient (x : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n / 2 + 1),
    (2 * x) ^ (n - 2 * k) /
      ((Nat.factorial k : ℝ) * (Nat.factorial (n - 2 * k) : ℝ))

def derivativePolynomial (x : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n / 2 + 1),
    (Nat.factorial n : ℝ) /
        ((Nat.factorial k : ℝ) * (Nat.factorial (n - 2 * k) : ℝ)) *
      (2 * x) ^ (n - 2 * k)

def taylorCoefficient (f : ℝ → ℝ) (x : ℝ) (n : ℕ) : ℝ :=
  iterDeriv n f x / (Nat.factorial n : ℝ)

private theorem derivativePolynomial_eq_factorial_mul_raw
    (x : ℝ) (n : ℕ) :
    derivativePolynomial x n =
      (Nat.factorial n : ℝ) * rawTaylorCoefficient x n := by
  unfold derivativePolynomial rawTaylorCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

private theorem iterDeriv_exp_sq (x : ℝ) (n : ℕ) :
    iterDeriv n (fun t : ℝ => Real.exp (t ^ 2)) x =
      Real.exp (x ^ 2) * derivativePolynomial x n := by
  have h := ProofGap.Exercise1230.gap7 Real.exp n x
    (Real.contDiff_exp.contDiffAt : ContDiffAt ℝ n Real.exp (x ^ 2))
  simpa [iterDeriv, derivativePolynomial,
    ProofGap.Exercise1230.iterDeriv, ProofGap.Exercise1230.y,
    ProofGap.Exercise1230.compositionSum, ProofGap.Exercise1230.coefficient,
    Real.iter_deriv_exp, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] using h

theorem gap1
    (f : ℝ → ℝ) (hf : ∀ x, f x = Real.exp (x ^ 2)) :
    ∀ x h : ℝ,
      f (x + h) - f x = Real.exp ((x + h) ^ 2) - Real.exp (x ^ 2) := by
  intro x h
  rw [hf (x + h), hf x]

theorem gap2
    (f : ℝ → ℝ) (hf : ∀ x, f x = Real.exp (x ^ 2))
    (hincrement :
      ∀ x h : ℝ,
        f (x + h) - f x = Real.exp ((x + h) ^ 2) - Real.exp (x ^ 2)) :
    ∀ x h : ℝ,
      Real.exp ((x + h) ^ 2) - Real.exp (x ^ 2) =
        Real.exp (x ^ 2) * (Real.exp (2 * x * h + h ^ 2) - 1) := by
  intro x h
  rw [show (x + h) ^ 2 = x ^ 2 + (2 * x * h + h ^ 2) by ring,
    Real.exp_add]
  ring

theorem gap3
    (f : ℝ → ℝ) (hf : ∀ x, f x = Real.exp (x ^ 2))
    (hincrement :
      ∀ x h : ℝ,
        f (x + h) - f x = Real.exp ((x + h) ^ 2) - Real.exp (x ^ 2))
    (hfactor :
      ∀ x h : ℝ,
        Real.exp ((x + h) ^ 2) - Real.exp (x ^ 2) =
          Real.exp (x ^ 2) * (Real.exp (2 * x * h + h ^ 2) - 1)) :
    ∀ x h : ℝ,
      f (x + h) - f x =
        Real.exp (x ^ 2) * (Real.exp (2 * x * h + h ^ 2) - 1) := by
  intro x h
  rw [hincrement x h, hfactor x h]

theorem gap4
    (f : ℝ → ℝ) (hf : ∀ x, f x = Real.exp (x ^ 2))
    (hfactor :
      ∀ x h : ℝ,
        f (x + h) - f x =
          Real.exp (x ^ 2) * (Real.exp (2 * x * h + h ^ 2) - 1)) :
    ∀ x h : ℝ,
      f (x + h) - f x =
        Real.exp (x ^ 2) * (∑' n, exponentialIncrementTerm x h n) := by
  intro x h
  rw [hfactor x h]
  congr 1
  let u : ℝ := 2 * x * h + h ^ 2
  have hexp : HasSum (fun n : ℕ => u ^ n / (Nat.factorial n : ℝ))
      (Real.exp u) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp u
  have htail := (hasSum_nat_add_iff' 1).2 hexp
  exact (by
    simpa [u, exponentialIncrementTerm] using htail.tsum_eq.symm)

theorem gap5
    (f : ℝ → ℝ) (hf : ∀ x, f x = Real.exp (x ^ 2))
    (hseries :
      ∀ x h : ℝ,
        f (x + h) - f x =
          Real.exp (x ^ 2) * (∑' n, exponentialIncrementTerm x h n)) :
    ∀ x : ℝ, ∀ n : ℕ, 1 ≤ n →
      taylorCoefficient f x n = Real.exp (x ^ 2) * rawTaylorCoefficient x n := by
  intro x n hn
  have heq : f = fun t : ℝ => Real.exp (t ^ 2) := funext hf
  subst f
  rw [taylorCoefficient, iterDeriv_exp_sq,
    derivativePolynomial_eq_factorial_mul_raw]
  have hfac : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  field_simp

theorem gap6
    (f : ℝ → ℝ) (hf : ∀ x, f x = Real.exp (x ^ 2))
    (hcoefficient :
      ∀ x : ℝ, ∀ n : ℕ, 1 ≤ n →
        taylorCoefficient f x n =
          Real.exp (x ^ 2) * rawTaylorCoefficient x n) :
    ∀ x : ℝ, ∀ n : ℕ, 1 ≤ n →
      taylorCoefficient f x n =
        Real.exp (x ^ 2) / (Nat.factorial n : ℝ) *
          derivativePolynomial x n := by
  intro x n hn
  rw [hcoefficient x n hn, derivativePolynomial_eq_factorial_mul_raw]
  have hfac : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  field_simp

theorem gap7
    (f : ℝ → ℝ) (hf : ∀ x, f x = Real.exp (x ^ 2))
    (hscaled :
      ∀ x : ℝ, ∀ n : ℕ, 1 ≤ n →
        taylorCoefficient f x n =
          Real.exp (x ^ 2) / (Nat.factorial n : ℝ) *
            derivativePolynomial x n) :
    ∀ n : ℕ, ∀ x : ℝ, 1 ≤ n →
      iterDeriv n f x = Real.exp (x ^ 2) * derivativePolynomial x n := by
  intro n x hn
  have hs := hscaled x n hn
  unfold taylorCoefficient at hs
  have hfac : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  field_simp [hfac] at hs
  exact hs

end

end ProofGap.Exercise2874_1

import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring

namespace ProofGap.Exercise2879

noncomputable section

open scoped BigOperators

def expTerm (x : ℝ) (n : ℕ) : ℝ :=
  x ^ n / (Nat.factorial n : ℝ)

def productTerm (x y : ℝ) (n₁ n₂ : ℕ) : ℝ :=
  x ^ n₁ * y ^ n₂ /
    ((Nat.factorial n₁ : ℝ) * (Nat.factorial n₂ : ℝ))

def diagonalProductTerm (x y : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), productTerm x y k (n - k)

def binomialTerm (x y : ℝ) (n : ℕ) : ℝ :=
  (1 / (Nat.factorial n : ℝ)) *
    ∑ k ∈ Finset.range (n + 1),
      (Nat.choose n k : ℝ) * x ^ k * y ^ (n - k)

private theorem expTerm_hasSum (x : ℝ) :
    HasSum (expTerm x) (Real.exp x) := by
  simpa [expTerm, Real.exp_eq_exp_ℝ] using
    (NormedSpace.expSeries_div_hasSum_exp (x : ℝ))

private theorem expTerm_norm_summable (x : ℝ) :
    Summable (fun n => ‖expTerm x n‖) := by
  simpa [expTerm] using
    (NormedSpace.norm_expSeries_div_summable (x : ℝ))

private theorem expTerm_mul_expTerm_eq_productTerm
    (x y : ℝ) (n₁ n₂ : ℕ) :
    expTerm x n₁ * expTerm y n₂ = productTerm x y n₁ n₂ := by
  simp only [expTerm, productTerm]
  ring

private theorem tsum_expTerm_mul_eq_diagonal (x y : ℝ) :
    (∑' n, expTerm x n) * (∑' n, expTerm y n) =
      ∑' n, diagonalProductTerm x y n := by
  calc
    (∑' n, expTerm x n) * (∑' n, expTerm y n) =
        ∑' n, ∑ k ∈ Finset.range (n + 1),
          expTerm x k * expTerm y (n - k) :=
      tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm
        (expTerm_norm_summable x) (expTerm_norm_summable y)
    _ = ∑' n, diagonalProductTerm x y n := by
      apply tsum_congr
      intro n
      rw [diagonalProductTerm]
      apply Finset.sum_congr rfl
      intro k hk
      exact expTerm_mul_expTerm_eq_productTerm x y k (n - k)

private theorem binomialTerm_eq_expTerm (x y : ℝ) (n : ℕ) :
    binomialTerm x y n = expTerm (x + y) n := by
  have hsum :
      (∑ k ∈ Finset.range (n + 1),
          (Nat.choose n k : ℝ) * x ^ k * y ^ (n - k)) =
        ∑ k ∈ Finset.range (n + 1),
          x ^ k * y ^ (n - k) * (Nat.choose n k : ℝ) := by
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [binomialTerm, expTerm, hsum, ← add_pow]
  ring

private theorem diagonal_tsum_eq_expTerm_add (x y : ℝ) :
    (∑' n, diagonalProductTerm x y n) =
      ∑' n, expTerm (x + y) n := by
  calc
    (∑' n, diagonalProductTerm x y n) =
        (∑' n, expTerm x n) * (∑' n, expTerm y n) :=
      (tsum_expTerm_mul_eq_diagonal x y).symm
    _ = Real.exp x * Real.exp y := by
      rw [(expTerm_hasSum x).tsum_eq, (expTerm_hasSum y).tsum_eq]
    _ = Real.exp (x + y) := (Real.exp_add x y).symm
    _ = ∑' n, expTerm (x + y) n :=
      (expTerm_hasSum (x + y)).tsum_eq.symm

theorem gap1 (f : ℝ → ℝ) (hf : ∀ x, f x = ∑' n, expTerm x n) :
    ∀ x y, f x * f y =
      (∑' n₁, expTerm x n₁) * (∑' n₂, expTerm y n₂) := by
  intro x y
  rw [hf x, hf y]

theorem gap2 :
    ∀ x y : ℝ,
      (∑' n₁, expTerm x n₁) * (∑' n₂, expTerm y n₂) =
        ∑' n₁, ∑' n₂, productTerm x y n₁ n₂ := by
  intro x y
  calc
    (∑' n₁, expTerm x n₁) * (∑' n₂, expTerm y n₂) =
        ∑' n₁, expTerm x n₁ * (∑' n₂, expTerm y n₂) :=
      tsum_mul_right.symm
    _ = ∑' n₁, ∑' n₂, expTerm x n₁ * expTerm y n₂ := by
      apply tsum_congr
      intro n₁
      rw [tsum_mul_left]
    _ = ∑' n₁, ∑' n₂, productTerm x y n₁ n₂ := by
      apply tsum_congr
      intro n₁
      apply tsum_congr
      intro n₂
      exact expTerm_mul_expTerm_eq_productTerm x y n₁ n₂

theorem gap3 (f : ℝ → ℝ) (hf : ∀ x, f x = ∑' n, expTerm x n) :
    ∀ x y, f x * f y =
      ∑' n₁, ∑' n₂, productTerm x y n₁ n₂ := by
  intro x y
  exact (gap1 f hf x y).trans (gap2 x y)

theorem gap4 (f : ℝ → ℝ) (hf : ∀ x, f x = ∑' n, expTerm x n) :
    ∀ x y, f x * f y = ∑' n, diagonalProductTerm x y n := by
  intro x y
  exact (gap1 f hf x y).trans (tsum_expTerm_mul_eq_diagonal x y)

theorem gap5 :
    ∀ x y : ℝ,
      (∑' n, diagonalProductTerm x y n) =
        ∑' n, binomialTerm x y n := by
  intro x y
  exact (diagonal_tsum_eq_expTerm_add x y).trans
    (tsum_congr (binomialTerm_eq_expTerm x y)).symm

theorem gap6 (f : ℝ → ℝ) (hf : ∀ x, f x = ∑' n, expTerm x n) :
    ∀ x y, f x * f y = ∑' n, binomialTerm x y n := by
  intro x y
  exact (gap4 f hf x y).trans (gap5 x y)

theorem gap7 (f : ℝ → ℝ) (hf : ∀ x, f x = ∑' n, expTerm x n) :
    ∀ x y, f x * f y =
      ∑' n, (1 / (Nat.factorial n : ℝ)) *
        ∑ k ∈ Finset.range (n + 1),
          (Nat.choose n k : ℝ) * x ^ k * y ^ (n - k) := by
  intro x y
  simpa only [binomialTerm] using gap6 f hf x y

theorem gap8 :
    ∀ x y : ℝ,
      (∑' n, (1 / (Nat.factorial n : ℝ)) *
        ∑ k ∈ Finset.range (n + 1),
          (Nat.choose n k : ℝ) * x ^ k * y ^ (n - k)) =
      ∑' n, expTerm (x + y) n := by
  intro x y
  change (∑' n, binomialTerm x y n) = ∑' n, expTerm (x + y) n
  exact tsum_congr (binomialTerm_eq_expTerm x y)

theorem gap9 (f : ℝ → ℝ) (hf : ∀ x, f x = ∑' n, expTerm x n) :
    ∀ x y, (∑' n, expTerm (x + y) n) = f (x + y) := by
  intro x y
  exact (hf (x + y)).symm

theorem gap10 (f : ℝ → ℝ) (hf : ∀ x, f x = ∑' n, expTerm x n) :
    ∀ x y, f x * f y = f (x + y) := by
  intro x y
  exact (gap6 f hf x y).trans ((gap8 x y).trans (gap9 f hf x y))

theorem gap11 :
    ∀ x : ℝ, Summable (expTerm x) := by
  intro x
  exact (expTerm_hasSum x).summable

theorem gap12 :
    ∀ y : ℝ, Summable (expTerm y) := by
  intro y
  exact (expTerm_hasSum y).summable

theorem gap13 (f : ℝ → ℝ) (hf : ∀ x, f x = ∑' n, expTerm x n) :
    ∀ x, f x = Real.exp x := by
  intro x
  exact (hf x).trans (expTerm_hasSum x).tsum_eq

theorem gap14 (f : ℝ → ℝ) (hf : ∀ x, f x = ∑' n, expTerm x n) :
    ∀ x y, f x * f y = f (x + y) := by
  exact gap10 f hf

theorem gap15 (f : ℝ → ℝ) (hf : ∀ x, f x = ∑' n, expTerm x n) :
    ∀ x y, f x * f y = f (x + y) := by
  exact gap10 f hf

end

end ProofGap.Exercise2879

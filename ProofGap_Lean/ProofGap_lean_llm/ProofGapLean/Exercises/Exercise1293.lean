import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise1293

open scoped BigOperators

noncomputable section

def squareSum (n : ℕ) (a b : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, (a k * x + b k) ^ 2

def aa (n : ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, a k ^ 2

def ab (n : ℕ) (a b : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, a k * b k

def bb (n : ℕ) (b : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, b k ^ 2

private theorem coefficientCauchy (n : ℕ) (a b : ℕ → ℝ) :
    (ab n a b) ^ 2 ≤ aa n a * bb n b := by
  unfold ab aa bb
  exact Finset.sum_mul_sq_le_sq_mul_sq (Finset.range n) a b

theorem gap1 (n : ℕ) (a b : ℕ → ℝ) (x : ℝ) :
    squareSum n a b x =
      aa n a * x ^ 2 + 2 * ab n a b * x + bb n b := by
  unfold squareSum aa ab bb
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simp only [Finset.sum_range_succ]
      rw [ih]
      ring

theorem gap2 (n : ℕ) (a b : ℕ → ℝ) (x : ℝ) :
    0 ≤ aa n a * x ^ 2 + 2 * ab n a b * x + bb n b := by
  rw [← gap1 n a b x]
  unfold squareSum
  exact Finset.sum_nonneg fun k hk => sq_nonneg _

theorem gap3 (n : ℕ) (a b : ℕ → ℝ) (x : ℝ) :
    0 ≤ squareSum n a b x := by
  unfold squareSum
  exact Finset.sum_nonneg fun k hk => sq_nonneg _

theorem gap4 (n : ℕ) (a b : ℕ → ℝ) :
    ∀ x : ℝ, 0 ≤ squareSum n a b x := by
  intro x
  exact gap3 n a b x

theorem gap5 (n : ℕ) (a b : ℕ → ℝ) :
    4 * (ab n a b) ^ 2 - 4 * aa n a * bb n b ≤ 0 := by
  have h := coefficientCauchy n a b
  linarith

theorem gap6 (n : ℕ) (a b : ℕ → ℝ) :
    (ab n a b) ^ 2 ≤ aa n a * bb n b := by
  exact coefficientCauchy n a b

theorem gap7 (n : ℕ) (a b : ℕ → ℝ) :
    (∑ k ∈ Finset.range n, a k * b k) ^ 2 ≤
      (∑ k ∈ Finset.range n, a k ^ 2) *
        (∑ k ∈ Finset.range n, b k ^ 2) := by
  simpa only [aa, ab, bb] using coefficientCauchy n a b

end

end ProofGap.Exercise1293

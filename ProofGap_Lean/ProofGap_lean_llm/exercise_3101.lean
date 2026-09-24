import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat
open Filter

def DivergentSeries (a : ℕ -> ℝ) : Prop :=
  ¬ ∃ l : ℝ, Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, a n) atTop (𝓝 l)

def InfiniteProductTendsTo (a : ℕ -> ℝ) (L : ℝ) : Prop :=
  Tendsto (fun N : ℕ => ∏ n ∈ Finset.Icc 1 N, a n) atTop (𝓝 L)

def InfiniteProductTendsToTop (a : ℕ -> ℝ) : Prop :=
  Tendsto (fun N : ℕ => ∏ n ∈ Finset.Icc 1 N, a n) atTop atTop

def DivergentProduct (a : ℕ -> ℝ) : Prop :=
  ¬ ∃ l : ℝ, InfiniteProductTendsTo a l

-- exercise: exercise_3101

-- GAP 1: Euler finite-product lower bound over primes not exceeding N.
theorem proof_gap_exercise_3101_1
  (p : ℕ -> ℕ)
  (hp : ∀ n : ℕ, 0 < n -> Nat.Prime (p n))
  : ∀ N : ℕ, 0 < N ->
      (∏ n ∈ (Finset.Icc 1 N).filter (fun n => p n ≤ N),
        (1 / (1 - 1 / (p n : ℝ)))) >
      (∑ n ∈ Finset.Icc 1 N, 1 / (n : ℝ)) := by
  sorry

-- GAP 2: divergence of the harmonic series.
theorem proof_gap_exercise_3101_2
  (p : ℕ -> ℕ)
  (hp : ∀ n : ℕ, 0 < n -> Nat.Prime (p n))
  (h1 : ∀ N : ℕ, 0 < N ->
      (∏ n ∈ (Finset.Icc 1 N).filter (fun n => p n ≤ N),
        (1 / (1 - 1 / (p n : ℝ)))) >
      (∑ n ∈ Finset.Icc 1 N, 1 / (n : ℝ)))
  : DivergentSeries (fun n : ℕ => 1 / (n : ℝ)) := by
  sorry

-- GAP 3: reciprocal Euler product tends to +infinity.
theorem proof_gap_exercise_3101_3
  (p : ℕ -> ℕ)
  (hp : ∀ n : ℕ, 0 < n -> Nat.Prime (p n))
  (h1 : ∀ N : ℕ, 0 < N ->
      (∏ n ∈ (Finset.Icc 1 N).filter (fun n => p n ≤ N),
        (1 / (1 - 1 / (p n : ℝ)))) >
      (∑ n ∈ Finset.Icc 1 N, 1 / (n : ℝ)))
  (h2 : DivergentSeries (fun n : ℕ => 1 / (n : ℝ)))
  : InfiniteProductTendsToTop (fun n : ℕ => (1 - 1 / (p n : ℝ))⁻¹) := by
  sorry

-- GAP 4: divergence of the reciprocal Euler product.
theorem proof_gap_exercise_3101_4
  (p : ℕ -> ℕ)
  (hp : ∀ n : ℕ, 0 < n -> Nat.Prime (p n))
  (h1 : ∀ N : ℕ, 0 < N ->
      (∏ n ∈ (Finset.Icc 1 N).filter (fun n => p n ≤ N),
        (1 / (1 - 1 / (p n : ℝ)))) >
      (∑ n ∈ Finset.Icc 1 N, 1 / (n : ℝ)))
  (h2 : DivergentSeries (fun n : ℕ => 1 / (n : ℝ)))
  (h3 : InfiniteProductTendsToTop (fun n : ℕ => (1 - 1 / (p n : ℝ))⁻¹))
  : DivergentProduct (fun n : ℕ => (1 - 1 / (p n : ℝ))⁻¹) := by
  sorry

-- GAP 5: the non-reciprocal prime product tends to zero.
theorem proof_gap_exercise_3101_5
  (p : ℕ -> ℕ)
  (hp : ∀ n : ℕ, 0 < n -> Nat.Prime (p n))
  (h1 : ∀ N : ℕ, 0 < N ->
      (∏ n ∈ (Finset.Icc 1 N).filter (fun n => p n ≤ N),
        (1 / (1 - 1 / (p n : ℝ)))) >
      (∑ n ∈ Finset.Icc 1 N, 1 / (n : ℝ)))
  (h2 : DivergentSeries (fun n : ℕ => 1 / (n : ℝ)))
  (h3 : InfiniteProductTendsToTop (fun n : ℕ => (1 - 1 / (p n : ℝ))⁻¹))
  (h4 : DivergentProduct (fun n : ℕ => (1 - 1 / (p n : ℝ))⁻¹))
  : InfiniteProductTendsTo (fun n : ℕ => 1 - 1 / (p n : ℝ)) 0 := by
  sorry

-- GAP 6: positivity of reciprocal prime terms.
theorem proof_gap_exercise_3101_6
  (p : ℕ -> ℕ)
  (hp : ∀ n : ℕ, 0 < n -> Nat.Prime (p n))
  (h1 : ∀ N : ℕ, 0 < N ->
      (∏ n ∈ (Finset.Icc 1 N).filter (fun n => p n ≤ N),
        (1 / (1 - 1 / (p n : ℝ)))) >
      (∑ n ∈ Finset.Icc 1 N, 1 / (n : ℝ)))
  (h2 : DivergentSeries (fun n : ℕ => 1 / (n : ℝ)))
  (h3 : InfiniteProductTendsToTop (fun n : ℕ => (1 - 1 / (p n : ℝ))⁻¹))
  (h4 : DivergentProduct (fun n : ℕ => (1 - 1 / (p n : ℝ))⁻¹))
  (h5 : InfiniteProductTendsTo (fun n : ℕ => 1 - 1 / (p n : ℝ)) 0)
  : ∀ n : ℕ, 0 < n -> 1 / (p n : ℝ) > 0 := by
  sorry

-- GAP 7: positive-term product criterion implies divergence of the prime reciprocal series.
theorem proof_gap_exercise_3101_7
  (p : ℕ -> ℕ)
  (hp : ∀ n : ℕ, 0 < n -> Nat.Prime (p n))
  (h1 : ∀ N : ℕ, 0 < N ->
      (∏ n ∈ (Finset.Icc 1 N).filter (fun n => p n ≤ N),
        (1 / (1 - 1 / (p n : ℝ)))) >
      (∑ n ∈ Finset.Icc 1 N, 1 / (n : ℝ)))
  (h2 : DivergentSeries (fun n : ℕ => 1 / (n : ℝ)))
  (h3 : InfiniteProductTendsToTop (fun n : ℕ => (1 - 1 / (p n : ℝ))⁻¹))
  (h4 : DivergentProduct (fun n : ℕ => (1 - 1 / (p n : ℝ))⁻¹))
  (h5 : InfiniteProductTendsTo (fun n : ℕ => 1 - 1 / (p n : ℝ)) 0)
  (h6 : ∀ n : ℕ, 0 < n -> 1 / (p n : ℝ) > 0)
  : DivergentSeries (fun n : ℕ => 1 / (p n : ℝ)) := by
  sorry

-- GAP 8: restate divergence of the reciprocal Euler product.
theorem proof_gap_exercise_3101_8
  (p : ℕ -> ℕ)
  (hp : ∀ n : ℕ, 0 < n -> Nat.Prime (p n))
  (h1 : ∀ N : ℕ, 0 < N ->
      (∏ n ∈ (Finset.Icc 1 N).filter (fun n => p n ≤ N),
        (1 / (1 - 1 / (p n : ℝ)))) >
      (∑ n ∈ Finset.Icc 1 N, 1 / (n : ℝ)))
  (h2 : DivergentSeries (fun n : ℕ => 1 / (n : ℝ)))
  (h3 : InfiniteProductTendsToTop (fun n : ℕ => (1 - 1 / (p n : ℝ))⁻¹))
  (h4 : DivergentProduct (fun n : ℕ => (1 - 1 / (p n : ℝ))⁻¹))
  (h5 : InfiniteProductTendsTo (fun n : ℕ => 1 - 1 / (p n : ℝ)) 0)
  (h6 : ∀ n : ℕ, 0 < n -> 1 / (p n : ℝ) > 0)
  (h7 : DivergentSeries (fun n : ℕ => 1 / (p n : ℝ)))
  : DivergentProduct (fun n : ℕ => (1 - 1 / (p n : ℝ))⁻¹) := by
  sorry

-- GAP 9: restate divergence of the reciprocal-prime series.
theorem proof_gap_exercise_3101_9
  (p : ℕ -> ℕ)
  (hp : ∀ n : ℕ, 0 < n -> Nat.Prime (p n))
  (h1 : ∀ N : ℕ, 0 < N ->
      (∏ n ∈ (Finset.Icc 1 N).filter (fun n => p n ≤ N),
        (1 / (1 - 1 / (p n : ℝ)))) >
      (∑ n ∈ Finset.Icc 1 N, 1 / (n : ℝ)))
  (h2 : DivergentSeries (fun n : ℕ => 1 / (n : ℝ)))
  (h3 : InfiniteProductTendsToTop (fun n : ℕ => (1 - 1 / (p n : ℝ))⁻¹))
  (h4 : DivergentProduct (fun n : ℕ => (1 - 1 / (p n : ℝ))⁻¹))
  (h5 : InfiniteProductTendsTo (fun n : ℕ => 1 - 1 / (p n : ℝ)) 0)
  (h6 : ∀ n : ℕ, 0 < n -> 1 / (p n : ℝ) > 0)
  (h7 : DivergentSeries (fun n : ℕ => 1 / (p n : ℝ)))
  (h8 : DivergentProduct (fun n : ℕ => (1 - 1 / (p n : ℝ))⁻¹))
  : DivergentSeries (fun n : ℕ => 1 / (p n : ℝ)) := by
  sorry

-- GAP 10: final conjunction of both divergence conclusions.
theorem proof_gap_exercise_3101_10
  (p : ℕ -> ℕ)
  (hp : ∀ n : ℕ, 0 < n -> Nat.Prime (p n))
  (h1 : ∀ N : ℕ, 0 < N ->
      (∏ n ∈ (Finset.Icc 1 N).filter (fun n => p n ≤ N),
        (1 / (1 - 1 / (p n : ℝ)))) >
      (∑ n ∈ Finset.Icc 1 N, 1 / (n : ℝ)))
  (h2 : DivergentSeries (fun n : ℕ => 1 / (n : ℝ)))
  (h3 : InfiniteProductTendsToTop (fun n : ℕ => (1 - 1 / (p n : ℝ))⁻¹))
  (h4 : DivergentProduct (fun n : ℕ => (1 - 1 / (p n : ℝ))⁻¹))
  (h5 : InfiniteProductTendsTo (fun n : ℕ => 1 - 1 / (p n : ℝ)) 0)
  (h6 : ∀ n : ℕ, 0 < n -> 1 / (p n : ℝ) > 0)
  (h7 : DivergentSeries (fun n : ℕ => 1 / (p n : ℝ)))
  (h8 : DivergentProduct (fun n : ℕ => (1 - 1 / (p n : ℝ))⁻¹))
  (h9 : DivergentSeries (fun n : ℕ => 1 / (p n : ℝ)))
  : DivergentProduct (fun n : ℕ => (1 - 1 / (p n : ℝ))⁻¹) ∧
      DivergentSeries (fun n : ℕ => 1 / (p n : ℝ)) := by
  sorry

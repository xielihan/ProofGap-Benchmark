import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat
open Filter

def lpAntitoneOnPositive (u : ℕ -> ℝ) : Prop :=
  ∀ m n : ℕ, 0 < m -> m ≤ n -> u n ≤ u m

-- exercise: exercise_2791

theorem proof_gap_exercise_2791_1
  (a : ℕ -> ℝ) (S : ℕ × ℝ -> ℝ) (n : ℕ)
  (hn : 0 ≤ n)
  (ha_sum : Summable (fun k : ℕ => if 1 ≤ k then a k else 0))
  (hS : S = (fun p : ℕ × ℝ =>
    Finset.sum (Finset.Icc (1 : ℕ) p.1) (fun k => a k * Real.exp (-((k : ℝ) * p.2)))))
  : ∀ (k : ℕ) (x : ℝ), 0 < k -> 0 ≤ x ->
      0 < Real.exp (-((k : ℝ) * x)) ∧ Real.exp (-((k : ℝ) * x)) ≤ 1 := by
  sorry

theorem proof_gap_exercise_2791_2
  (a : ℕ -> ℝ) (S : ℕ × ℝ -> ℝ) (n : ℕ)
  (hn : 0 ≤ n)
  (ha_sum : Summable (fun k : ℕ => if 1 ≤ k then a k else 0))
  (hS : S = (fun p : ℕ × ℝ =>
    Finset.sum (Finset.Icc (1 : ℕ) p.1) (fun k => a k * Real.exp (-((k : ℝ) * p.2)))))
  (h1 : ∀ (k : ℕ) (x : ℝ), 0 < k -> 0 ≤ x ->
      0 < Real.exp (-((k : ℝ) * x)) ∧ Real.exp (-((k : ℝ) * x)) ≤ 1)
  : ∀ x : ℝ, 0 ≤ x ->
      lpAntitoneOnPositive (fun k : ℕ => Real.exp (-((k : ℝ) * x))) := by
  sorry

theorem proof_gap_exercise_2791_3
  (a : ℕ -> ℝ) (S : ℕ × ℝ -> ℝ) (n : ℕ)
  (hn : 0 ≤ n)
  (ha_sum : Summable (fun k : ℕ => if 1 ≤ k then a k else 0))
  (hS : S = (fun p : ℕ × ℝ =>
    Finset.sum (Finset.Icc (1 : ℕ) p.1) (fun k => a k * Real.exp (-((k : ℝ) * p.2)))))
  (h1 : ∀ (k : ℕ) (x : ℝ), 0 < k -> 0 ≤ x ->
      0 < Real.exp (-((k : ℝ) * x)) ∧ Real.exp (-((k : ℝ) * x)) ≤ 1)
  (h2 : ∀ x : ℝ, 0 ≤ x ->
      lpAntitoneOnPositive (fun k : ℕ => Real.exp (-((k : ℝ) * x))))
  : ∀ x : ℝ, 0 ≤ x -> Summable (fun k : ℕ => if 1 ≤ k then a k else 0) := by
  sorry

theorem proof_gap_exercise_2791_4
  (a : ℕ -> ℝ) (S : ℕ × ℝ -> ℝ) (n : ℕ)
  (hn : 0 ≤ n)
  (ha_sum : Summable (fun k : ℕ => if 1 ≤ k then a k else 0))
  (hS : S = (fun p : ℕ × ℝ =>
    Finset.sum (Finset.Icc (1 : ℕ) p.1) (fun k => a k * Real.exp (-((k : ℝ) * p.2)))))
  (h1 : ∀ (k : ℕ) (x : ℝ), 0 < k -> 0 ≤ x ->
      0 < Real.exp (-((k : ℝ) * x)) ∧ Real.exp (-((k : ℝ) * x)) ≤ 1)
  (h2 : ∀ x : ℝ, 0 ≤ x ->
      lpAntitoneOnPositive (fun k : ℕ => Real.exp (-((k : ℝ) * x))))
  (h3 : ∀ x : ℝ, 0 ≤ x -> Summable (fun k : ℕ => if 1 ≤ k then a k else 0))
  : TendstoUniformlyOn
      (fun N x => S (N, x))
      (fun x : ℝ => ∑' k : ℕ, if 1 ≤ k then a k * Real.exp (-((k : ℝ) * x)) else 0)
      atTop
      (Set.Ici 0) := by
  sorry

theorem proof_gap_exercise_2791_5
  (a : ℕ -> ℝ) (S : ℕ × ℝ -> ℝ) (n : ℕ)
  (hn : 0 ≤ n)
  (ha_sum : Summable (fun k : ℕ => if 1 ≤ k then a k else 0))
  (hS : S = (fun p : ℕ × ℝ =>
    Finset.sum (Finset.Icc (1 : ℕ) p.1) (fun k => a k * Real.exp (-((k : ℝ) * p.2)))))
  (h4 : TendstoUniformlyOn
      (fun N x => S (N, x))
      (fun x : ℝ => ∑' k : ℕ, if 1 ≤ k then a k * Real.exp (-((k : ℝ) * x)) else 0)
      atTop
      (Set.Ici 0))
  : TendstoUniformlyOn
      (fun N x => S (N, x))
      (fun x : ℝ => ∑' k : ℕ, if 1 ≤ k then a k * Real.exp (-((k : ℝ) * x)) else 0)
      atTop
      (Set.Ici 0) := by
  sorry

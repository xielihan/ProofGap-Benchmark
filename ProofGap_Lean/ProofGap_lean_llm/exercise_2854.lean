import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat
open Filter

local infixl:70 " /. " => fun x y => ((x : ℝ) / (y : ℝ))

noncomputable def lpSeriesDom (term : ℝ -> ℕ -> ℝ) : Set ℝ :=
  {x | Summable (term x)}

-- exercise: exercise_2854

theorem proof_gap_exercise_2854_1
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : x ≠ 1)
  : (x ^ 10 : ℝ) / (1 - x) = x ^ 10 * (∑' n : ℕ, x ^ n) := by
  sorry

theorem proof_gap_exercise_2854_2
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : x ≠ 1)
  (h3 : (x ^ 10 : ℝ) / (1 - x) = x ^ 10 * (∑' n : ℕ, x ^ n))
  : (x ^ 10 : ℝ) / (1 - x) = (∑' n : ℕ, if 10 ≤ n then x ^ n else 0) := by
  sorry

theorem proof_gap_exercise_2854_3
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : x ≠ 1)
  (h3 : (x ^ 10 : ℝ) / (1 - x) = x ^ 10 * (∑' n : ℕ, x ^ n))
  (h4 : (x ^ 10 : ℝ) / (1 - x) = (∑' n : ℕ, if 10 ≤ n then x ^ n else 0))
  : lpSeriesDom (fun x n => if 10 ≤ n then x ^ n else 0) = Set.Ioo (-1 : ℝ) 1 := by
  sorry

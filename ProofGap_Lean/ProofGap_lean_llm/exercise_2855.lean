import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat
open Filter

local infixl:70 " /. " => fun x y => ((x : ℝ) / (y : ℝ))

noncomputable def lpSeriesDom (term : ℝ -> ℕ -> ℝ) : Set ℝ :=
  {x | Summable (term x)}

-- exercise: exercise_2855

theorem proof_gap_exercise_2855_1
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : x ≠ 1)
  : (1 /. ((1 - x) ^ 2)) = (1 - x) ^ (-2 : ℤ) := by
  sorry

theorem proof_gap_exercise_2855_2
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : x ≠ 1)
  (h3 : (1 /. ((1 - x) ^ 2)) = (1 - x) ^ (-2 : ℤ))
  : (1 - x) ^ (-2 : ℤ) =
      (∑' n : ℕ, ((Finset.prod (Finset.range n) (fun k => (-2 : ℝ) - k)) / (Nat.factorial n : ℝ)) * ((-x) ^ n)) := by
  sorry

theorem proof_gap_exercise_2855_3
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : x ≠ 1)
  (h3 : (1 /. ((1 - x) ^ 2)) = (1 - x) ^ (-2 : ℤ))
  (h4 : (1 - x) ^ (-2 : ℤ) =
      (∑' n : ℕ, ((Finset.prod (Finset.range n) (fun k => (-2 : ℝ) - k)) / (Nat.factorial n : ℝ)) * ((-x) ^ n)))
  : (1 /. ((1 - x) ^ 2)) = (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * x ^ n) := by
  sorry

theorem proof_gap_exercise_2855_4
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : x ≠ 1)
  (h3 : (1 /. ((1 - x) ^ 2)) = (1 - x) ^ (-2 : ℤ))
  (h4 : (1 - x) ^ (-2 : ℤ) =
      (∑' n : ℕ, ((Finset.prod (Finset.range n) (fun k => (-2 : ℝ) - k)) / (Nat.factorial n : ℝ)) * ((-x) ^ n)))
  (h5 : (1 /. ((1 - x) ^ 2)) = (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * x ^ n))
  : lpSeriesDom (fun x n => ((n + 1 : ℕ) : ℝ) * x ^ n) = Set.Ioo (-1 : ℝ) 1 := by
  sorry

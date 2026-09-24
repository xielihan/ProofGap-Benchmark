import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

noncomputable def lpSeriesDom (s : ℝ -> ℕ -> ℝ) : Set ℝ :=
  {x | Summable (s x)}

-- exercise: exercise_2853

theorem proof_gap_exercise_2853_1
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  : (Real.sin x) ^ 3 = (3 /. 4) * Real.sin x - (1 /. 4) * Real.sin (3 * x) := by
  sorry

theorem proof_gap_exercise_2853_2
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (Real.sin x) ^ 3 = (3 /. 4) * Real.sin x - (1 /. 4) * Real.sin (3 * x))
  : (Real.sin x) ^ 3 =
      (3 /. 4) * (∑' n : ℕ, ((-(1 : ℤ)) ^ n) * ((x ^ (2 * n + 1)) /. ((2 * n + 1)!))) -
      (1 /. 4) * (∑' n : ℕ, ((-(1 : ℤ)) ^ n) * (((3 : ℝ) ^ (2 * n + 1) * x ^ (2 * n + 1)) /. ((2 * n + 1)!))) := by
  sorry

theorem proof_gap_exercise_2853_3
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (Real.sin x) ^ 3 = (3 /. 4) * Real.sin x - (1 /. 4) * Real.sin (3 * x))
  (h3 : (Real.sin x) ^ 3 =
      (3 /. 4) * (∑' n : ℕ, ((-(1 : ℤ)) ^ n) * ((x ^ (2 * n + 1)) /. ((2 * n + 1)!))) -
      (1 /. 4) * (∑' n : ℕ, ((-(1 : ℤ)) ^ n) * (((3 : ℝ) ^ (2 * n + 1) * x ^ (2 * n + 1)) /. ((2 * n + 1)!))))
  : (Real.sin x) ^ 3 =
      (3 /. 4) * (∑' n : ℕ, ((-(1 : ℤ)) ^ (n + 1)) * ((((3 : ℝ) ^ (2 * n) - 1) /. ((2 * n + 1)!)) * x ^ (2 * n + 1))) := by
  sorry

theorem proof_gap_exercise_2853_4
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (Real.sin x) ^ 3 = (3 /. 4) * Real.sin x - (1 /. 4) * Real.sin (3 * x))
  (h3 : (Real.sin x) ^ 3 =
      (3 /. 4) * (∑' n : ℕ, ((-(1 : ℤ)) ^ n) * ((x ^ (2 * n + 1)) /. ((2 * n + 1)!))) -
      (1 /. 4) * (∑' n : ℕ, ((-(1 : ℤ)) ^ n) * (((3 : ℝ) ^ (2 * n + 1) * x ^ (2 * n + 1)) /. ((2 * n + 1)!))))
  (h4 : (Real.sin x) ^ 3 =
      (3 /. 4) * (∑' n : ℕ, ((-(1 : ℤ)) ^ (n + 1)) * ((((3 : ℝ) ^ (2 * n) - 1) /. ((2 * n + 1)!)) * x ^ (2 * n + 1))))
  : lpSeriesDom (fun y : ℝ => fun n : ℕ =>
      ((-(1 : ℤ)) ^ (n + 1)) * ((((3 : ℝ) ^ (2 * n) - 1) /. ((2 * n + 1)!)) * y ^ (2 * n + 1))) =
      (Set.univ : Set ℝ) := by
  sorry

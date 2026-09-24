import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

def approx (eps x y : ℝ) : Prop := |x - y| < eps

noncomputable def cosMaclaurinAt (x : ℝ) : ℝ :=
  ∑' n : ℕ, ((-1 : ℝ) ^ n) * x ^ (2 * n) /. (Nat.factorial (2 * n))

-- exercise: exercise_2923
-- Exercise 2923, gap 1
theorem proof_gap_exercise_2923_1 :
    (Real.cos (Real.pi /. 180)) ^ (2 : ℕ) = Real.cos (Real.pi /. 180) := by
  sorry

-- Exercise 2923, gap 2
theorem proof_gap_exercise_2923_2
    (h1 : (Real.cos (Real.pi /. 180)) ^ (2 : ℕ) = Real.cos (Real.pi /. 180)) :
    Real.cos (Real.pi /. 180) = cosMaclaurinAt (Real.pi /. 180) := by
  sorry

-- Exercise 2923, gap 3
theorem proof_gap_exercise_2923_3
    (h1 : (Real.cos (Real.pi /. 180)) ^ (2 : ℕ) = Real.cos (Real.pi /. 180))
    (h2 : Real.cos (Real.pi /. 180) = cosMaclaurinAt (Real.pi /. 180)) :
    ∃ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧
      ∃ Δ : ℝ, Δ ∈ (Set.univ : Set ℝ) ∧ 0 ≤ Δ ∧ n = 2 ∧
        Δ < (1 /. Nat.factorial 4) * (Real.pi /. 180) ^ (4 : ℕ) ∧
        (1 /. Nat.factorial 4) * (Real.pi /. 180) ^ (4 : ℕ) < (10 : ℝ) ^ (-6 : ℤ) := by
  sorry

-- Exercise 2923, gap 4
theorem proof_gap_exercise_2923_4
    (h1 : (Real.cos (Real.pi /. 180)) ^ (2 : ℕ) = Real.cos (Real.pi /. 180))
    (h2 : Real.cos (Real.pi /. 180) = cosMaclaurinAt (Real.pi /. 180))
    (h3 : ∃ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧
      ∃ Δ : ℝ, Δ ∈ (Set.univ : Set ℝ) ∧ 0 ≤ Δ ∧ n = 2 ∧
        Δ < (1 /. Nat.factorial 4) * (Real.pi /. 180) ^ (4 : ℕ) ∧
        (1 /. Nat.factorial 4) * (Real.pi /. 180) ^ (4 : ℕ) < (10 : ℝ) ^ (-6 : ℤ)) :
    approx ((10 : ℝ) ^ (-6 : ℤ)) ((Real.cos (Real.pi /. 180)) ^ (2 : ℕ)) 0.999848 := by
  sorry

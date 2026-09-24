import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

def approx (eps x y : ℝ) : Prop := |x - y| < eps

noncomputable def cubeRoot (x : ℝ) : ℝ := Real.rpow x (1 / (3 : ℝ))

noncomputable def binomialInvCubeSeries (x : ℝ) : ℝ :=
  1 + x ^ (2 : ℕ) /. 3 + (4 * x ^ (4 : ℕ)) /. ((3 : ℝ) ^ (2 : ℕ) * (Nat.factorial 2 : ℝ)) +
    ∑' k : ℕ, 0

noncomputable def int013 (f : ℝ → ℝ) : ℝ := ∫ x in (0 : ℝ)..(1 / (3 : ℝ)), f x

noncomputable def binomialInvCubeIntegral : ℝ :=
  int013 (fun x => 1 / cubeRoot (1 - x ^ (2 : ℕ)))

noncomputable def binomialInvCubeIntegralSeriesValue : ℝ :=
  1 / (3 : ℝ) + 1 /. ((3 : ℝ) ^ (5 : ℕ)) + ∑' k : ℕ, 0

-- exercise: exercise_2932_7
theorem proof_gap_exercise_2932_7_1 :
    ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ (1 / (3 : ℝ)) →
      1 - x ^ (2 : ℕ) > 0 := by
  sorry

theorem proof_gap_exercise_2932_7_2
    (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ (1 / (3 : ℝ)) →
      1 - x ^ (2 : ℕ) > 0) :
    ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ (1 / (3 : ℝ)) →
      1 / cubeRoot (1 - x ^ (2 : ℕ)) = Real.rpow (1 - x ^ (2 : ℕ)) (-(1 / (3 : ℝ))) := by
  sorry

theorem proof_gap_exercise_2932_7_3
    (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ (1 / (3 : ℝ)) →
      1 - x ^ (2 : ℕ) > 0)
    (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ (1 / (3 : ℝ)) →
      1 / cubeRoot (1 - x ^ (2 : ℕ)) = Real.rpow (1 - x ^ (2 : ℕ)) (-(1 / (3 : ℝ)))) :
    ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ (1 / (3 : ℝ)) →
      Real.rpow (1 - x ^ (2 : ℕ)) (-(1 / (3 : ℝ))) = binomialInvCubeSeries x := by
  sorry

theorem proof_gap_exercise_2932_7_4
    (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ (1 / (3 : ℝ)) →
      1 - x ^ (2 : ℕ) > 0)
    (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ (1 / (3 : ℝ)) →
      1 / cubeRoot (1 - x ^ (2 : ℕ)) = Real.rpow (1 - x ^ (2 : ℕ)) (-(1 / (3 : ℝ))))
    (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ (1 / (3 : ℝ)) →
      Real.rpow (1 - x ^ (2 : ℕ)) (-(1 / (3 : ℝ))) = binomialInvCubeSeries x) :
    ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ (1 / (3 : ℝ)) →
      1 / cubeRoot (1 - x ^ (2 : ℕ)) = binomialInvCubeSeries x := by
  sorry

theorem proof_gap_exercise_2932_7_5
    (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ (1 / (3 : ℝ)) →
      1 - x ^ (2 : ℕ) > 0)
    (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ (1 / (3 : ℝ)) →
      1 / cubeRoot (1 - x ^ (2 : ℕ)) = Real.rpow (1 - x ^ (2 : ℕ)) (-(1 / (3 : ℝ))))
    (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ (1 / (3 : ℝ)) →
      Real.rpow (1 - x ^ (2 : ℕ)) (-(1 / (3 : ℝ))) = binomialInvCubeSeries x)
    (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ (1 / (3 : ℝ)) →
      1 / cubeRoot (1 - x ^ (2 : ℕ)) = binomialInvCubeSeries x) :
    binomialInvCubeIntegral = binomialInvCubeIntegralSeriesValue := by
  sorry

theorem proof_gap_exercise_2932_7_6
    (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ (1 / (3 : ℝ)) →
      1 - x ^ (2 : ℕ) > 0)
    (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ (1 / (3 : ℝ)) →
      1 / cubeRoot (1 - x ^ (2 : ℕ)) = Real.rpow (1 - x ^ (2 : ℕ)) (-(1 / (3 : ℝ))))
    (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ (1 / (3 : ℝ)) →
      Real.rpow (1 - x ^ (2 : ℕ)) (-(1 / (3 : ℝ))) = binomialInvCubeSeries x)
    (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ (1 / (3 : ℝ)) →
      1 / cubeRoot (1 - x ^ (2 : ℕ)) = binomialInvCubeSeries x)
    (h5 : binomialInvCubeIntegral = binomialInvCubeIntegralSeriesValue) :
    approx 0.001 binomialInvCubeIntegral 0.337 := by
  sorry

import Mathlib

set_option linter.style.longLine false
open scoped BigOperators Topology Nat

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))
local notation:50 a " ≈[" eps "] " b => |a - b| < eps

noncomputable def exercise2921BinomialExpansionWithTail : ℝ :=
  1 + (1 /. 3) * (1 /. 8) - (1 /. (2 : ℕ)!) * (1 /. 3) * (2 /. 3) * (1 /. (8 ^ (2 : ℕ))) +
    (1 /. (3 : ℕ)!) * (1 /. 3) * (2 /. 3) * (5 /. 3) * (1 /. (8 ^ (3 : ℕ)))

-- exercise: exercise_2921
-- Exercise 2921, gap 1
theorem proof_gap_exercise_2921_1
  (R : ℕ -> ℝ)
  : Real.rpow (9 : ℝ) ((3 : ℝ)⁻¹) = 2 * Real.rpow (1 + 1 /. 8) (1 /. 3) := by
  sorry

-- Exercise 2921, gap 2
theorem proof_gap_exercise_2921_2
  (R : ℕ -> ℝ)
  (h1 : Real.rpow (9 : ℝ) ((3 : ℝ)⁻¹) = 2 * Real.rpow (1 + 1 /. 8) (1 /. 3))
  : (1 /. 8) ∈ Set.Ioo (-(1 : ℝ)) 1 := by
  sorry

-- Exercise 2921, gap 3
theorem proof_gap_exercise_2921_3
  (R : ℕ -> ℝ)
  (h1 : Real.rpow (9 : ℝ) ((3 : ℝ)⁻¹) = 2 * Real.rpow (1 + 1 /. 8) (1 /. 3))
  (h2 : (1 /. 8) ∈ Set.Ioo (-(1 : ℝ)) 1)
  : Real.rpow (9 : ℝ) ((3 : ℝ)⁻¹) = 2 * exercise2921BinomialExpansionWithTail := by
  sorry

-- Exercise 2921, gap 4
theorem proof_gap_exercise_2921_4
  (R : ℕ -> ℝ)
  (h1 : Real.rpow (9 : ℝ) ((3 : ℝ)⁻¹) = 2 * Real.rpow (1 + 1 /. 8) (1 /. 3))
  (h2 : (1 /. 8) ∈ Set.Ioo (-(1 : ℝ)) 1)
  (h3 : Real.rpow (9 : ℝ) ((3 : ℝ)⁻¹) = 2 * exercise2921BinomialExpansionWithTail)
  : |R 3| < 2 * (1 /. (3 : ℕ)!) * ((2 * 5) /. (3 ^ (3 : ℕ))) * (1 /. (8 ^ (3 : ℕ))) := by
  sorry

-- Exercise 2921, gap 5
theorem proof_gap_exercise_2921_5
  (R : ℕ -> ℝ)
  (h1 : Real.rpow (9 : ℝ) ((3 : ℝ)⁻¹) = 2 * Real.rpow (1 + 1 /. 8) (1 /. 3))
  (h2 : (1 /. 8) ∈ Set.Ioo (-(1 : ℝ)) 1)
  (h3 : Real.rpow (9 : ℝ) ((3 : ℝ)⁻¹) = 2 * exercise2921BinomialExpansionWithTail)
  (h4 : |R 3| < 2 * (1 /. (3 : ℕ)!) * ((2 * 5) /. (3 ^ (3 : ℕ))) * (1 /. (8 ^ (3 : ℕ))))
  : 2 * (1 /. (3 : ℕ)!) * ((2 * 5) /. (3 ^ (3 : ℕ))) * (1 /. (8 ^ (3 : ℕ))) =
      10 / ((3 : ℝ) ^ (4 : ℕ) * (8 : ℝ) ^ (3 : ℕ)) := by
  sorry

-- Exercise 2921, gap 6
theorem proof_gap_exercise_2921_6
  (R : ℕ -> ℝ)
  (h1 : Real.rpow (9 : ℝ) ((3 : ℝ)⁻¹) = 2 * Real.rpow (1 + 1 /. 8) (1 /. 3))
  (h2 : (1 /. 8) ∈ Set.Ioo (-(1 : ℝ)) 1)
  (h3 : Real.rpow (9 : ℝ) ((3 : ℝ)⁻¹) = 2 * exercise2921BinomialExpansionWithTail)
  (h4 : |R 3| < 2 * (1 /. (3 : ℕ)!) * ((2 * 5) /. (3 ^ (3 : ℕ))) * (1 /. (8 ^ (3 : ℕ))))
  (h5 : 2 * (1 /. (3 : ℕ)!) * ((2 * 5) /. (3 ^ (3 : ℕ))) * (1 /. (8 ^ (3 : ℕ))) =
      10 / ((3 : ℝ) ^ (4 : ℕ) * (8 : ℝ) ^ (3 : ℕ)))
  : 10 / ((3 : ℝ) ^ (4 : ℕ) * (8 : ℝ) ^ (3 : ℕ)) < (0.001 : ℝ) := by
  sorry

-- Exercise 2921, gap 7
theorem proof_gap_exercise_2921_7
  (R : ℕ -> ℝ)
  (h1 : Real.rpow (9 : ℝ) ((3 : ℝ)⁻¹) = 2 * Real.rpow (1 + 1 /. 8) (1 /. 3))
  (h2 : (1 /. 8) ∈ Set.Ioo (-(1 : ℝ)) 1)
  (h3 : Real.rpow (9 : ℝ) ((3 : ℝ)⁻¹) = 2 * exercise2921BinomialExpansionWithTail)
  (h4 : |R 3| < 2 * (1 /. (3 : ℕ)!) * ((2 * 5) /. (3 ^ (3 : ℕ))) * (1 /. (8 ^ (3 : ℕ))))
  (h5 : 2 * (1 /. (3 : ℕ)!) * ((2 * 5) /. (3 ^ (3 : ℕ))) * (1 /. (8 ^ (3 : ℕ))) =
      10 / ((3 : ℝ) ^ (4 : ℕ) * (8 : ℝ) ^ (3 : ℕ)))
  (h6 : 10 / ((3 : ℝ) ^ (4 : ℕ) * (8 : ℝ) ^ (3 : ℕ)) < (0.001 : ℝ))
  : |R 3| < (0.001 : ℝ) := by
  sorry

-- Exercise 2921, gap 8
theorem proof_gap_exercise_2921_8
  (R : ℕ -> ℝ)
  (h1 : Real.rpow (9 : ℝ) ((3 : ℝ)⁻¹) = 2 * Real.rpow (1 + 1 /. 8) (1 /. 3))
  (h2 : (1 /. 8) ∈ Set.Ioo (-(1 : ℝ)) 1)
  (h3 : Real.rpow (9 : ℝ) ((3 : ℝ)⁻¹) = 2 * exercise2921BinomialExpansionWithTail)
  (h4 : |R 3| < 2 * (1 /. (3 : ℕ)!) * ((2 * 5) /. (3 ^ (3 : ℕ))) * (1 /. (8 ^ (3 : ℕ))))
  (h5 : 2 * (1 /. (3 : ℕ)!) * ((2 * 5) /. (3 ^ (3 : ℕ))) * (1 /. (8 ^ (3 : ℕ))) =
      10 / ((3 : ℝ) ^ (4 : ℕ) * (8 : ℝ) ^ (3 : ℕ)))
  (h6 : 10 / ((3 : ℝ) ^ (4 : ℕ) * (8 : ℝ) ^ (3 : ℕ)) < (0.001 : ℝ))
  (h7 : |R 3| < (0.001 : ℝ))
  : Real.rpow (9 : ℝ) ((3 : ℝ)⁻¹) ≈[(0.001 : ℝ)]
      2 * (1 + (1 /. 3) * (1 /. 8) - (1 /. (2 : ℕ)!) * (2 /. (3 ^ (2 : ℕ))) * (1 /. (8 ^ (2 : ℕ)))) := by
  sorry

-- Exercise 2921, gap 9
theorem proof_gap_exercise_2921_9
  (R : ℕ -> ℝ)
  (h1 : Real.rpow (9 : ℝ) ((3 : ℝ)⁻¹) = 2 * Real.rpow (1 + 1 /. 8) (1 /. 3))
  (h2 : (1 /. 8) ∈ Set.Ioo (-(1 : ℝ)) 1)
  (h3 : Real.rpow (9 : ℝ) ((3 : ℝ)⁻¹) = 2 * exercise2921BinomialExpansionWithTail)
  (h4 : |R 3| < 2 * (1 /. (3 : ℕ)!) * ((2 * 5) /. (3 ^ (3 : ℕ))) * (1 /. (8 ^ (3 : ℕ))))
  (h5 : 2 * (1 /. (3 : ℕ)!) * ((2 * 5) /. (3 ^ (3 : ℕ))) * (1 /. (8 ^ (3 : ℕ))) =
      10 / ((3 : ℝ) ^ (4 : ℕ) * (8 : ℝ) ^ (3 : ℕ)))
  (h6 : 10 / ((3 : ℝ) ^ (4 : ℕ) * (8 : ℝ) ^ (3 : ℕ)) < (0.001 : ℝ))
  (h7 : |R 3| < (0.001 : ℝ))
  (h8 : Real.rpow (9 : ℝ) ((3 : ℝ)⁻¹) ≈[(0.001 : ℝ)]
      2 * (1 + (1 /. 3) * (1 /. 8) - (1 /. (2 : ℕ)!) * (2 /. (3 ^ (2 : ℕ))) * (1 /. (8 ^ (2 : ℕ)))))
  : Real.rpow (9 : ℝ) ((3 : ℝ)⁻¹) ≈[(0.001 : ℝ)] 2.080 := by
  sorry

import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

noncomputable def AntiderivSet (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x : ℝ, deriv F x = f x}

noncomputable def SetScale (a : ℝ) (S : Set (ℝ → ℝ)) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ S, ∀ x, F x = a * G x}

noncomputable def SetAdd (S T : Set (ℝ → ℝ)) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ S, ∃ H ∈ T, ∀ x, F x = G x + H x}

-- exercise: exercise_1953

theorem proof_gap_exercise_1953_1
  (x : ℝ) (hx1 : x ≠ 1) (hx2 : x ≠ -1) (hpos : 0 < x ^ (2 : ℕ) - x - 1)
  (I I1 I2 : Set (ℝ → ℝ))
  (hI : I = AntiderivSet (fun y => y /. ((y ^ (2 : ℕ) - 1) * Real.sqrt (y ^ (2 : ℕ) - y - 1))))
  (hI1 : I1 = AntiderivSet (fun y => 1 /. ((y + 1) * Real.sqrt (y ^ (2 : ℕ) - y - 1))))
  (hI2 : I2 = AntiderivSet (fun y => 1 /. ((y - 1) * Real.sqrt (y ^ (2 : ℕ) - y - 1))))
  : I = {F | ∃ G : ℝ → ℝ,
      G ∈ AntiderivSet (fun y => (1 /. (y + 1) + 1 /. (y - 1)) * (1 /. Real.sqrt (y ^ (2 : ℕ) - y - 1))) ∧
      ∀ y, F y = (1 /. 2) * G y} := by
  sorry

theorem proof_gap_exercise_1953_2
  (x : ℝ) (I I1 I2 : Set (ℝ → ℝ))
  : I = SetAdd (SetScale (1 /. 2) I1) (SetScale (1 /. 2) I2) := by
  sorry

theorem proof_gap_exercise_1953_3
  (x t : ℝ) (hsub : x + 1 = 1 /. t)
  : deriv (fun u : ℝ => u) x = (-1 /. t ^ (2 : ℕ)) * deriv (fun u : ℝ => u) t := by
  sorry

theorem proof_gap_exercise_1953_4
  (x t : ℝ) (hsub : x + 1 = 1 /. t)
  : t > 0 → Real.sqrt (x ^ (2 : ℕ) - x - 1) = Real.sqrt (t ^ (2 : ℕ) - 3 * t + 1) /. t := by
  sorry

theorem proof_gap_exercise_1953_5
  (I1 : Set (ℝ → ℝ))
  : I1 = {F | ∃ G : ℝ → ℝ,
      G ∈ AntiderivSet (fun t => 1 /. Real.sqrt (t ^ (2 : ℕ) - 3 * t + 1)) ∧
      ∀ t, F t = -G t} := by
  sorry

theorem proof_gap_exercise_1953_6
  (I1 : Set (ℝ → ℝ)) (t : ℝ)
  : ∀ C1 : ℝ, (fun u => -Real.log |u - 3 /. 2 + Real.sqrt (u ^ (2 : ℕ) - 3 * u + 1)| + C1) ∈ I1 := by
  sorry

theorem proof_gap_exercise_1953_7
  (I1 : Set (ℝ → ℝ)) (x : ℝ)
  : ∀ C2 : ℝ, (fun y => -Real.log |(3 * y + 1 - 2 * Real.sqrt (y ^ (2 : ℕ) - y - 1)) /. (y + 1)| + C2) ∈ I1 := by
  sorry

theorem proof_gap_exercise_1953_8
  (x u : ℝ) (hsub : x - 1 = 1 /. u)
  : deriv (fun y : ℝ => y) x = (-1 /. u ^ (2 : ℕ)) * deriv (fun y : ℝ => y) u := by
  sorry

theorem proof_gap_exercise_1953_9
  (I2 : Set (ℝ → ℝ))
  : ∀ C3 : ℝ, (fun y => Real.arcsin ((y - 3) /. (|y - 1| * Real.sqrt 5)) + C3) ∈ I2 := by
  sorry

theorem proof_gap_exercise_1953_10
  (I : Set (ℝ → ℝ))
  : ∀ C : ℝ,
      (fun y => -(1 /. 2) * Real.log |(3 * y + 1 - 2 * Real.sqrt (y ^ (2 : ℕ) - y - 1)) /. (y + 1)| +
        (1 /. 2) * Real.arcsin ((y - 3) /. (|y - 1| * Real.sqrt 5)) + C) ∈ I := by
  sorry

theorem proof_gap_exercise_1953_11
  : AntiderivSet (fun x => x /. ((x ^ (2 : ℕ) - 1) * Real.sqrt (x ^ (2 : ℕ) - x - 1))) =
      {F | ∃ C : ℝ, ∀ x : ℝ,
        F x = -(1 /. 2) * Real.log |(3 * x + 1 - 2 * Real.sqrt (x ^ (2 : ℕ) - x - 1)) /. (x + 1)| +
          (1 /. 2) * Real.arcsin ((x - 3) /. (|x - 1| * Real.sqrt 5)) + C} := by
  sorry

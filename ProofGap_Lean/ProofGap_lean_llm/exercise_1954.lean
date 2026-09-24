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

noncomputable def SetSub (S T : Set (ℝ → ℝ)) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ S, ∃ H ∈ T, ∀ x, F x = G x - H x}

-- exercise: exercise_1954

theorem proof_gap_exercise_1954_1
  (x : ℝ) (hx : x ≠ -1) (I : Set (ℝ → ℝ))
  : I = AntiderivSet (fun y => ((y ^ (2 : ℕ) + y + 1) /. ((y + 1) ^ (2 : ℕ))) * (1 /. Real.sqrt (y ^ (2 : ℕ) + y + 1))) := by
  sorry

theorem proof_gap_exercise_1954_2
  (x : ℝ) (I : Set (ℝ → ℝ))
  : I = AntiderivSet (fun y => (((y + 1) ^ (2 : ℕ) - (y + 1) + 1) /. ((y + 1) ^ (2 : ℕ))) * (1 /. Real.sqrt (y ^ (2 : ℕ) + y + 1))) := by
  sorry

theorem proof_gap_exercise_1954_3
  (I I1 I2 I3 : Set (ℝ → ℝ))
  : I = SetAdd (SetSub I1 I2) I3 := by
  sorry

theorem proof_gap_exercise_1954_4
  (I1 : Set (ℝ → ℝ))
  : ∀ C1 : ℝ, (fun x => Real.log (x + 1 /. 2 + Real.sqrt (x ^ (2 : ℕ) + x + 1)) + C1) ∈ I1 := by
  sorry

theorem proof_gap_exercise_1954_5
  (I2 : Set (ℝ → ℝ))
  : ∀ C2 : ℝ, (fun x => -Real.log |(1 - x + 2 * Real.sqrt (x ^ (2 : ℕ) + x + 1)) /. (x + 1)| + C2) ∈ I2 := by
  sorry

theorem proof_gap_exercise_1954_6
  (x t : ℝ) (hsub : x + 1 = 1 /. t)
  : deriv (fun u : ℝ => u) x = (-1 /. t ^ (2 : ℕ)) * deriv (fun u : ℝ => u) t := by
  sorry

theorem proof_gap_exercise_1954_7
  (x t : ℝ) (hsub : x + 1 = 1 /. t)
  : t > 0 → Real.sqrt (x ^ (2 : ℕ) + x + 1) = Real.sqrt (t ^ (2 : ℕ) - t + 1) /. t := by
  sorry

theorem proof_gap_exercise_1954_8
  (I3 : Set (ℝ → ℝ))
  : I3 = {F | ∃ G : ℝ → ℝ,
      G ∈ AntiderivSet (fun t => t /. Real.sqrt (t ^ (2 : ℕ) - t + 1)) ∧
      ∀ t, F t = -G t} := by
  sorry

theorem proof_gap_exercise_1954_9
  (I3 : Set (ℝ → ℝ))
  : I3 = {F | ∃ G H : ℝ → ℝ,
      G ∈ AntiderivSet (fun t => (2 * t - 1) /. Real.sqrt (t ^ (2 : ℕ) - t + 1)) ∧
      H ∈ AntiderivSet (fun t => 1 /. Real.sqrt (t ^ (2 : ℕ) - t + 1)) ∧
      ∀ t, F t = -(1 /. 2) * G t - (1 /. 2) * H t} := by
  sorry

theorem proof_gap_exercise_1954_10
  (I3 : Set (ℝ → ℝ))
  : ∀ C3 : ℝ,
      (fun t => -Real.sqrt (t ^ (2 : ℕ) - t + 1) -
        (1 /. 2) * Real.log |t - 1 /. 2 + Real.sqrt (t ^ (2 : ℕ) - t + 1)| + C3) ∈ I3 := by
  sorry

theorem proof_gap_exercise_1954_11
  (I3 : Set (ℝ → ℝ))
  : ∀ C4 : ℝ,
      (fun x => -(Real.sqrt (x ^ (2 : ℕ) + x + 1) /. (x + 1)) -
        (1 /. 2) * Real.log |(1 - x + 2 * Real.sqrt (x ^ (2 : ℕ) + x + 1)) /. (x + 1)| + C4) ∈ I3 := by
  sorry

theorem proof_gap_exercise_1954_12
  (I : Set (ℝ → ℝ))
  : ∀ C : ℝ,
      (fun x => Real.log (x + 1 /. 2 + Real.sqrt (x ^ (2 : ℕ) + x + 1)) -
        Real.sqrt (x ^ (2 : ℕ) + x + 1) /. (x + 1) +
        (1 /. 2) * Real.log |(1 - x + 2 * Real.sqrt (x ^ (2 : ℕ) + x + 1)) /. (x + 1)| + C) ∈ I := by
  sorry

theorem proof_gap_exercise_1954_13
  : AntiderivSet (fun x => Real.sqrt (x ^ (2 : ℕ) + x + 1) /. ((x + 1) ^ (2 : ℕ))) =
      {F | ∃ C : ℝ, ∀ x : ℝ,
        F x = Real.log (x + 1 /. 2 + Real.sqrt (x ^ (2 : ℕ) + x + 1)) -
          Real.sqrt (x ^ (2 : ℕ) + x + 1) /. (x + 1) +
          (1 /. 2) * Real.log |(1 - x + 2 * Real.sqrt (x ^ (2 : ℕ) + x + 1)) /. (x + 1)| + C} := by
  sorry

import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology

noncomputable section

def VolumeInt3 (V : Set (ℝ × ℝ × ℝ)) (f : ℝ × ℝ × ℝ -> ℝ) : ℝ :=
  ∫ p in V, f p

def V4078 : Set (ℝ × ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.1 ^ (2 : ℕ) + p.2.1 ^ (2 : ℕ) + p.2.2 ^ (2 : ℕ) ≤ 1}

-- exercise: exercise_4078

theorem proof_gap_exercise_4078_1
  (V : Set (ℝ × ℝ × ℝ))
  (hV : V = V4078) :
  ∀ x : ℝ, ∀ y : ℝ, ∀ z : ℝ,
    VolumeInt3 V (fun p => p.1 * p.2.1 * p.2.2) =
      ∫ x in (0 : ℝ)..(1 : ℝ),
        x * (∫ y in (0 : ℝ)..Real.sqrt (1 - x ^ (2 : ℕ)),
          y * (∫ z in (0 : ℝ)..Real.sqrt (1 - x ^ (2 : ℕ) - y ^ (2 : ℕ)), z)) := by
  sorry

theorem proof_gap_exercise_4078_2
  (V : Set (ℝ × ℝ × ℝ))
  (hV : V = V4078)
  (h1 : ∀ x : ℝ, ∀ y : ℝ, ∀ z : ℝ,
    VolumeInt3 V (fun p => p.1 * p.2.1 * p.2.2) =
      ∫ x in (0 : ℝ)..(1 : ℝ),
        x * (∫ y in (0 : ℝ)..Real.sqrt (1 - x ^ (2 : ℕ)),
          y * (∫ z in (0 : ℝ)..Real.sqrt (1 - x ^ (2 : ℕ) - y ^ (2 : ℕ)), z))) :
  ∀ x : ℝ, ∀ y : ℝ, ∀ z : ℝ,
    VolumeInt3 V (fun p => p.1 * p.2.1 * p.2.2) =
      (1 : ℝ) / 2 * (∫ x in (0 : ℝ)..(1 : ℝ),
        x * (∫ y in (0 : ℝ)..Real.sqrt (1 - x ^ (2 : ℕ)),
          y * (1 - x ^ (2 : ℕ) - y ^ (2 : ℕ)))) := by
  sorry

theorem proof_gap_exercise_4078_3
  (V : Set (ℝ × ℝ × ℝ))
  (hV : V = V4078)
  (h1 : ∀ x : ℝ, ∀ y : ℝ, ∀ z : ℝ,
    VolumeInt3 V (fun p => p.1 * p.2.1 * p.2.2) =
      ∫ x in (0 : ℝ)..(1 : ℝ),
        x * (∫ y in (0 : ℝ)..Real.sqrt (1 - x ^ (2 : ℕ)),
          y * (∫ z in (0 : ℝ)..Real.sqrt (1 - x ^ (2 : ℕ) - y ^ (2 : ℕ)), z)))
  (h2 : ∀ x : ℝ, ∀ y : ℝ, ∀ z : ℝ,
    VolumeInt3 V (fun p => p.1 * p.2.1 * p.2.2) =
      (1 : ℝ) / 2 * (∫ x in (0 : ℝ)..(1 : ℝ),
        x * (∫ y in (0 : ℝ)..Real.sqrt (1 - x ^ (2 : ℕ)),
          y * (1 - x ^ (2 : ℕ) - y ^ (2 : ℕ))))) :
  ∀ x : ℝ, ∀ y : ℝ, ∀ z : ℝ,
    VolumeInt3 V (fun p => p.1 * p.2.1 * p.2.2) =
      (1 : ℝ) / 8 * (∫ x in (0 : ℝ)..(1 : ℝ), x * (1 - x ^ (2 : ℕ)) ^ (2 : ℕ)) := by
  sorry

theorem proof_gap_exercise_4078_4
  (V : Set (ℝ × ℝ × ℝ))
  (hV : V = V4078)
  (h1 : ∀ x : ℝ, ∀ y : ℝ, ∀ z : ℝ,
    VolumeInt3 V (fun p => p.1 * p.2.1 * p.2.2) =
      ∫ x in (0 : ℝ)..(1 : ℝ),
        x * (∫ y in (0 : ℝ)..Real.sqrt (1 - x ^ (2 : ℕ)),
          y * (∫ z in (0 : ℝ)..Real.sqrt (1 - x ^ (2 : ℕ) - y ^ (2 : ℕ)), z)))
  (h2 : ∀ x : ℝ, ∀ y : ℝ, ∀ z : ℝ,
    VolumeInt3 V (fun p => p.1 * p.2.1 * p.2.2) =
      (1 : ℝ) / 2 * (∫ x in (0 : ℝ)..(1 : ℝ),
        x * (∫ y in (0 : ℝ)..Real.sqrt (1 - x ^ (2 : ℕ)),
          y * (1 - x ^ (2 : ℕ) - y ^ (2 : ℕ)))))
  (h3 : ∀ x : ℝ, ∀ y : ℝ, ∀ z : ℝ,
    VolumeInt3 V (fun p => p.1 * p.2.1 * p.2.2) =
      (1 : ℝ) / 8 * (∫ x in (0 : ℝ)..(1 : ℝ), x * (1 - x ^ (2 : ℕ)) ^ (2 : ℕ))) :
  ∀ x : ℝ, ∀ y : ℝ, ∀ z : ℝ,
    VolumeInt3 V (fun p => p.1 * p.2.1 * p.2.2) = (1 : ℝ) / 48 := by
  sorry

end

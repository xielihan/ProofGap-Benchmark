import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

-- exercise: exercise_2154

def e2154_domain (x : ℝ) : Prop :=
  x ∈ (Set.univ : Set ℝ) ∧ -1 < x ∧ x < 1

noncomputable def e2154_s (x : ℝ) : ℝ :=
  Real.sqrt (1 - x ^ (2 : ℕ))

noncomputable def e2154_integrand (x : ℝ) : ℝ :=
  (x ^ (3 : ℕ) * Real.arccos x) /. e2154_s x

theorem proof_gap_exercise_2154_1
  (C : ℝ)
  (hC : C ∈ (Set.univ : Set ℝ))
  (hlo : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → -1 < x)
  (hhi : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → x < 1)
  : ({F : ℝ → ℝ | ∀ x : ℝ, e2154_domain x →
        iteratedDeriv 1 F x = e2154_integrand x} =
      {F : ℝ → ℝ | ∃ G : ℝ → ℝ,
        (∀ x : ℝ, e2154_domain x →
          iteratedDeriv 1 G x =
            x ^ (2 : ℕ) * Real.arccos x * iteratedDeriv 1 e2154_s x) ∧
        (∀ x : ℝ, e2154_domain x → F x = -G x)}) := by
  sorry

theorem proof_gap_exercise_2154_2
  (C : ℝ)
  (hC : C ∈ (Set.univ : Set ℝ))
  (hlo : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → -1 < x)
  (hhi : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → x < 1)
  : ({F : ℝ → ℝ | ∃ G : ℝ → ℝ,
        (∀ x : ℝ, e2154_domain x →
          iteratedDeriv 1 G x =
            x ^ (2 : ℕ) * Real.arccos x * iteratedDeriv 1 e2154_s x) ∧
        (∀ x : ℝ, e2154_domain x → F x = -G x)} =
      {F : ℝ → ℝ | ∃ G : ℝ → ℝ,
        (∀ x : ℝ, e2154_domain x →
          iteratedDeriv 1 G x =
            e2154_s x * (2 * x * Real.arccos x - (x ^ (2 : ℕ) /. e2154_s x))) ∧
        (∀ x : ℝ, e2154_domain x →
          F x = -(x ^ (2 : ℕ)) * e2154_s x * Real.arccos x + G x)}) := by
  sorry

theorem proof_gap_exercise_2154_3
  (C : ℝ)
  (hC : C ∈ (Set.univ : Set ℝ))
  (hlo : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → -1 < x)
  (hhi : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → x < 1)
  : ({F : ℝ → ℝ | ∀ x : ℝ, e2154_domain x →
        iteratedDeriv 1 F x =
          e2154_s x * (2 * x * Real.arccos x - (x ^ (2 : ℕ) /. e2154_s x))} =
      {F : ℝ → ℝ | ∃ G H : ℝ → ℝ,
        (∀ x : ℝ, e2154_domain x →
          iteratedDeriv 1 G x =
            Real.arccos x * iteratedDeriv 1 (fun t : ℝ =>
              Real.rpow (1 - t ^ (2 : ℕ)) ((3 : ℝ) /. 2)) x) ∧
        (∀ x : ℝ, e2154_domain x →
          iteratedDeriv 1 H x = x ^ (2 : ℕ)) ∧
        (∀ x : ℝ, e2154_domain x →
          F x = -((2 : ℝ) /. 3) * G x - H x)}) := by
  sorry

theorem proof_gap_exercise_2154_4
  (C : ℝ)
  (hC : C ∈ (Set.univ : Set ℝ))
  (hlo : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → -1 < x)
  (hhi : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → x < 1)
  : ({F : ℝ → ℝ | ∀ x : ℝ, e2154_domain x →
        iteratedDeriv 1 F x = e2154_integrand x} =
      {F : ℝ → ℝ | ∃ G : ℝ → ℝ,
        (∀ x : ℝ, e2154_domain x →
          iteratedDeriv 1 G x =
            Real.rpow (1 - x ^ (2 : ℕ)) ((3 : ℝ) /. 2) * (1 /. e2154_s x)) ∧
        (∀ x : ℝ, e2154_domain x →
          F x =
            -(x ^ (2 : ℕ)) * e2154_s x * Real.arccos x -
              ((2 : ℝ) /. 3) *
                Real.rpow (1 - x ^ (2 : ℕ)) ((3 : ℝ) /. 2) * Real.arccos x -
              ((2 : ℝ) /. 3) * G x - ((1 : ℝ) /. 3) * x ^ (3 : ℕ))}) := by
  sorry

theorem proof_gap_exercise_2154_5
  (C : ℝ)
  (hC : C ∈ (Set.univ : Set ℝ))
  (hlo : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → -1 < x)
  (hhi : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → x < 1)
  : ({F : ℝ → ℝ | ∀ x : ℝ, e2154_domain x →
        iteratedDeriv 1 F x =
          Real.rpow (1 - x ^ (2 : ℕ)) ((3 : ℝ) /. 2) * (1 /. e2154_s x)} =
      {F : ℝ → ℝ | ∃ C : ℝ, C ∈ (Set.univ : Set ℝ) ∧
        ∀ x : ℝ, e2154_domain x →
          F x = x - ((1 : ℝ) /. 3) * x ^ (3 : ℕ) + C}) := by
  sorry

theorem proof_gap_exercise_2154_6
  (C : ℝ)
  (hC : C ∈ (Set.univ : Set ℝ))
  (hlo : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → -1 < x)
  (hhi : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → x < 1)
  : ({F : ℝ → ℝ | ∀ x : ℝ, e2154_domain x →
        iteratedDeriv 1 F x = e2154_integrand x} =
      {F : ℝ → ℝ | ∃ C : ℝ, C ∈ (Set.univ : Set ℝ) ∧
        ∀ x : ℝ, e2154_domain x →
          F x =
            -(x ^ (2 : ℕ)) * e2154_s x * Real.arccos x -
              ((2 : ℝ) /. 3) *
                Real.rpow (1 - x ^ (2 : ℕ)) ((3 : ℝ) /. 2) * Real.arccos x -
              ((2 : ℝ) /. 3) * x + ((2 : ℝ) /. 9) * x ^ (3 : ℕ) -
              ((1 : ℝ) /. 3) * x ^ (3 : ℕ) + C}) := by
  sorry

theorem proof_gap_exercise_2154_7
  (C : ℝ)
  (hC : C ∈ (Set.univ : Set ℝ))
  (hlo : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → -1 < x)
  (hhi : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → x < 1)
  : ({F : ℝ → ℝ | ∀ x : ℝ, e2154_domain x →
        iteratedDeriv 1 F x = e2154_integrand x} =
      {F : ℝ → ℝ | ∃ C : ℝ, C ∈ (Set.univ : Set ℝ) ∧
        ∀ x : ℝ, e2154_domain x →
          F x =
            -((6 * x + x ^ (3 : ℕ)) /. 9) -
              ((2 + x ^ (2 : ℕ)) /. 3) * e2154_s x * Real.arccos x + C}) := by
  sorry

import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

-- exercise: exercise_2150

def e2150_domain (x : ℝ) : Prop :=
  x ∈ (Set.univ : Set ℝ) ∧ x ≠ 1 ∧ x ≠ -1

noncomputable def e2150_L (x : ℝ) : ℝ :=
  Real.log |((x - 1) /. (x + 1))|

noncomputable def e2150_integrand (a b x : ℝ) : ℝ :=
  ((a * x ^ (2 : ℕ) + b) /. (x ^ (2 : ℕ) - 1)) * e2150_L x

theorem proof_gap_exercise_2150_1
  (x a b C : ℝ)
  (hx : e2150_domain x)
  (ha : a ∈ (Set.univ : Set ℝ))
  (hb : b ∈ (Set.univ : Set ℝ))
  (hC : C ∈ (Set.univ : Set ℝ))
  : ((a * x ^ (2 : ℕ) + b) /. (x ^ (2 : ℕ) - 1)) =
      a + ((a + b) /. (x ^ (2 : ℕ) - 1)) := by
  sorry

theorem proof_gap_exercise_2150_2
  (x a b C : ℝ)
  (hx : e2150_domain x)
  (ha : a ∈ (Set.univ : Set ℝ))
  (hb : b ∈ (Set.univ : Set ℝ))
  (hC : C ∈ (Set.univ : Set ℝ))
  : ({F : ℝ → ℝ | ∀ t : ℝ, e2150_domain t →
        iteratedDeriv 1 F t = e2150_integrand a b t} =
      {F : ℝ → ℝ | ∀ t : ℝ, e2150_domain t →
        iteratedDeriv 1 F t =
          (a + ((a + b) /. (t ^ (2 : ℕ) - 1))) * e2150_L t}) := by
  sorry

theorem proof_gap_exercise_2150_3
  (x a b C : ℝ)
  (hx : e2150_domain x)
  (ha : a ∈ (Set.univ : Set ℝ))
  (hb : b ∈ (Set.univ : Set ℝ))
  (hC : C ∈ (Set.univ : Set ℝ))
  : ({F : ℝ → ℝ | ∀ t : ℝ, e2150_domain t →
        iteratedDeriv 1 F t =
          (a + ((a + b) /. (t ^ (2 : ℕ) - 1))) * e2150_L t} =
      {F : ℝ → ℝ | ∃ G H : ℝ → ℝ,
        (∀ t : ℝ, e2150_domain t →
          iteratedDeriv 1 G t = (2 * t) /. (t ^ (2 : ℕ) - 1)) ∧
        (∀ t : ℝ, e2150_domain t →
          iteratedDeriv 1 H t = e2150_L t * iteratedDeriv 1 e2150_L t) ∧
        (∀ t : ℝ, e2150_domain t →
          F t = a * t * e2150_L t - a * G t + ((a + b) /. 2) * H t)}) := by
  sorry

theorem proof_gap_exercise_2150_4
  (x a b C : ℝ)
  (hx : e2150_domain x)
  (ha : a ∈ (Set.univ : Set ℝ))
  (hb : b ∈ (Set.univ : Set ℝ))
  (hC : C ∈ (Set.univ : Set ℝ))
  : ({F : ℝ → ℝ | ∀ t : ℝ, e2150_domain t →
        iteratedDeriv 1 F t = (2 * t) /. (t ^ (2 : ℕ) - 1)} =
      {F : ℝ → ℝ | ∃ C : ℝ, C ∈ (Set.univ : Set ℝ) ∧
        ∀ t : ℝ, e2150_domain t →
          F t = Real.log |(t ^ (2 : ℕ) - 1)| + C}) := by
  sorry

theorem proof_gap_exercise_2150_5
  (x a b C : ℝ)
  (hx : e2150_domain x)
  (ha : a ∈ (Set.univ : Set ℝ))
  (hb : b ∈ (Set.univ : Set ℝ))
  (hC : C ∈ (Set.univ : Set ℝ))
  : ({F : ℝ → ℝ | ∀ t : ℝ, e2150_domain t →
        iteratedDeriv 1 F t = e2150_L t * iteratedDeriv 1 e2150_L t} =
      {F : ℝ → ℝ | ∃ C : ℝ, C ∈ (Set.univ : Set ℝ) ∧
        ∀ t : ℝ, e2150_domain t →
          F t = (1 /. 2) * (e2150_L t) ^ (2 : ℕ) + C}) := by
  sorry

theorem proof_gap_exercise_2150_6
  (x a b C : ℝ)
  (hx : e2150_domain x)
  (ha : a ∈ (Set.univ : Set ℝ))
  (hb : b ∈ (Set.univ : Set ℝ))
  (hC : C ∈ (Set.univ : Set ℝ))
  : ({F : ℝ → ℝ | ∀ t : ℝ, e2150_domain t →
        iteratedDeriv 1 F t = e2150_integrand a b t} =
      {F : ℝ → ℝ | ∃ C : ℝ, C ∈ (Set.univ : Set ℝ) ∧
        ∀ t : ℝ, e2150_domain t →
          F t =
            a * (t * e2150_L t - Real.log |(t ^ (2 : ℕ) - 1)|) +
              ((a + b) /. 4) * (e2150_L t) ^ (2 : ℕ) + C}) := by
  sorry

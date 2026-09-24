import Mathlib

namespace Exercise225_1

-- A restricted real function is represented by its domain and a total extension.
-- All graphs ignore values outside the specified domain.
def restrictedGraph (f : ℝ → ℝ) (D : Set ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ D ∧ p.2 = f p.1}

-- The inverse graph is obtained by interchanging input and output.
-- Under the source hypotheses the original function is injective on D.
def inverseGraph (y : ℝ → ℝ) (D : Set ℝ) : Set (ℝ × ℝ) :=
  {p | p.2 ∈ D ∧ y p.2 = p.1}

def graphDomain (G : Set (ℝ × ℝ)) : Set ℝ :=
  {z | ∃ x, (z, x) ∈ G}

-- Choose the inverse value from the actual fiber. The fallback is used only
-- outside the inverse domain; no theorem constrains such evaluations.
noncomputable def inverseValue (y : ℝ → ℝ) (D : Set ℝ) (z : ℝ) : ℝ := by
  classical
  exact if h : ∃ x, (z, x) ∈ inverseGraph y D then Classical.choose h else 0

end Exercise225_1

open Exercise225_1

-- Exercise 225_1, gap 1 (PROOF GAP @1)
theorem proof_gap_exercise_225_1_1
    (y : ℝ → ℝ) (D : Set ℝ)
    (h_formula : ∀ x : ℝ, x ≤ 0 → y x = x ^ (2 : ℕ))
    (h_domain : D = Set.Iic (0 : ℝ)) :
    ∀ z : ℝ, z ∈ Set.Ici (0 : ℝ) →
      inverseValue y D z = -Real.sqrt z := by
  sorry

-- Exercise 225_1, gap 2 (PROOF GAP @2)
theorem proof_gap_exercise_225_1_2
    (y : ℝ → ℝ) (D : Set ℝ)
    (h_formula : ∀ x : ℝ, x ≤ 0 → y x = x ^ (2 : ℕ))
    (h_domain : D = Set.Iic (0 : ℝ))
    (h_inverse : ∀ z : ℝ, z ∈ Set.Ici (0 : ℝ) →
      inverseValue y D z = -Real.sqrt z) :
    graphDomain (inverseGraph y D) = Set.Ici (0 : ℝ) := by
  sorry

-- Exercise 225_1, gap 3 (PROOF GAP @3)
-- Equality of restricted functions is equality of their graphs, including domains.
theorem proof_gap_exercise_225_1_3
    (y : ℝ → ℝ) (D : Set ℝ)
    (h_formula : ∀ x : ℝ, x ≤ 0 → y x = x ^ (2 : ℕ))
    (h_domain : D = Set.Iic (0 : ℝ))
    (h_inverse : ∀ z : ℝ, z ∈ Set.Ici (0 : ℝ) →
      inverseValue y D z = -Real.sqrt z)
    (h_inverse_domain : graphDomain (inverseGraph y D) = Set.Ici (0 : ℝ)) :
    inverseGraph y D = restrictedGraph (fun z : ℝ => -Real.sqrt z) (Set.Ici 0) := by
  sorry

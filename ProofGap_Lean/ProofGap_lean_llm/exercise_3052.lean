import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology

namespace Exercise_3052

noncomputable def pTerm (n : ℕ) : ℝ := ((n : ℝ) ^ 3 - 1) / ((n : ℝ) ^ 3 + 1)

noncomputable def finiteProductFromTwo (u : ℕ -> ℝ) (n : ℕ) : ℝ :=
  Finset.prod (Finset.Icc 2 n) (fun i => u i)

noncomputable def infiniteProductFromTwo (u : ℕ -> ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto (fun n : ℕ => Finset.prod (Finset.Icc 2 n) (fun i => u i)) Filter.atTop (𝓝 L)

theorem proof_gap_exercise_3052_1
    (p P : ℕ -> ℝ)
    (hp : ∀ n : ℕ, 2 ≤ n -> p n = pTerm n)
    (hP : ∀ n : ℕ, 2 ≤ n -> P n = finiteProductFromTwo p n) :
    ∀ n : ℕ, 0 < n -> 2 ≤ n ->
      P n = finiteProductFromTwo pTerm n := by
  sorry

theorem proof_gap_exercise_3052_2
    (p P : ℕ -> ℝ)
    (hp : ∀ n : ℕ, 2 ≤ n -> p n = pTerm n)
    (hP : ∀ n : ℕ, 2 ≤ n -> P n = finiteProductFromTwo p n)
    (hprod : ∀ n : ℕ, 0 < n -> 2 ≤ n ->
      P n = finiteProductFromTwo pTerm n) :
    ∀ n : ℕ, 0 < n -> 2 ≤ n ->
      P n = (2 / 3 : ℝ) * (((n : ℝ) ^ 2 + n + 1) / ((n : ℝ) * (n + 1))) := by
  sorry

theorem proof_gap_exercise_3052_3
    (p P : ℕ -> ℝ)
    (hclosed : ∀ n : ℕ, 0 < n -> 2 ≤ n ->
      P n = (2 / 3 : ℝ) * (((n : ℝ) ^ 2 + n + 1) / ((n : ℝ) * (n + 1)))) :
    Filter.Tendsto P Filter.atTop (𝓝 (2 / 3 : ℝ)) := by
  sorry

theorem proof_gap_exercise_3052_4
    (p P : ℕ -> ℝ)
    (hp : ∀ n : ℕ, 2 ≤ n -> p n = pTerm n)
    (hlim : Filter.Tendsto P Filter.atTop (𝓝 (2 / 3 : ℝ)))
    (hpartials : ∀ n : ℕ, 2 ≤ n -> P n = finiteProductFromTwo pTerm n) :
    infiniteProductFromTwo pTerm (2 / 3 : ℝ) := by
  sorry

theorem proof_gap_exercise_3052_5
    (p P : ℕ -> ℝ)
    (hprod : infiniteProductFromTwo pTerm (2 / 3 : ℝ)) :
    infiniteProductFromTwo pTerm (2 / 3 : ℝ) := by
  sorry

end Exercise_3052

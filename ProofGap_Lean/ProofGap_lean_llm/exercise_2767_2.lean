import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology
open Filter

def lpConvergentSeriesTo (a : ℕ -> ℝ) (L : ℝ) : Prop :=
  Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), a n) atTop (𝓝 L)

def lpUniformConvergentSeriesOn (a : ℕ -> ℝ -> ℝ) (s : Set ℝ) (g : ℝ -> ℝ) : Prop :=
  TendstoUniformlyOn (fun N x => ∑ n ∈ Finset.range (N + 1), a n x) g atTop s

noncomputable def lpRootTwo (n : ℕ) : ℝ :=
  (2 : ℝ) ^ (1 / ((n + 1 : ℕ) : ℝ))

-- exercise: exercise_2767_2

theorem proof_gap_exercise_2767_2_1
  (S : ℝ -> ℝ) (P : ℕ × ℝ -> ℝ)
  (hPsum : ∀ (n : ℕ) (x : ℝ) (k : ℕ), n ∈ (Set.univ : Set ℕ) ∧ x ∈ (Set.univ : Set ℝ) ∧ x ≠ 1 ∧ k ∈ (Set.univ : Set ℕ) ∧ k ≤ n -> P (n, x) = ∑ k ∈ Finset.range (n + 1), x ^ k)
  : ∀ (n : ℕ) (x : ℝ), n ∈ (Set.univ : Set ℕ) ∧ x ∈ (Set.univ : Set ℝ) ∧ x ≠ 1 -> P (n, x) = (1 - x ^ (n + 1)) / (1 - x) := by
  sorry

theorem proof_gap_exercise_2767_2_2
  (S : ℝ -> ℝ) (P : ℕ × ℝ -> ℝ)
  (h1 : ∀ (n : ℕ) (x : ℝ), n ∈ (Set.univ : Set ℕ) ∧ x ∈ (Set.univ : Set ℝ) ∧ x ≠ 1 -> P (n, x) = (1 - x ^ (n + 1)) / (1 - x))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ |x| < 1 -> Tendsto (fun n : ℕ => P (n, x)) atTop (𝓝 (1 / (1 - x))) := by
  sorry

theorem proof_gap_exercise_2767_2_3
  (S : ℝ -> ℝ) (P : ℕ × ℝ -> ℝ)
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ |x| < 1 -> Tendsto (fun n : ℕ => P (n, x)) atTop (𝓝 (1 / (1 - x))))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ |x| < 1 -> S x = 1 / (1 - x) := by
  sorry

theorem proof_gap_exercise_2767_2_4
  (S : ℝ -> ℝ) (P : ℕ × ℝ -> ℝ)
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ |x| < 1 -> S x = 1 / (1 - x))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ |x| < 1 -> lpConvergentSeriesTo (fun n : ℕ => x ^ n) (1 / (1 - x)) := by
  sorry

theorem proof_gap_exercise_2767_2_5
  (S : ℝ -> ℝ) (P : ℕ × ℝ -> ℝ)
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ |x| < 1 -> lpConvergentSeriesTo (fun n : ℕ => x ^ n) (1 / (1 - x)))
  : ∃ ε0 : ℝ, ε0 ∈ (Set.univ : Set ℝ) ∧ ε0 = 1 / 2 ∧ ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ 0 < n -> ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x = 1 / lpRootTwo n ∧ |x| < 1 := by
  sorry

theorem proof_gap_exercise_2767_2_6
  (S : ℝ -> ℝ) (P : ℕ × ℝ -> ℝ)
  (h5 : ∃ ε0 : ℝ, ε0 ∈ (Set.univ : Set ℝ) ∧ ε0 = 1 / 2 ∧ ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ 0 < n -> ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x = 1 / lpRootTwo n ∧ |x| < 1)
  : ∃ ε0 : ℝ, ε0 ∈ (Set.univ : Set ℝ) ∧ ε0 = 1 / 2 ∧ ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ 0 < n -> ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x = 1 / lpRootTwo n ∧ |P (n, x) - S x| = |(1 / 2) / (1 - (lpRootTwo n)⁻¹)| := by
  sorry

theorem proof_gap_exercise_2767_2_7
  (S : ℝ -> ℝ) (P : ℕ × ℝ -> ℝ)
  (h6 : ∃ ε0 : ℝ, ε0 ∈ (Set.univ : Set ℝ) ∧ ε0 = 1 / 2 ∧ ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ 0 < n -> ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x = 1 / lpRootTwo n ∧ |P (n, x) - S x| = |(1 / 2) / (1 - (lpRootTwo n)⁻¹)|)
  : ∃ ε0 : ℝ, ε0 ∈ (Set.univ : Set ℝ) ∧ ε0 = 1 / 2 ∧ ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ 0 < n -> ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x = 1 / lpRootTwo n ∧ |(1 / 2) / (1 - (lpRootTwo n)⁻¹)| > 1 / 2 := by
  sorry

theorem proof_gap_exercise_2767_2_8
  (S : ℝ -> ℝ) (P : ℕ × ℝ -> ℝ)
  (h7 : ∃ ε0 : ℝ, ε0 ∈ (Set.univ : Set ℝ) ∧ ε0 = 1 / 2 ∧ ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ 0 < n -> ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x = 1 / lpRootTwo n ∧ |(1 / 2) / (1 - (lpRootTwo n)⁻¹)| > 1 / 2)
  : ∃ ε0 : ℝ, ε0 ∈ (Set.univ : Set ℝ) ∧ ε0 = 1 / 2 ∧ ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ 0 < n -> ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x = 1 / lpRootTwo n ∧ (1 / 2 : ℝ) ≥ ε0 := by
  sorry

theorem proof_gap_exercise_2767_2_9
  (S : ℝ -> ℝ) (P : ℕ × ℝ -> ℝ)
  (h6 : ∃ ε0 : ℝ, ε0 ∈ (Set.univ : Set ℝ) ∧ ε0 = 1 / 2 ∧ ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ 0 < n -> ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x = 1 / lpRootTwo n ∧ |P (n, x) - S x| = |(1 / 2) / (1 - (lpRootTwo n)⁻¹)|)
  (h8 : ∃ ε0 : ℝ, ε0 ∈ (Set.univ : Set ℝ) ∧ ε0 = 1 / 2 ∧ ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ 0 < n -> ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x = 1 / lpRootTwo n ∧ (1 / 2 : ℝ) ≥ ε0)
  : ∃ ε0 : ℝ, ε0 ∈ (Set.univ : Set ℝ) ∧ ε0 = 1 / 2 ∧ ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ 0 < n -> ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x = 1 / lpRootTwo n ∧ |P (n, x) - S x| > ε0 := by
  sorry

theorem proof_gap_exercise_2767_2_10
  (S : ℝ -> ℝ) (P : ℕ × ℝ -> ℝ)
  (h9 : ∃ ε0 : ℝ, ε0 ∈ (Set.univ : Set ℝ) ∧ ε0 = 1 / 2 ∧ ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ 0 < n -> ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x = 1 / lpRootTwo n ∧ |P (n, x) - S x| > ε0)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ |x| < 1 -> ¬ lpUniformConvergentSeriesOn (fun n x => x ^ n) {x : ℝ | x ∈ (Set.univ : Set ℝ) ∧ |x| < 1} S := by
  sorry

theorem proof_gap_exercise_2767_2_11
  (S : ℝ -> ℝ) (P : ℕ × ℝ -> ℝ)
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ |x| < 1 -> lpConvergentSeriesTo (fun n : ℕ => x ^ n) (1 / (1 - x)))
  (h10 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ |x| < 1 -> ¬ lpUniformConvergentSeriesOn (fun n x => x ^ n) {x : ℝ | x ∈ (Set.univ : Set ℝ) ∧ |x| < 1} S)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ |x| < 1 -> lpConvergentSeriesTo (fun n : ℕ => x ^ n) (1 / (1 - x)) ∧ ¬ lpUniformConvergentSeriesOn (fun n x => x ^ n) {x : ℝ | x ∈ (Set.univ : Set ℝ) ∧ |x| < 1} S := by
  sorry

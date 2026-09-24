import Mathlib

attribute [local instance] Classical.propDecidable
set_option linter.style.longLine false

open Filter
open scoped Topology BigOperators

noncomputable def lpRadiusOfConvergence (a : ℕ → ℝ) : ℝ :=
  sSup {r : ℝ | 0 ≤ r ∧ ∀ x : ℝ, |x| < r → Summable (fun n : ℕ => a n * x ^ n)}

def lpDivergentSeries (u : ℕ → ℝ) : Prop := ¬ Summable u

noncomputable def cosLogCoeff (n : ℕ) : ℝ :=
  ((1 + 2 * Real.cos (Real.pi * (n : ℝ) / (4 : ℝ))) ^ n) / Real.log n

noncomputable def cosLogResidueTerm (x : ℝ) (r k : ℕ) : ℝ :=
  (((1 + 2 * Real.cos (((8 * k + r : ℕ) : ℝ) * Real.pi / (4 : ℝ))) ^ (8 * k + r)) / Real.log (8 * k + r)) *
    x ^ (8 * k + r)

-- exercise: exercise_2829
-- Exercise 2829

theorem proof_gap_exercise_2829_1 (a : ℕ → ℝ) (x : ℝ)
  (ha : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ 2 ≤ n → a n = cosLogCoeff n) :
  Tendsto (fun n : ℕ => (|a n|) ^ ((1 : ℝ) / (n : ℝ))) atTop (𝓝 3) := by
  sorry

theorem proof_gap_exercise_2829_2 (a : ℕ → ℝ) (x : ℝ)
  (ha : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ 2 ≤ n → a n = cosLogCoeff n)
  (h4 : Tendsto (fun n : ℕ => (|a n|) ^ ((1 : ℝ) / (n : ℝ))) atTop (𝓝 3)) :
  lpRadiusOfConvergence a = (1 : ℝ) / (3 : ℝ) := by
  sorry

theorem proof_gap_exercise_2829_3 (a : ℕ → ℝ) (x : ℝ)
  (hR : lpRadiusOfConvergence a = (1 : ℝ) / (3 : ℝ)) :
  ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ |y| < (1 : ℝ) / (3 : ℝ) →
    Summable (fun n : ℕ => if 2 ≤ n then a n * y ^ n else 0) := by
  sorry

theorem proof_gap_exercise_2829_4 (a : ℕ → ℝ) (x : ℝ) :
  |x| = (1 : ℝ) / (3 : ℝ) →
    (∑' k : ℕ, if 1 ≤ k then (((1 + 2 * Real.cos (2 * (k : ℝ) * Real.pi)) ^ (8 * k)) / Real.log (8 * k)) * ((1 : ℝ) / ((3 : ℝ) ^ (8 * k))) else 0) =
    (∑' k : ℕ, if 1 ≤ k then (1 : ℝ) / (Real.log k + Real.log 8) else 0) := by
  sorry

theorem proof_gap_exercise_2829_5 (a : ℕ → ℝ) (x : ℝ) :
  |x| = (1 : ℝ) / (3 : ℝ) → ∀ k : ℕ, k ∈ (Set.univ : Set ℕ) ∧ k ∈ {m : ℕ | 0 < m} →
    ((1 : ℝ) / (Real.log k + Real.log 8)) > ((1 : ℝ) / ((k : ℝ) + Real.log 8)) ∧
      ((1 : ℝ) / ((k : ℝ) + Real.log 8)) > 0 := by
  sorry

theorem proof_gap_exercise_2829_6 (a : ℕ → ℝ) (x : ℝ) :
  |x| = (1 : ℝ) / (3 : ℝ) → lpDivergentSeries (fun k : ℕ => if 1 ≤ k then (1 : ℝ) / ((k : ℝ) + Real.log 8) else 0) := by
  sorry

theorem proof_gap_exercise_2829_7 (a : ℕ → ℝ) (x : ℝ)
  (h8 : |x| = (1 : ℝ) / (3 : ℝ) → ∀ k : ℕ, k ∈ (Set.univ : Set ℕ) ∧ k ∈ {m : ℕ | 0 < m} →
    ((1 : ℝ) / (Real.log k + Real.log 8)) > ((1 : ℝ) / ((k : ℝ) + Real.log 8)) ∧
      ((1 : ℝ) / ((k : ℝ) + Real.log 8)) > 0)
  (h9 : |x| = (1 : ℝ) / (3 : ℝ) → lpDivergentSeries (fun k : ℕ => if 1 ≤ k then (1 : ℝ) / ((k : ℝ) + Real.log 8) else 0)) :
  |x| = (1 : ℝ) / (3 : ℝ) → lpDivergentSeries (fun k : ℕ => if 1 ≤ k then (1 : ℝ) / (Real.log k + Real.log 8) else 0) := by
  sorry

theorem proof_gap_exercise_2829_8 (a : ℕ → ℝ) (x : ℝ) :
  |x| = (1 : ℝ) / (3 : ℝ) → ∀ r : ℕ, r ∈ (Set.univ : Set ℕ) ∧ r ∈ ({1, 2, 3, 4, 5, 6, 7} : Finset ℕ) →
    Summable (fun k : ℕ => if 1 ≤ k then cosLogResidueTerm x r k else 0) := by
  sorry

theorem proof_gap_exercise_2829_9 (a : ℕ → ℝ) (x : ℝ)
  (h10 : |x| = (1 : ℝ) / (3 : ℝ) → lpDivergentSeries (fun k : ℕ => if 1 ≤ k then (1 : ℝ) / (Real.log k + Real.log 8) else 0))
  (h11 : |x| = (1 : ℝ) / (3 : ℝ) → ∀ r : ℕ, r ∈ (Set.univ : Set ℕ) ∧ r ∈ ({1, 2, 3, 4, 5, 6, 7} : Finset ℕ) →
    Summable (fun k : ℕ => if 1 ≤ k then cosLogResidueTerm x r k else 0)) :
  |x| = (1 : ℝ) / (3 : ℝ) → lpDivergentSeries (fun n : ℕ => if 2 ≤ n then a n * x ^ n else 0) := by
  sorry

theorem proof_gap_exercise_2829_10 (a : ℕ → ℝ) (x : ℝ)
  (h6 : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ |y| < (1 : ℝ) / (3 : ℝ) →
    Summable (fun n : ℕ => if 2 ≤ n then a n * y ^ n else 0))
  (h12 : |x| = (1 : ℝ) / (3 : ℝ) → lpDivergentSeries (fun n : ℕ => if 2 ≤ n then a n * x ^ n else 0)) :
  x ∈ Set.Ioo (-((1 : ℝ) / (3 : ℝ))) ((1 : ℝ) / (3 : ℝ)) ↔
    Summable (fun n : ℕ => if 2 ≤ n then a n * x ^ n else 0) := by
  sorry

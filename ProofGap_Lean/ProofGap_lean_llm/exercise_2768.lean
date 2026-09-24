import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

def ConvergentSeries (a : ℕ -> ℝ) : Prop := Summable a
def AbsoluteConvergentSeries (a : ℕ -> ℝ) : Prop := Summable (fun n => ‖a n‖)
def UniformConvergentSeriesOn (a : ℕ -> ℝ -> ℝ) (s : Set ℝ) : Prop :=
  ∃ g : ℝ -> ℝ, TendstoUniformlyOn (fun N x => (∑ k ∈ Finset.Icc 1 N, a k x)) g atTop s

-- exercise: exercise_2768

-- GAP 1
theorem proof_gap_exercise_2768_1 :
    ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) →
      ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x ∈ Set.Icc (-1 : ℝ) 1 ∧ n ∈ ({m : ℕ | 0 < m}) →
        |(x ^ n) /. (n ^ 2)| ≤ 1 /. (n ^ 2) := by
  sorry

-- GAP 2
theorem proof_gap_exercise_2768_2
    (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) →
      ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x ∈ Set.Icc (-1 : ℝ) 1 ∧ n ∈ ({m : ℕ | 0 < m}) →
        |(x ^ n) /. (n ^ 2)| ≤ 1 /. (n ^ 2)) :
    ConvergentSeries (fun n : ℕ => if 1 ≤ n then 1 /. (n ^ 2) else 0) := by
  sorry

-- GAP 3
theorem proof_gap_exercise_2768_3
    (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) →
      ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x ∈ Set.Icc (-1 : ℝ) 1 ∧ n ∈ ({m : ℕ | 0 < m}) →
        |(x ^ n) /. (n ^ 2)| ≤ 1 /. (n ^ 2))
    (h2 : ConvergentSeries (fun n : ℕ => if 1 ≤ n then 1 /. (n ^ 2) else 0)) :
    ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Icc (-1 : ℝ) 1 →
      AbsoluteConvergentSeries (fun n : ℕ => if 1 ≤ n then (x ^ n) /. (n ^ 2) else 0) := by
  sorry

-- GAP 4
theorem proof_gap_exercise_2768_4
    (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) →
      ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x ∈ Set.Icc (-1 : ℝ) 1 ∧ n ∈ ({m : ℕ | 0 < m}) →
        |(x ^ n) /. (n ^ 2)| ≤ 1 /. (n ^ 2))
    (h2 : ConvergentSeries (fun n : ℕ => if 1 ≤ n then 1 /. (n ^ 2) else 0))
    (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Icc (-1 : ℝ) 1 →
      AbsoluteConvergentSeries (fun n : ℕ => if 1 ≤ n then (x ^ n) /. (n ^ 2) else 0)) :
    UniformConvergentSeriesOn (fun n x => (x ^ n) /. (n ^ 2)) (Set.Icc (-1 : ℝ) 1) := by
  sorry

-- GAP 5
theorem proof_gap_exercise_2768_5
    (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Icc (-1 : ℝ) 1 →
      AbsoluteConvergentSeries (fun n : ℕ => if 1 ≤ n then (x ^ n) /. (n ^ 2) else 0))
    (h4 : UniformConvergentSeriesOn (fun n x => (x ^ n) /. (n ^ 2)) (Set.Icc (-1 : ℝ) 1)) :
    (∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Icc (-1 : ℝ) 1 →
      AbsoluteConvergentSeries (fun n : ℕ => if 1 ≤ n then (x ^ n) /. (n ^ 2) else 0)) ∧
      UniformConvergentSeriesOn (fun n x => (x ^ n) /. (n ^ 2)) (Set.Icc (-1 : ℝ) 1) := by
  sorry

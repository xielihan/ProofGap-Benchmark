import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology
open Filter

def lpConvergentSeries (a : ℕ -> ℝ) : Prop := Summable a
def lpAbsoluteConvergentSeries (a : ℕ -> ℝ) : Prop := Summable fun n => |a n|
def lpUniformConvergentSeriesOn (a : ℕ -> ℝ -> ℝ) (s : Set ℝ) (g : ℝ -> ℝ) : Prop :=
  TendstoUniformlyOn (fun N x => ∑ n ∈ Finset.range (N + 1), a n x) g atTop s

-- exercise: exercise_2767_1

theorem proof_gap_exercise_2767_1_1 (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ |x| < q -> ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) -> |x ^ n| < q ^ n := by
  sorry

theorem proof_gap_exercise_2767_1_2 (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ |x| < q -> ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) -> |x ^ n| < q ^ n)
  : lpConvergentSeries fun n : ℕ => q ^ n := by
  sorry

theorem proof_gap_exercise_2767_1_3 (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ |x| < q -> ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) -> |x ^ n| < q ^ n)
  (h2 : lpConvergentSeries fun n : ℕ => q ^ n)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ |x| < q -> lpAbsoluteConvergentSeries fun n : ℕ => x ^ n := by
  sorry

theorem proof_gap_exercise_2767_1_4 (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ |x| < q -> ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) -> |x ^ n| < q ^ n)
  (h2 : lpConvergentSeries fun n : ℕ => q ^ n)
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ |x| < q -> lpAbsoluteConvergentSeries fun n : ℕ => x ^ n)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ |x| < q -> lpUniformConvergentSeriesOn (fun n x => x ^ n) {x : ℝ | x ∈ (Set.univ : Set ℝ) ∧ |x| < q} (fun x => 1 / (1 - x)) := by
  sorry

theorem proof_gap_exercise_2767_1_5 (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ |x| < q -> lpAbsoluteConvergentSeries fun n : ℕ => x ^ n)
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ |x| < q -> lpUniformConvergentSeriesOn (fun n x => x ^ n) {x : ℝ | x ∈ (Set.univ : Set ℝ) ∧ |x| < q} (fun x => 1 / (1 - x)))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ |x| < q -> lpAbsoluteConvergentSeries (fun n : ℕ => x ^ n) ∧ lpUniformConvergentSeriesOn (fun n x => x ^ n) {x : ℝ | x ∈ (Set.univ : Set ℝ) ∧ |x| < q} (fun x => 1 / (1 - x)) := by
  sorry

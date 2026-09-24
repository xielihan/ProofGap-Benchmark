import Mathlib

attribute [local instance] Classical.propDecidable

set_option linter.style.longLine false

open Filter
open scoped BigOperators Topology

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

noncomputable def lpRadiusOfConvergence (a : ℕ → ℝ) : ENNReal :=
  ⨆ (r : NNReal), ⨆ (_h : Summable (fun n : ℕ => ‖a n‖ * (r : ℝ) ^ n)), (r : ENNReal)

def lpConditionalConvergent (u : ℕ → ℝ) : Prop :=
  Summable u ∧ ¬ Summable (fun n : ℕ => ‖u n‖)

def lpDivergentSeries (u : ℕ → ℝ) : Prop :=
  ¬ Summable u

abbrev posNatSet : Set ℕ := {n : ℕ | 0 < n}

-- exercise: exercise_2813

-- Exercise 2813, gap 1
theorem proof_gap_exercise_2813_1
  (x : ℝ)
  (a : ℕ → ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ posNatSet → a n = ((3 : ℝ) ^ n + (-2 : ℝ) ^ n) /. n)
  : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => |((a k) /. (a (k + 1)))|) atTop (𝓝 ((1 : ℝ) / 3)) := by
  sorry

-- Exercise 2813, gap 2
theorem proof_gap_exercise_2813_2
  (x : ℝ)
  (a : ℕ → ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ posNatSet → a n = ((3 : ℝ) ^ n + (-2 : ℝ) ^ n) /. n)
  (h3 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => |((a k) /. (a (k + 1)))|) atTop (𝓝 ((1 : ℝ) / 3)))
  : (lpRadiusOfConvergence a) = ((1 : ENNReal) / 3) := by
  sorry

-- Exercise 2813, gap 3
theorem proof_gap_exercise_2813_3
  (x : ℝ)
  (a : ℕ → ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ posNatSet → a n = ((3 : ℝ) ^ n + (-2 : ℝ) ^ n) /. n)
  (h3 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => |((a k) /. (a (k + 1)))|) atTop (𝓝 ((1 : ℝ) / 3)))
  (h4 : (lpRadiusOfConvergence a) = ((1 : ENNReal) / 3))
  : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ (-1 - (1 : ℝ) / 3 < x) ∧ (x < -1 + (1 : ℝ) / 3) → Summable (fun k : ℕ => if 1 ≤ k then a k * (x + 1) ^ k else 0) := by
  sorry

-- Exercise 2813, gap 4
theorem proof_gap_exercise_2813_4
  (x : ℝ)
  (a : ℕ → ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ posNatSet → a n = ((3 : ℝ) ^ n + (-2 : ℝ) ^ n) /. n)
  (h3 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => |((a k) /. (a (k + 1)))|) atTop (𝓝 ((1 : ℝ) / 3)))
  (h4 : (lpRadiusOfConvergence a) = ((1 : ENNReal) / 3))
  (h5 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ (-1 - (1 : ℝ) / 3 < x) ∧ (x < -1 + (1 : ℝ) / 3) → Summable (fun k : ℕ => if 1 ≤ k then a k * (x + 1) ^ k else 0))
  : Set.Ioo (-1 - (1 : ℝ) / 3) (-1 + (1 : ℝ) / 3) = Set.Ioo (-(4 : ℝ) / 3) (-(2 : ℝ) / 3) := by
  sorry

-- Exercise 2813, gap 5
theorem proof_gap_exercise_2813_5
  (x : ℝ)
  (a : ℕ → ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ posNatSet → a n = ((3 : ℝ) ^ n + (-2 : ℝ) ^ n) /. n)
  (h3 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => |((a k) /. (a (k + 1)))|) atTop (𝓝 ((1 : ℝ) / 3)))
  (h4 : (lpRadiusOfConvergence a) = ((1 : ENNReal) / 3))
  (h5 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ (-1 - (1 : ℝ) / 3 < x) ∧ (x < -1 + (1 : ℝ) / 3) → Summable (fun k : ℕ => if 1 ≤ k then a k * (x + 1) ^ k else 0))
  (h6 : Set.Ioo (-1 - (1 : ℝ) / 3) (-1 + (1 : ℝ) / 3) = Set.Ioo (-(4 : ℝ) / 3) (-(2 : ℝ) / 3))
  : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → (∑' k, if 1 ≤ k then (((3 : ℝ) ^ k + (-2 : ℝ) ^ k) /. k) * (x + 1) ^ k else 0) = (∑' k, if 1 ≤ k then (((-1 : ℝ) ^ k + ((2 : ℝ) / 3) ^ k) /. k) else 0) := by
  sorry

-- Exercise 2813, gap 6
theorem proof_gap_exercise_2813_6
  (x : ℝ)
  (a : ℕ → ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ posNatSet → a n = ((3 : ℝ) ^ n + (-2 : ℝ) ^ n) /. n)
  (h3 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => |((a k) /. (a (k + 1)))|) atTop (𝓝 ((1 : ℝ) / 3)))
  (h4 : (lpRadiusOfConvergence a) = ((1 : ENNReal) / 3))
  (h5 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ (-1 - (1 : ℝ) / 3 < x) ∧ (x < -1 + (1 : ℝ) / 3) → Summable (fun k : ℕ => if 1 ≤ k then a k * (x + 1) ^ k else 0))
  (h6 : Set.Ioo (-1 - (1 : ℝ) / 3) (-1 + (1 : ℝ) / 3) = Set.Ioo (-(4 : ℝ) / 3) (-(2 : ℝ) / 3))
  (h7 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → (∑' k, if 1 ≤ k then (((3 : ℝ) ^ k + (-2 : ℝ) ^ k) /. k) * (x + 1) ^ k else 0) = (∑' k, if 1 ≤ k then (((-1 : ℝ) ^ k + ((2 : ℝ) / 3) ^ k) /. k) else 0))
  : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → (∑' k, if 1 ≤ k then (((-1 : ℝ) ^ k + ((2 : ℝ) / 3) ^ k) /. k) else 0) = (∑' k, if 1 ≤ k then ((-1 : ℝ) ^ k) /. k else 0) + (∑' k, if 1 ≤ k then (((2 : ℝ) / 3) ^ k) /. k else 0) := by
  sorry

-- Exercise 2813, gap 7
theorem proof_gap_exercise_2813_7
  (x : ℝ)
  (a : ℕ → ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ posNatSet → a n = ((3 : ℝ) ^ n + (-2 : ℝ) ^ n) /. n)
  (h3 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => |((a k) /. (a (k + 1)))|) atTop (𝓝 ((1 : ℝ) / 3)))
  (h4 : (lpRadiusOfConvergence a) = ((1 : ENNReal) / 3))
  (h5 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ (-1 - (1 : ℝ) / 3 < x) ∧ (x < -1 + (1 : ℝ) / 3) → Summable (fun k : ℕ => if 1 ≤ k then a k * (x + 1) ^ k else 0))
  (h6 : Set.Ioo (-1 - (1 : ℝ) / 3) (-1 + (1 : ℝ) / 3) = Set.Ioo (-(4 : ℝ) / 3) (-(2 : ℝ) / 3))
  (h7 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → (∑' k, if 1 ≤ k then (((3 : ℝ) ^ k + (-2 : ℝ) ^ k) /. k) * (x + 1) ^ k else 0) = (∑' k, if 1 ≤ k then (((-1 : ℝ) ^ k + ((2 : ℝ) / 3) ^ k) /. k) else 0))
  (h8 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → (∑' k, if 1 ≤ k then (((-1 : ℝ) ^ k + ((2 : ℝ) / 3) ^ k) /. k) else 0) = (∑' k, if 1 ≤ k then ((-1 : ℝ) ^ k) /. k else 0) + (∑' k, if 1 ≤ k then (((2 : ℝ) / 3) ^ k) /. k else 0))
  : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → lpConditionalConvergent (fun k : ℕ => if 1 ≤ k then ((-1 : ℝ) ^ k) /. k else 0) := by
  sorry

-- Exercise 2813, gap 8
theorem proof_gap_exercise_2813_8
  (x : ℝ)
  (a : ℕ → ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ posNatSet → a n = ((3 : ℝ) ^ n + (-2 : ℝ) ^ n) /. n)
  (h3 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => |((a k) /. (a (k + 1)))|) atTop (𝓝 ((1 : ℝ) / 3)))
  (h4 : (lpRadiusOfConvergence a) = ((1 : ENNReal) / 3))
  (h5 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ (-1 - (1 : ℝ) / 3 < x) ∧ (x < -1 + (1 : ℝ) / 3) → Summable (fun k : ℕ => if 1 ≤ k then a k * (x + 1) ^ k else 0))
  (h6 : Set.Ioo (-1 - (1 : ℝ) / 3) (-1 + (1 : ℝ) / 3) = Set.Ioo (-(4 : ℝ) / 3) (-(2 : ℝ) / 3))
  (h7 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → (∑' k, if 1 ≤ k then (((3 : ℝ) ^ k + (-2 : ℝ) ^ k) /. k) * (x + 1) ^ k else 0) = (∑' k, if 1 ≤ k then (((-1 : ℝ) ^ k + ((2 : ℝ) / 3) ^ k) /. k) else 0))
  (h8 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → (∑' k, if 1 ≤ k then (((-1 : ℝ) ^ k + ((2 : ℝ) / 3) ^ k) /. k) else 0) = (∑' k, if 1 ≤ k then ((-1 : ℝ) ^ k) /. k else 0) + (∑' k, if 1 ≤ k then (((2 : ℝ) / 3) ^ k) /. k else 0))
  (h9 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → lpConditionalConvergent (fun k : ℕ => if 1 ≤ k then ((-1 : ℝ) ^ k) /. k else 0))
  : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → Tendsto (fun k : ℕ => (((((2 : ℝ) / 3) ^ (k + 1)) /. (k + 1)) /. ((((2 : ℝ) / 3) ^ k) /. k))) atTop (𝓝 ((2 : ℝ) / 3)) := by
  sorry

-- Exercise 2813, gap 9
theorem proof_gap_exercise_2813_9
  (x : ℝ)
  (a : ℕ → ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ posNatSet → a n = ((3 : ℝ) ^ n + (-2 : ℝ) ^ n) /. n)
  (h3 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => |((a k) /. (a (k + 1)))|) atTop (𝓝 ((1 : ℝ) / 3)))
  (h4 : (lpRadiusOfConvergence a) = ((1 : ENNReal) / 3))
  (h5 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ (-1 - (1 : ℝ) / 3 < x) ∧ (x < -1 + (1 : ℝ) / 3) → Summable (fun k : ℕ => if 1 ≤ k then a k * (x + 1) ^ k else 0))
  (h6 : Set.Ioo (-1 - (1 : ℝ) / 3) (-1 + (1 : ℝ) / 3) = Set.Ioo (-(4 : ℝ) / 3) (-(2 : ℝ) / 3))
  (h7 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → (∑' k, if 1 ≤ k then (((3 : ℝ) ^ k + (-2 : ℝ) ^ k) /. k) * (x + 1) ^ k else 0) = (∑' k, if 1 ≤ k then (((-1 : ℝ) ^ k + ((2 : ℝ) / 3) ^ k) /. k) else 0))
  (h8 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → (∑' k, if 1 ≤ k then (((-1 : ℝ) ^ k + ((2 : ℝ) / 3) ^ k) /. k) else 0) = (∑' k, if 1 ≤ k then ((-1 : ℝ) ^ k) /. k else 0) + (∑' k, if 1 ≤ k then (((2 : ℝ) / 3) ^ k) /. k else 0))
  (h9 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → lpConditionalConvergent (fun k : ℕ => if 1 ≤ k then ((-1 : ℝ) ^ k) /. k else 0))
  (h10 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → Tendsto (fun k : ℕ => (((((2 : ℝ) / 3) ^ (k + 1)) /. (k + 1)) /. ((((2 : ℝ) / 3) ^ k) /. k))) atTop (𝓝 ((2 : ℝ) / 3)))
  : x = -(4 : ℝ) / 3 → ((2 : ℝ) / 3) < 1 := by
  sorry

-- Exercise 2813, gap 10
theorem proof_gap_exercise_2813_10
  (x : ℝ)
  (a : ℕ → ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ posNatSet → a n = ((3 : ℝ) ^ n + (-2 : ℝ) ^ n) /. n)
  (h3 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => |((a k) /. (a (k + 1)))|) atTop (𝓝 ((1 : ℝ) / 3)))
  (h4 : (lpRadiusOfConvergence a) = ((1 : ENNReal) / 3))
  (h5 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ (-1 - (1 : ℝ) / 3 < x) ∧ (x < -1 + (1 : ℝ) / 3) → Summable (fun k : ℕ => if 1 ≤ k then a k * (x + 1) ^ k else 0))
  (h6 : Set.Ioo (-1 - (1 : ℝ) / 3) (-1 + (1 : ℝ) / 3) = Set.Ioo (-(4 : ℝ) / 3) (-(2 : ℝ) / 3))
  (h7 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → (∑' k, if 1 ≤ k then (((3 : ℝ) ^ k + (-2 : ℝ) ^ k) /. k) * (x + 1) ^ k else 0) = (∑' k, if 1 ≤ k then (((-1 : ℝ) ^ k + ((2 : ℝ) / 3) ^ k) /. k) else 0))
  (h8 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → (∑' k, if 1 ≤ k then (((-1 : ℝ) ^ k + ((2 : ℝ) / 3) ^ k) /. k) else 0) = (∑' k, if 1 ≤ k then ((-1 : ℝ) ^ k) /. k else 0) + (∑' k, if 1 ≤ k then (((2 : ℝ) / 3) ^ k) /. k else 0))
  (h9 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → lpConditionalConvergent (fun k : ℕ => if 1 ≤ k then ((-1 : ℝ) ^ k) /. k else 0))
  (h10 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → Tendsto (fun k : ℕ => (((((2 : ℝ) / 3) ^ (k + 1)) /. (k + 1)) /. ((((2 : ℝ) / 3) ^ k) /. k))) atTop (𝓝 ((2 : ℝ) / 3)))
  (h11 : x = -(4 : ℝ) / 3 → ((2 : ℝ) / 3) < 1)
  : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → ∃ L : ℝ, Tendsto (fun k : ℕ => (((((2 : ℝ) / 3) ^ (k + 1)) /. (k + 1)) /. ((((2 : ℝ) / 3) ^ k) /. k))) atTop (𝓝 L) ∧ L < 1 := by
  sorry

-- Exercise 2813, gap 11
theorem proof_gap_exercise_2813_11
  (x : ℝ)
  (a : ℕ → ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ posNatSet → a n = ((3 : ℝ) ^ n + (-2 : ℝ) ^ n) /. n)
  (h3 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => |((a k) /. (a (k + 1)))|) atTop (𝓝 ((1 : ℝ) / 3)))
  (h4 : (lpRadiusOfConvergence a) = ((1 : ENNReal) / 3))
  (h5 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ (-1 - (1 : ℝ) / 3 < x) ∧ (x < -1 + (1 : ℝ) / 3) → Summable (fun k : ℕ => if 1 ≤ k then a k * (x + 1) ^ k else 0))
  (h6 : Set.Ioo (-1 - (1 : ℝ) / 3) (-1 + (1 : ℝ) / 3) = Set.Ioo (-(4 : ℝ) / 3) (-(2 : ℝ) / 3))
  (h7 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → (∑' k, if 1 ≤ k then (((3 : ℝ) ^ k + (-2 : ℝ) ^ k) /. k) * (x + 1) ^ k else 0) = (∑' k, if 1 ≤ k then (((-1 : ℝ) ^ k + ((2 : ℝ) / 3) ^ k) /. k) else 0))
  (h8 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → (∑' k, if 1 ≤ k then (((-1 : ℝ) ^ k + ((2 : ℝ) / 3) ^ k) /. k) else 0) = (∑' k, if 1 ≤ k then ((-1 : ℝ) ^ k) /. k else 0) + (∑' k, if 1 ≤ k then (((2 : ℝ) / 3) ^ k) /. k else 0))
  (h9 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → lpConditionalConvergent (fun k : ℕ => if 1 ≤ k then ((-1 : ℝ) ^ k) /. k else 0))
  (h10 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → Tendsto (fun k : ℕ => (((((2 : ℝ) / 3) ^ (k + 1)) /. (k + 1)) /. ((((2 : ℝ) / 3) ^ k) /. k))) atTop (𝓝 ((2 : ℝ) / 3)))
  (h11 : x = -(4 : ℝ) / 3 → ((2 : ℝ) / 3) < 1)
  (h12 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → ∃ L : ℝ, Tendsto (fun k : ℕ => (((((2 : ℝ) / 3) ^ (k + 1)) /. (k + 1)) /. ((((2 : ℝ) / 3) ^ k) /. k))) atTop (𝓝 L) ∧ L < 1)
  : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → Summable (fun k : ℕ => if 1 ≤ k then (((2 : ℝ) / 3) ^ k) /. k else 0) := by
  sorry

-- Exercise 2813, gap 12
theorem proof_gap_exercise_2813_12
  (x : ℝ)
  (a : ℕ → ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ posNatSet → a n = ((3 : ℝ) ^ n + (-2 : ℝ) ^ n) /. n)
  (h3 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => |((a k) /. (a (k + 1)))|) atTop (𝓝 ((1 : ℝ) / 3)))
  (h4 : (lpRadiusOfConvergence a) = ((1 : ENNReal) / 3))
  (h5 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ (-1 - (1 : ℝ) / 3 < x) ∧ (x < -1 + (1 : ℝ) / 3) → Summable (fun k : ℕ => if 1 ≤ k then a k * (x + 1) ^ k else 0))
  (h6 : Set.Ioo (-1 - (1 : ℝ) / 3) (-1 + (1 : ℝ) / 3) = Set.Ioo (-(4 : ℝ) / 3) (-(2 : ℝ) / 3))
  (h7 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → (∑' k, if 1 ≤ k then (((3 : ℝ) ^ k + (-2 : ℝ) ^ k) /. k) * (x + 1) ^ k else 0) = (∑' k, if 1 ≤ k then (((-1 : ℝ) ^ k + ((2 : ℝ) / 3) ^ k) /. k) else 0))
  (h8 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → (∑' k, if 1 ≤ k then (((-1 : ℝ) ^ k + ((2 : ℝ) / 3) ^ k) /. k) else 0) = (∑' k, if 1 ≤ k then ((-1 : ℝ) ^ k) /. k else 0) + (∑' k, if 1 ≤ k then (((2 : ℝ) / 3) ^ k) /. k else 0))
  (h9 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → lpConditionalConvergent (fun k : ℕ => if 1 ≤ k then ((-1 : ℝ) ^ k) /. k else 0))
  (h10 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → Tendsto (fun k : ℕ => (((((2 : ℝ) / 3) ^ (k + 1)) /. (k + 1)) /. ((((2 : ℝ) / 3) ^ k) /. k))) atTop (𝓝 ((2 : ℝ) / 3)))
  (h11 : x = -(4 : ℝ) / 3 → ((2 : ℝ) / 3) < 1)
  (h12 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → ∃ L : ℝ, Tendsto (fun k : ℕ => (((((2 : ℝ) / 3) ^ (k + 1)) /. (k + 1)) /. ((((2 : ℝ) / 3) ^ k) /. k))) atTop (𝓝 L) ∧ L < 1)
  (h13 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → Summable (fun k : ℕ => if 1 ≤ k then (((2 : ℝ) / 3) ^ k) /. k else 0))
  : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → lpConditionalConvergent (fun k : ℕ => if 1 ≤ k then (((3 : ℝ) ^ k + (-2 : ℝ) ^ k) /. k) * (x + 1) ^ k else 0) := by
  sorry

-- Exercise 2813, gap 13
theorem proof_gap_exercise_2813_13
  (x : ℝ)
  (a : ℕ → ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ posNatSet → a n = ((3 : ℝ) ^ n + (-2 : ℝ) ^ n) /. n)
  (h3 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => |((a k) /. (a (k + 1)))|) atTop (𝓝 ((1 : ℝ) / 3)))
  (h4 : (lpRadiusOfConvergence a) = ((1 : ENNReal) / 3))
  (h5 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ (-1 - (1 : ℝ) / 3 < x) ∧ (x < -1 + (1 : ℝ) / 3) → Summable (fun k : ℕ => if 1 ≤ k then a k * (x + 1) ^ k else 0))
  (h6 : Set.Ioo (-1 - (1 : ℝ) / 3) (-1 + (1 : ℝ) / 3) = Set.Ioo (-(4 : ℝ) / 3) (-(2 : ℝ) / 3))
  (h7 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → (∑' k, if 1 ≤ k then (((3 : ℝ) ^ k + (-2 : ℝ) ^ k) /. k) * (x + 1) ^ k else 0) = (∑' k, if 1 ≤ k then (((-1 : ℝ) ^ k + ((2 : ℝ) / 3) ^ k) /. k) else 0))
  (h8 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → (∑' k, if 1 ≤ k then (((-1 : ℝ) ^ k + ((2 : ℝ) / 3) ^ k) /. k) else 0) = (∑' k, if 1 ≤ k then ((-1 : ℝ) ^ k) /. k else 0) + (∑' k, if 1 ≤ k then (((2 : ℝ) / 3) ^ k) /. k else 0))
  (h9 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → lpConditionalConvergent (fun k : ℕ => if 1 ≤ k then ((-1 : ℝ) ^ k) /. k else 0))
  (h10 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → Tendsto (fun k : ℕ => (((((2 : ℝ) / 3) ^ (k + 1)) /. (k + 1)) /. ((((2 : ℝ) / 3) ^ k) /. k))) atTop (𝓝 ((2 : ℝ) / 3)))
  (h11 : x = -(4 : ℝ) / 3 → ((2 : ℝ) / 3) < 1)
  (h12 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → ∃ L : ℝ, Tendsto (fun k : ℕ => (((((2 : ℝ) / 3) ^ (k + 1)) /. (k + 1)) /. ((((2 : ℝ) / 3) ^ k) /. k))) atTop (𝓝 L) ∧ L < 1)
  (h13 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → Summable (fun k : ℕ => if 1 ≤ k then (((2 : ℝ) / 3) ^ k) /. k else 0))
  (h14 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → lpConditionalConvergent (fun k : ℕ => if 1 ≤ k then (((3 : ℝ) ^ k + (-2 : ℝ) ^ k) /. k) * (x + 1) ^ k else 0))
  : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(2 : ℝ) / 3 → (∑' k, if 1 ≤ k then (((3 : ℝ) ^ k + (-2 : ℝ) ^ k) /. k) * (x + 1) ^ k else 0) = (∑' k, if 1 ≤ k then (1 : ℝ) /. k else 0) + (∑' k, if 1 ≤ k then ((-((2 : ℝ) / 3)) ^ k) /. k else 0) := by
  sorry

-- Exercise 2813, gap 14
theorem proof_gap_exercise_2813_14
  (x : ℝ)
  (a : ℕ → ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ posNatSet → a n = ((3 : ℝ) ^ n + (-2 : ℝ) ^ n) /. n)
  (h3 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => |((a k) /. (a (k + 1)))|) atTop (𝓝 ((1 : ℝ) / 3)))
  (h4 : (lpRadiusOfConvergence a) = ((1 : ENNReal) / 3))
  (h5 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ (-1 - (1 : ℝ) / 3 < x) ∧ (x < -1 + (1 : ℝ) / 3) → Summable (fun k : ℕ => if 1 ≤ k then a k * (x + 1) ^ k else 0))
  (h6 : Set.Ioo (-1 - (1 : ℝ) / 3) (-1 + (1 : ℝ) / 3) = Set.Ioo (-(4 : ℝ) / 3) (-(2 : ℝ) / 3))
  (h7 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → (∑' k, if 1 ≤ k then (((3 : ℝ) ^ k + (-2 : ℝ) ^ k) /. k) * (x + 1) ^ k else 0) = (∑' k, if 1 ≤ k then (((-1 : ℝ) ^ k + ((2 : ℝ) / 3) ^ k) /. k) else 0))
  (h8 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → (∑' k, if 1 ≤ k then (((-1 : ℝ) ^ k + ((2 : ℝ) / 3) ^ k) /. k) else 0) = (∑' k, if 1 ≤ k then ((-1 : ℝ) ^ k) /. k else 0) + (∑' k, if 1 ≤ k then (((2 : ℝ) / 3) ^ k) /. k else 0))
  (h9 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → lpConditionalConvergent (fun k : ℕ => if 1 ≤ k then ((-1 : ℝ) ^ k) /. k else 0))
  (h10 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → Tendsto (fun k : ℕ => (((((2 : ℝ) / 3) ^ (k + 1)) /. (k + 1)) /. ((((2 : ℝ) / 3) ^ k) /. k))) atTop (𝓝 ((2 : ℝ) / 3)))
  (h11 : x = -(4 : ℝ) / 3 → ((2 : ℝ) / 3) < 1)
  (h12 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → ∃ L : ℝ, Tendsto (fun k : ℕ => (((((2 : ℝ) / 3) ^ (k + 1)) /. (k + 1)) /. ((((2 : ℝ) / 3) ^ k) /. k))) atTop (𝓝 L) ∧ L < 1)
  (h13 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → Summable (fun k : ℕ => if 1 ≤ k then (((2 : ℝ) / 3) ^ k) /. k else 0))
  (h14 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → lpConditionalConvergent (fun k : ℕ => if 1 ≤ k then (((3 : ℝ) ^ k + (-2 : ℝ) ^ k) /. k) * (x + 1) ^ k else 0))
  (h15 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(2 : ℝ) / 3 → (∑' k, if 1 ≤ k then (((3 : ℝ) ^ k + (-2 : ℝ) ^ k) /. k) * (x + 1) ^ k else 0) = (∑' k, if 1 ≤ k then (1 : ℝ) /. k else 0) + (∑' k, if 1 ≤ k then ((-((2 : ℝ) / 3)) ^ k) /. k else 0))
  : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(2 : ℝ) / 3 → lpDivergentSeries (fun k : ℕ => if 1 ≤ k then (1 : ℝ) /. k else 0) := by
  sorry

-- Exercise 2813, gap 15
theorem proof_gap_exercise_2813_15
  (x : ℝ)
  (a : ℕ → ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ posNatSet → a n = ((3 : ℝ) ^ n + (-2 : ℝ) ^ n) /. n)
  (h3 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => |((a k) /. (a (k + 1)))|) atTop (𝓝 ((1 : ℝ) / 3)))
  (h4 : (lpRadiusOfConvergence a) = ((1 : ENNReal) / 3))
  (h5 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ (-1 - (1 : ℝ) / 3 < x) ∧ (x < -1 + (1 : ℝ) / 3) → Summable (fun k : ℕ => if 1 ≤ k then a k * (x + 1) ^ k else 0))
  (h6 : Set.Ioo (-1 - (1 : ℝ) / 3) (-1 + (1 : ℝ) / 3) = Set.Ioo (-(4 : ℝ) / 3) (-(2 : ℝ) / 3))
  (h7 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → (∑' k, if 1 ≤ k then (((3 : ℝ) ^ k + (-2 : ℝ) ^ k) /. k) * (x + 1) ^ k else 0) = (∑' k, if 1 ≤ k then (((-1 : ℝ) ^ k + ((2 : ℝ) / 3) ^ k) /. k) else 0))
  (h8 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → (∑' k, if 1 ≤ k then (((-1 : ℝ) ^ k + ((2 : ℝ) / 3) ^ k) /. k) else 0) = (∑' k, if 1 ≤ k then ((-1 : ℝ) ^ k) /. k else 0) + (∑' k, if 1 ≤ k then (((2 : ℝ) / 3) ^ k) /. k else 0))
  (h9 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → lpConditionalConvergent (fun k : ℕ => if 1 ≤ k then ((-1 : ℝ) ^ k) /. k else 0))
  (h10 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → Tendsto (fun k : ℕ => (((((2 : ℝ) / 3) ^ (k + 1)) /. (k + 1)) /. ((((2 : ℝ) / 3) ^ k) /. k))) atTop (𝓝 ((2 : ℝ) / 3)))
  (h11 : x = -(4 : ℝ) / 3 → ((2 : ℝ) / 3) < 1)
  (h12 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → ∃ L : ℝ, Tendsto (fun k : ℕ => (((((2 : ℝ) / 3) ^ (k + 1)) /. (k + 1)) /. ((((2 : ℝ) / 3) ^ k) /. k))) atTop (𝓝 L) ∧ L < 1)
  (h13 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → Summable (fun k : ℕ => if 1 ≤ k then (((2 : ℝ) / 3) ^ k) /. k else 0))
  (h14 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → lpConditionalConvergent (fun k : ℕ => if 1 ≤ k then (((3 : ℝ) ^ k + (-2 : ℝ) ^ k) /. k) * (x + 1) ^ k else 0))
  (h15 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(2 : ℝ) / 3 → (∑' k, if 1 ≤ k then (((3 : ℝ) ^ k + (-2 : ℝ) ^ k) /. k) * (x + 1) ^ k else 0) = (∑' k, if 1 ≤ k then (1 : ℝ) /. k else 0) + (∑' k, if 1 ≤ k then ((-((2 : ℝ) / 3)) ^ k) /. k else 0))
  (h16 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(2 : ℝ) / 3 → lpDivergentSeries (fun k : ℕ => if 1 ≤ k then (1 : ℝ) /. k else 0))
  : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(2 : ℝ) / 3 → Summable (fun k : ℕ => if 1 ≤ k then ((-((2 : ℝ) / 3)) ^ k) /. k else 0) := by
  sorry

-- Exercise 2813, gap 16
theorem proof_gap_exercise_2813_16
  (x : ℝ)
  (a : ℕ → ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ posNatSet → a n = ((3 : ℝ) ^ n + (-2 : ℝ) ^ n) /. n)
  (h3 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => |((a k) /. (a (k + 1)))|) atTop (𝓝 ((1 : ℝ) / 3)))
  (h4 : (lpRadiusOfConvergence a) = ((1 : ENNReal) / 3))
  (h5 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ (-1 - (1 : ℝ) / 3 < x) ∧ (x < -1 + (1 : ℝ) / 3) → Summable (fun k : ℕ => if 1 ≤ k then a k * (x + 1) ^ k else 0))
  (h6 : Set.Ioo (-1 - (1 : ℝ) / 3) (-1 + (1 : ℝ) / 3) = Set.Ioo (-(4 : ℝ) / 3) (-(2 : ℝ) / 3))
  (h7 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → (∑' k, if 1 ≤ k then (((3 : ℝ) ^ k + (-2 : ℝ) ^ k) /. k) * (x + 1) ^ k else 0) = (∑' k, if 1 ≤ k then (((-1 : ℝ) ^ k + ((2 : ℝ) / 3) ^ k) /. k) else 0))
  (h8 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → (∑' k, if 1 ≤ k then (((-1 : ℝ) ^ k + ((2 : ℝ) / 3) ^ k) /. k) else 0) = (∑' k, if 1 ≤ k then ((-1 : ℝ) ^ k) /. k else 0) + (∑' k, if 1 ≤ k then (((2 : ℝ) / 3) ^ k) /. k else 0))
  (h9 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → lpConditionalConvergent (fun k : ℕ => if 1 ≤ k then ((-1 : ℝ) ^ k) /. k else 0))
  (h10 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → Tendsto (fun k : ℕ => (((((2 : ℝ) / 3) ^ (k + 1)) /. (k + 1)) /. ((((2 : ℝ) / 3) ^ k) /. k))) atTop (𝓝 ((2 : ℝ) / 3)))
  (h11 : x = -(4 : ℝ) / 3 → ((2 : ℝ) / 3) < 1)
  (h12 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → ∃ L : ℝ, Tendsto (fun k : ℕ => (((((2 : ℝ) / 3) ^ (k + 1)) /. (k + 1)) /. ((((2 : ℝ) / 3) ^ k) /. k))) atTop (𝓝 L) ∧ L < 1)
  (h13 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → Summable (fun k : ℕ => if 1 ≤ k then (((2 : ℝ) / 3) ^ k) /. k else 0))
  (h14 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → lpConditionalConvergent (fun k : ℕ => if 1 ≤ k then (((3 : ℝ) ^ k + (-2 : ℝ) ^ k) /. k) * (x + 1) ^ k else 0))
  (h15 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(2 : ℝ) / 3 → (∑' k, if 1 ≤ k then (((3 : ℝ) ^ k + (-2 : ℝ) ^ k) /. k) * (x + 1) ^ k else 0) = (∑' k, if 1 ≤ k then (1 : ℝ) /. k else 0) + (∑' k, if 1 ≤ k then ((-((2 : ℝ) / 3)) ^ k) /. k else 0))
  (h16 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(2 : ℝ) / 3 → lpDivergentSeries (fun k : ℕ => if 1 ≤ k then (1 : ℝ) /. k else 0))
  (h17 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(2 : ℝ) / 3 → Summable (fun k : ℕ => if 1 ≤ k then ((-((2 : ℝ) / 3)) ^ k) /. k else 0))
  : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(2 : ℝ) / 3 → lpDivergentSeries (fun k : ℕ => if 1 ≤ k then (((3 : ℝ) ^ k + (-2 : ℝ) ^ k) /. k) * (x + 1) ^ k else 0) := by
  sorry

-- Exercise 2813, gap 17
theorem proof_gap_exercise_2813_17
  (x : ℝ)
  (a : ℕ → ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ posNatSet → a n = ((3 : ℝ) ^ n + (-2 : ℝ) ^ n) /. n)
  (h3 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => |((a k) /. (a (k + 1)))|) atTop (𝓝 ((1 : ℝ) / 3)))
  (h4 : (lpRadiusOfConvergence a) = ((1 : ENNReal) / 3))
  (h5 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ (-1 - (1 : ℝ) / 3 < x) ∧ (x < -1 + (1 : ℝ) / 3) → Summable (fun k : ℕ => if 1 ≤ k then a k * (x + 1) ^ k else 0))
  (h6 : Set.Ioo (-1 - (1 : ℝ) / 3) (-1 + (1 : ℝ) / 3) = Set.Ioo (-(4 : ℝ) / 3) (-(2 : ℝ) / 3))
  (h7 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → (∑' k, if 1 ≤ k then (((3 : ℝ) ^ k + (-2 : ℝ) ^ k) /. k) * (x + 1) ^ k else 0) = (∑' k, if 1 ≤ k then (((-1 : ℝ) ^ k + ((2 : ℝ) / 3) ^ k) /. k) else 0))
  (h8 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → (∑' k, if 1 ≤ k then (((-1 : ℝ) ^ k + ((2 : ℝ) / 3) ^ k) /. k) else 0) = (∑' k, if 1 ≤ k then ((-1 : ℝ) ^ k) /. k else 0) + (∑' k, if 1 ≤ k then (((2 : ℝ) / 3) ^ k) /. k else 0))
  (h9 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → lpConditionalConvergent (fun k : ℕ => if 1 ≤ k then ((-1 : ℝ) ^ k) /. k else 0))
  (h10 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → Tendsto (fun k : ℕ => (((((2 : ℝ) / 3) ^ (k + 1)) /. (k + 1)) /. ((((2 : ℝ) / 3) ^ k) /. k))) atTop (𝓝 ((2 : ℝ) / 3)))
  (h11 : x = -(4 : ℝ) / 3 → ((2 : ℝ) / 3) < 1)
  (h12 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → ∃ L : ℝ, Tendsto (fun k : ℕ => (((((2 : ℝ) / 3) ^ (k + 1)) /. (k + 1)) /. ((((2 : ℝ) / 3) ^ k) /. k))) atTop (𝓝 L) ∧ L < 1)
  (h13 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → Summable (fun k : ℕ => if 1 ≤ k then (((2 : ℝ) / 3) ^ k) /. k else 0))
  (h14 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(4 : ℝ) / 3 → lpConditionalConvergent (fun k : ℕ => if 1 ≤ k then (((3 : ℝ) ^ k + (-2 : ℝ) ^ k) /. k) * (x + 1) ^ k else 0))
  (h15 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(2 : ℝ) / 3 → (∑' k, if 1 ≤ k then (((3 : ℝ) ^ k + (-2 : ℝ) ^ k) /. k) * (x + 1) ^ k else 0) = (∑' k, if 1 ≤ k then (1 : ℝ) /. k else 0) + (∑' k, if 1 ≤ k then ((-((2 : ℝ) / 3)) ^ k) /. k else 0))
  (h16 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(2 : ℝ) / 3 → lpDivergentSeries (fun k : ℕ => if 1 ≤ k then (1 : ℝ) /. k else 0))
  (h17 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(2 : ℝ) / 3 → Summable (fun k : ℕ => if 1 ≤ k then ((-((2 : ℝ) / 3)) ^ k) /. k else 0))
  (h18 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x = -(2 : ℝ) / 3 → lpDivergentSeries (fun k : ℕ => if 1 ≤ k then (((3 : ℝ) ^ k + (-2 : ℝ) ^ k) /. k) * (x + 1) ^ k else 0))
  : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → (x ∈ Set.Ico (-(4 : ℝ) / 3) (-(2 : ℝ) / 3) ↔ Summable (fun k : ℕ => if 1 ≤ k then (((3 : ℝ) ^ k + (-2 : ℝ) ^ k) /. k) * (x + 1) ^ k else 0)) := by
  sorry


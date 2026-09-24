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

-- exercise: exercise_2817

-- Exercise 2817, gap 1
theorem proof_gap_exercise_2817_1
  (x a : ℝ)
  (b : ℕ → ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : a > 1)
  (h4 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ posNatSet → b n = (Nat.factorial n : ℝ) /. (a ^ (n ^ 2)))
  : Tendsto (fun k : ℕ => |((b k) /. (b (k + 1)))|) atTop (𝓝 (limUnder atTop (fun k : ℕ => (a ^ (2 * k + 1)) /. (k + 1)))) := by
  sorry

-- Exercise 2817, gap 2
theorem proof_gap_exercise_2817_2
  (x a : ℝ)
  (b : ℕ → ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : a > 1)
  (h4 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ posNatSet → b n = (Nat.factorial n : ℝ) /. (a ^ (n ^ 2)))
  (h10 : Tendsto (fun k : ℕ => |((b k) /. (b (k + 1)))|) atTop (𝓝 (limUnder atTop (fun k : ℕ => (a ^ (2 * k + 1)) /. (k + 1)))))
  : Tendsto (fun k : ℕ => (a ^ (2 * k + 1)) /. (k + 1)) atTop atTop := by
  sorry

-- Exercise 2817, gap 3
theorem proof_gap_exercise_2817_3
  (x a : ℝ)
  (b : ℕ → ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : a > 1)
  (h4 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ posNatSet → b n = (Nat.factorial n : ℝ) /. (a ^ (n ^ 2)))
  (h10 : Tendsto (fun k : ℕ => |((b k) /. (b (k + 1)))|) atTop (𝓝 (limUnder atTop (fun k : ℕ => (a ^ (2 * k + 1)) /. (k + 1)))))
  (h11 : Tendsto (fun k : ℕ => (a ^ (2 * k + 1)) /. (k + 1)) atTop atTop)
  : Tendsto (fun k : ℕ => |((b k) /. (b (k + 1)))|) atTop atTop := by
  sorry

-- Exercise 2817, gap 4
theorem proof_gap_exercise_2817_4
  (x a : ℝ)
  (b : ℕ → ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : a > 1)
  (h4 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ posNatSet → b n = (Nat.factorial n : ℝ) /. (a ^ (n ^ 2)))
  (h10 : Tendsto (fun k : ℕ => |((b k) /. (b (k + 1)))|) atTop (𝓝 (limUnder atTop (fun k : ℕ => (a ^ (2 * k + 1)) /. (k + 1)))))
  (h11 : Tendsto (fun k : ℕ => (a ^ (2 * k + 1)) /. (k + 1)) atTop atTop)
  (h12 : Tendsto (fun k : ℕ => |((b k) /. (b (k + 1)))|) atTop atTop)
  : (lpRadiusOfConvergence b) = ⊤ := by
  sorry

-- Exercise 2817, gap 5
theorem proof_gap_exercise_2817_5
  (x a : ℝ)
  (b : ℕ → ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : a > 1)
  (h4 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ posNatSet → b n = (Nat.factorial n : ℝ) /. (a ^ (n ^ 2)))
  (h10 : Tendsto (fun k : ℕ => |((b k) /. (b (k + 1)))|) atTop (𝓝 (limUnder atTop (fun k : ℕ => (a ^ (2 * k + 1)) /. (k + 1)))))
  (h11 : Tendsto (fun k : ℕ => (a ^ (2 * k + 1)) /. (k + 1)) atTop atTop)
  (h12 : Tendsto (fun k : ℕ => |((b k) /. (b (k + 1)))|) atTop atTop)
  (h13 : (lpRadiusOfConvergence b) = ⊤)
  : ∀ x_1 : ℝ, x_1 ∈ (Set.univ : Set ℝ) → Summable (fun k : ℕ => if 1 ≤ k then b k * x_1 ^ k else 0) := by
  sorry

-- Exercise 2817, gap 6
theorem proof_gap_exercise_2817_6
  (x a : ℝ)
  (b : ℕ → ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : a > 1)
  (h4 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ posNatSet → b n = (Nat.factorial n : ℝ) /. (a ^ (n ^ 2)))
  (h10 : Tendsto (fun k : ℕ => |((b k) /. (b (k + 1)))|) atTop (𝓝 (limUnder atTop (fun k : ℕ => (a ^ (2 * k + 1)) /. (k + 1)))))
  (h11 : Tendsto (fun k : ℕ => (a ^ (2 * k + 1)) /. (k + 1)) atTop atTop)
  (h12 : Tendsto (fun k : ℕ => |((b k) /. (b (k + 1)))|) atTop atTop)
  (h13 : (lpRadiusOfConvergence b) = ⊤)
  (h14 : ∀ x_1 : ℝ, x_1 ∈ (Set.univ : Set ℝ) → Summable (fun k : ℕ => if 1 ≤ k then b k * x_1 ^ k else 0))
  : x ∈ (Set.univ : Set ℝ) ↔ Summable (fun k : ℕ => if 1 ≤ k then b k * x ^ k else 0) := by
  sorry


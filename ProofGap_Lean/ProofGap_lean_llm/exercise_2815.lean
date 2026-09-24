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

-- exercise: exercise_2815

-- Exercise 2815, gap 1
theorem proof_gap_exercise_2815_1
  (x a : ℝ)
  (b : ℕ → ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : 0 < a)
  (h4 : a < 1)
  (h5 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ posNatSet → b n = a ^ (n ^ 2))
  : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => |((b k) /. (b (k + 1)))|) atTop (𝓝 (limUnder atTop (fun k : ℕ => (1 : ℝ) /. (a ^ (2 * k + 1))))) := by
  sorry

-- Exercise 2815, gap 2
theorem proof_gap_exercise_2815_2
  (x a : ℝ)
  (b : ℕ → ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : 0 < a)
  (h4 : a < 1)
  (h5 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ posNatSet → b n = a ^ (n ^ 2))
  (h10 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => |((b k) /. (b (k + 1)))|) atTop (𝓝 (limUnder atTop (fun k : ℕ => (1 : ℝ) /. (a ^ (2 * k + 1))))))
  : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => (1 : ℝ) /. (a ^ (2 * k + 1))) atTop atTop := by
  sorry

-- Exercise 2815, gap 3
theorem proof_gap_exercise_2815_3
  (x a : ℝ)
  (b : ℕ → ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : 0 < a)
  (h4 : a < 1)
  (h5 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ posNatSet → b n = a ^ (n ^ 2))
  (h10 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => |((b k) /. (b (k + 1)))|) atTop (𝓝 (limUnder atTop (fun k : ℕ => (1 : ℝ) /. (a ^ (2 * k + 1))))))
  (h11 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => (1 : ℝ) /. (a ^ (2 * k + 1))) atTop atTop)
  : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => |((b k) /. (b (k + 1)))|) atTop atTop := by
  sorry

-- Exercise 2815, gap 4
theorem proof_gap_exercise_2815_4
  (x a : ℝ)
  (b : ℕ → ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : 0 < a)
  (h4 : a < 1)
  (h5 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ posNatSet → b n = a ^ (n ^ 2))
  (h10 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => |((b k) /. (b (k + 1)))|) atTop (𝓝 (limUnder atTop (fun k : ℕ => (1 : ℝ) /. (a ^ (2 * k + 1))))))
  (h11 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => (1 : ℝ) /. (a ^ (2 * k + 1))) atTop atTop)
  (h12 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => |((b k) /. (b (k + 1)))|) atTop atTop)
  : (lpRadiusOfConvergence b) = ⊤ := by
  sorry

-- Exercise 2815, gap 5
theorem proof_gap_exercise_2815_5
  (x a : ℝ)
  (b : ℕ → ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : 0 < a)
  (h4 : a < 1)
  (h5 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ posNatSet → b n = a ^ (n ^ 2))
  (h10 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => |((b k) /. (b (k + 1)))|) atTop (𝓝 (limUnder atTop (fun k : ℕ => (1 : ℝ) /. (a ^ (2 * k + 1))))))
  (h11 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => (1 : ℝ) /. (a ^ (2 * k + 1))) atTop atTop)
  (h12 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => |((b k) /. (b (k + 1)))|) atTop atTop)
  (h13 : (lpRadiusOfConvergence b) = ⊤)
  : ∀ (n : ℕ) (x_1 : ℝ), n ∈ (Set.univ : Set ℕ) ∧ x_1 ∈ (Set.univ : Set ℝ) → Summable (fun k : ℕ => if 1 ≤ k then a ^ (k ^ 2) * x_1 ^ k else 0) := by
  sorry

-- Exercise 2815, gap 6
theorem proof_gap_exercise_2815_6
  (x a : ℝ)
  (b : ℕ → ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : 0 < a)
  (h4 : a < 1)
  (h5 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ posNatSet → b n = a ^ (n ^ 2))
  (h10 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => |((b k) /. (b (k + 1)))|) atTop (𝓝 (limUnder atTop (fun k : ℕ => (1 : ℝ) /. (a ^ (2 * k + 1))))))
  (h11 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => (1 : ℝ) /. (a ^ (2 * k + 1))) atTop atTop)
  (h12 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => |((b k) /. (b (k + 1)))|) atTop atTop)
  (h13 : (lpRadiusOfConvergence b) = ⊤)
  (h14 : ∀ (n : ℕ) (x_1 : ℝ), n ∈ (Set.univ : Set ℕ) ∧ x_1 ∈ (Set.univ : Set ℝ) → Summable (fun k : ℕ => if 1 ≤ k then a ^ (k ^ 2) * x_1 ^ k else 0))
  : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → (x ∈ (Set.univ : Set ℝ) ↔ Summable (fun k : ℕ => if 1 ≤ k then a ^ (k ^ 2) * x ^ k else 0)) := by
  sorry

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

-- exercise: exercise_2816

-- Exercise 2816, gap 1
theorem proof_gap_exercise_2816_1
  (x : ℝ)
  (a : ℕ → ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ posNatSet → a n = (1 + (1 : ℝ) /. n) ^ (n ^ 2))
  : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => |((a k) /. (a (k + 1)))|) atTop (𝓝 (limUnder atTop (fun k : ℕ => ((((1 + (1 : ℝ) /. k) ^ k) /. ((1 + (1 : ℝ) /. (k + 1)) ^ (k + 1))) ^ k) * ((1 : ℝ) /. ((1 + (1 : ℝ) /. (k + 1)) ^ (k + 1)))))) := by
  sorry

-- Exercise 2816, gap 2
theorem proof_gap_exercise_2816_2
  (x : ℝ)
  (a : ℕ → ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ posNatSet → a n = (1 + (1 : ℝ) /. n) ^ (n ^ 2))
  (h10 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => |((a k) /. (a (k + 1)))|) atTop (𝓝 (limUnder atTop (fun k : ℕ => ((((1 + (1 : ℝ) /. k) ^ k) /. ((1 + (1 : ℝ) /. (k + 1)) ^ (k + 1))) ^ k) * ((1 : ℝ) /. ((1 + (1 : ℝ) /. (k + 1)) ^ (k + 1)))))))
  : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => ((((1 + (1 : ℝ) /. k) ^ k) /. ((1 + (1 : ℝ) /. (k + 1)) ^ (k + 1))) ^ k) * ((1 : ℝ) /. ((1 + (1 : ℝ) /. (k + 1)) ^ (k + 1)))) atTop (𝓝 ((1 : ℝ) / Real.exp 1)) := by
  sorry

-- Exercise 2816, gap 3
theorem proof_gap_exercise_2816_3
  (x : ℝ)
  (a : ℕ → ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ posNatSet → a n = (1 + (1 : ℝ) /. n) ^ (n ^ 2))
  (h10 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => |((a k) /. (a (k + 1)))|) atTop (𝓝 (limUnder atTop (fun k : ℕ => ((((1 + (1 : ℝ) /. k) ^ k) /. ((1 + (1 : ℝ) /. (k + 1)) ^ (k + 1))) ^ k) * ((1 : ℝ) /. ((1 + (1 : ℝ) /. (k + 1)) ^ (k + 1)))))))
  (h11 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => ((((1 + (1 : ℝ) /. k) ^ k) /. ((1 + (1 : ℝ) /. (k + 1)) ^ (k + 1))) ^ k) * ((1 : ℝ) /. ((1 + (1 : ℝ) /. (k + 1)) ^ (k + 1)))) atTop (𝓝 ((1 : ℝ) / Real.exp 1)))
  : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => |((a k) /. (a (k + 1)))|) atTop (𝓝 ((1 : ℝ) / Real.exp 1)) := by
  sorry

-- Exercise 2816, gap 4
theorem proof_gap_exercise_2816_4
  (x : ℝ)
  (a : ℕ → ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ posNatSet → a n = (1 + (1 : ℝ) /. n) ^ (n ^ 2))
  (h10 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => |((a k) /. (a (k + 1)))|) atTop (𝓝 (limUnder atTop (fun k : ℕ => ((((1 + (1 : ℝ) /. k) ^ k) /. ((1 + (1 : ℝ) /. (k + 1)) ^ (k + 1))) ^ k) * ((1 : ℝ) /. ((1 + (1 : ℝ) /. (k + 1)) ^ (k + 1)))))))
  (h11 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => ((((1 + (1 : ℝ) /. k) ^ k) /. ((1 + (1 : ℝ) /. (k + 1)) ^ (k + 1))) ^ k) * ((1 : ℝ) /. ((1 + (1 : ℝ) /. (k + 1)) ^ (k + 1)))) atTop (𝓝 ((1 : ℝ) / Real.exp 1)))
  (h12 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => |((a k) /. (a (k + 1)))|) atTop (𝓝 ((1 : ℝ) / Real.exp 1)))
  : (lpRadiusOfConvergence a) = ENNReal.ofReal ((1 : ℝ) / Real.exp 1) := by
  sorry

-- Exercise 2816, gap 5
theorem proof_gap_exercise_2816_5
  (x : ℝ)
  (a : ℕ → ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ posNatSet → a n = (1 + (1 : ℝ) /. n) ^ (n ^ 2))
  (h10 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => |((a k) /. (a (k + 1)))|) atTop (𝓝 (limUnder atTop (fun k : ℕ => ((((1 + (1 : ℝ) /. k) ^ k) /. ((1 + (1 : ℝ) /. (k + 1)) ^ (k + 1))) ^ k) * ((1 : ℝ) /. ((1 + (1 : ℝ) /. (k + 1)) ^ (k + 1)))))))
  (h11 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => ((((1 + (1 : ℝ) /. k) ^ k) /. ((1 + (1 : ℝ) /. (k + 1)) ^ (k + 1))) ^ k) * ((1 : ℝ) /. ((1 + (1 : ℝ) /. (k + 1)) ^ (k + 1)))) atTop (𝓝 ((1 : ℝ) / Real.exp 1)))
  (h12 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => |((a k) /. (a (k + 1)))|) atTop (𝓝 ((1 : ℝ) / Real.exp 1)))
  (h13 : (lpRadiusOfConvergence a) = ENNReal.ofReal ((1 : ℝ) / Real.exp 1))
  : ∀ (n : ℕ) (x_1 : ℝ), n ∈ (Set.univ : Set ℕ) ∧ x_1 ∈ (Set.univ : Set ℝ) ∧ |x_1| < (1 : ℝ) / Real.exp 1 → Summable (fun k : ℕ => if 1 ≤ k then a k * x_1 ^ k else 0) := by
  sorry

-- Exercise 2816, gap 6
theorem proof_gap_exercise_2816_6
  (x : ℝ)
  (a : ℕ → ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ posNatSet → a n = (1 + (1 : ℝ) /. n) ^ (n ^ 2))
  (h10 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => |((a k) /. (a (k + 1)))|) atTop (𝓝 (limUnder atTop (fun k : ℕ => ((((1 + (1 : ℝ) /. k) ^ k) /. ((1 + (1 : ℝ) /. (k + 1)) ^ (k + 1))) ^ k) * ((1 : ℝ) /. ((1 + (1 : ℝ) /. (k + 1)) ^ (k + 1)))))))
  (h11 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => ((((1 + (1 : ℝ) /. k) ^ k) /. ((1 + (1 : ℝ) /. (k + 1)) ^ (k + 1))) ^ k) * ((1 : ℝ) /. ((1 + (1 : ℝ) /. (k + 1)) ^ (k + 1)))) atTop (𝓝 ((1 : ℝ) / Real.exp 1)))
  (h12 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => |((a k) /. (a (k + 1)))|) atTop (𝓝 ((1 : ℝ) / Real.exp 1)))
  (h13 : (lpRadiusOfConvergence a) = ENNReal.ofReal ((1 : ℝ) / Real.exp 1))
  (h14 : ∀ (n : ℕ) (x_1 : ℝ), n ∈ (Set.univ : Set ℕ) ∧ x_1 ∈ (Set.univ : Set ℝ) ∧ |x_1| < (1 : ℝ) / Real.exp 1 → Summable (fun k : ℕ => if 1 ≤ k then a k * x_1 ^ k else 0))
  : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ |x| = (1 : ℝ) / Real.exp 1 → Tendsto (fun k : ℕ => |(a k * ((1 : ℝ) / Real.exp 1) ^ k * (-1 : ℝ) ^ k)|) atTop (𝓝 1) := by
  sorry

-- Exercise 2816, gap 7
theorem proof_gap_exercise_2816_7
  (x : ℝ)
  (a : ℕ → ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ posNatSet → a n = (1 + (1 : ℝ) /. n) ^ (n ^ 2))
  (h10 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => |((a k) /. (a (k + 1)))|) atTop (𝓝 (limUnder atTop (fun k : ℕ => ((((1 + (1 : ℝ) /. k) ^ k) /. ((1 + (1 : ℝ) /. (k + 1)) ^ (k + 1))) ^ k) * ((1 : ℝ) /. ((1 + (1 : ℝ) /. (k + 1)) ^ (k + 1)))))))
  (h11 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => ((((1 + (1 : ℝ) /. k) ^ k) /. ((1 + (1 : ℝ) /. (k + 1)) ^ (k + 1))) ^ k) * ((1 : ℝ) /. ((1 + (1 : ℝ) /. (k + 1)) ^ (k + 1)))) atTop (𝓝 ((1 : ℝ) / Real.exp 1)))
  (h12 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => |((a k) /. (a (k + 1)))|) atTop (𝓝 ((1 : ℝ) / Real.exp 1)))
  (h13 : (lpRadiusOfConvergence a) = ENNReal.ofReal ((1 : ℝ) / Real.exp 1))
  (h14 : ∀ (n : ℕ) (x_1 : ℝ), n ∈ (Set.univ : Set ℕ) ∧ x_1 ∈ (Set.univ : Set ℝ) ∧ |x_1| < (1 : ℝ) / Real.exp 1 → Summable (fun k : ℕ => if 1 ≤ k then a k * x_1 ^ k else 0))
  (h15 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ |x| = (1 : ℝ) / Real.exp 1 → Tendsto (fun k : ℕ => |(a k * ((1 : ℝ) / Real.exp 1) ^ k * (-1 : ℝ) ^ k)|) atTop (𝓝 1))
  : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ |x| = (1 : ℝ) / Real.exp 1 → ¬ Tendsto (fun k : ℕ => a k * x ^ k) atTop (𝓝 0) := by
  sorry

-- Exercise 2816, gap 8
theorem proof_gap_exercise_2816_8
  (x : ℝ)
  (a : ℕ → ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ posNatSet → a n = (1 + (1 : ℝ) /. n) ^ (n ^ 2))
  (h10 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => |((a k) /. (a (k + 1)))|) atTop (𝓝 (limUnder atTop (fun k : ℕ => ((((1 + (1 : ℝ) /. k) ^ k) /. ((1 + (1 : ℝ) /. (k + 1)) ^ (k + 1))) ^ k) * ((1 : ℝ) /. ((1 + (1 : ℝ) /. (k + 1)) ^ (k + 1)))))))
  (h11 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => ((((1 + (1 : ℝ) /. k) ^ k) /. ((1 + (1 : ℝ) /. (k + 1)) ^ (k + 1))) ^ k) * ((1 : ℝ) /. ((1 + (1 : ℝ) /. (k + 1)) ^ (k + 1)))) atTop (𝓝 ((1 : ℝ) / Real.exp 1)))
  (h12 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => |((a k) /. (a (k + 1)))|) atTop (𝓝 ((1 : ℝ) / Real.exp 1)))
  (h13 : (lpRadiusOfConvergence a) = ENNReal.ofReal ((1 : ℝ) / Real.exp 1))
  (h14 : ∀ (n : ℕ) (x_1 : ℝ), n ∈ (Set.univ : Set ℕ) ∧ x_1 ∈ (Set.univ : Set ℝ) ∧ |x_1| < (1 : ℝ) / Real.exp 1 → Summable (fun k : ℕ => if 1 ≤ k then a k * x_1 ^ k else 0))
  (h15 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ |x| = (1 : ℝ) / Real.exp 1 → Tendsto (fun k : ℕ => |(a k * ((1 : ℝ) / Real.exp 1) ^ k * (-1 : ℝ) ^ k)|) atTop (𝓝 1))
  (h16 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ |x| = (1 : ℝ) / Real.exp 1 → ¬ Tendsto (fun k : ℕ => a k * x ^ k) atTop (𝓝 0))
  : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ |x| = (1 : ℝ) / Real.exp 1 → lpDivergentSeries (fun k : ℕ => if 1 ≤ k then a k * x ^ k else 0) := by
  sorry

-- Exercise 2816, gap 9
theorem proof_gap_exercise_2816_9
  (x : ℝ)
  (a : ℕ → ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ posNatSet → a n = (1 + (1 : ℝ) /. n) ^ (n ^ 2))
  (h10 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => |((a k) /. (a (k + 1)))|) atTop (𝓝 (limUnder atTop (fun k : ℕ => ((((1 + (1 : ℝ) /. k) ^ k) /. ((1 + (1 : ℝ) /. (k + 1)) ^ (k + 1))) ^ k) * ((1 : ℝ) /. ((1 + (1 : ℝ) /. (k + 1)) ^ (k + 1)))))))
  (h11 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => ((((1 + (1 : ℝ) /. k) ^ k) /. ((1 + (1 : ℝ) /. (k + 1)) ^ (k + 1))) ^ k) * ((1 : ℝ) /. ((1 + (1 : ℝ) /. (k + 1)) ^ (k + 1)))) atTop (𝓝 ((1 : ℝ) / Real.exp 1)))
  (h12 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → Tendsto (fun k : ℕ => |((a k) /. (a (k + 1)))|) atTop (𝓝 ((1 : ℝ) / Real.exp 1)))
  (h13 : (lpRadiusOfConvergence a) = ENNReal.ofReal ((1 : ℝ) / Real.exp 1))
  (h14 : ∀ (n : ℕ) (x_1 : ℝ), n ∈ (Set.univ : Set ℕ) ∧ x_1 ∈ (Set.univ : Set ℝ) ∧ |x_1| < (1 : ℝ) / Real.exp 1 → Summable (fun k : ℕ => if 1 ≤ k then a k * x_1 ^ k else 0))
  (h15 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ |x| = (1 : ℝ) / Real.exp 1 → Tendsto (fun k : ℕ => |(a k * ((1 : ℝ) / Real.exp 1) ^ k * (-1 : ℝ) ^ k)|) atTop (𝓝 1))
  (h16 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ |x| = (1 : ℝ) / Real.exp 1 → ¬ Tendsto (fun k : ℕ => a k * x ^ k) atTop (𝓝 0))
  (h17 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ |x| = (1 : ℝ) / Real.exp 1 → lpDivergentSeries (fun k : ℕ => if 1 ≤ k then a k * x ^ k else 0))
  : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → (x ∈ Set.Ioo (-((1 : ℝ) / Real.exp 1)) ((1 : ℝ) / Real.exp 1) ↔ Summable (fun k : ℕ => if 1 ≤ k then a k * x ^ k else 0)) := by
  sorry


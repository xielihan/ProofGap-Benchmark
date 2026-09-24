import Mathlib

set_option linter.style.longLine false
open scoped BigOperators Topology Nat
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

noncomputable def lpRadiusOfConvergence {𝕜 : Type*} [NormedField 𝕜] (a : ℕ -> 𝕜) : ENNReal :=
  ⨆ (r : NNReal), ⨆ (_h : Summable (fun n : ℕ => ‖a n‖ * (r : ℝ) ^ n)), (r : ENNReal)

-- exercise: exercise_2917
-- Exercise 2917, gap 1
theorem proof_gap_exercise_2917_1
  (c : ℕ -> ℂ) (z : ℂ)
  (h1 : z ∈ (Set.univ : Set ℂ))
  (h2 : ∀ n : ℕ, ((n ∈ (Set.univ : Set ℕ)) ∧ n > 0 ∧ n ∈ {n_1 : ℕ | 0 < n_1}) →
    c n = (((1 + Complex.I) ^ n) / (((n + 1) * (n + 2) : ℕ) : ℂ)))
  : Tendsto (fun n : ℕ => ‖c n / c (n + 1)‖) atTop (𝓝 ((1 : ℝ) / ‖(1 + Complex.I)‖)) := by
  sorry

-- Exercise 2917, gap 2
theorem proof_gap_exercise_2917_2
  (c : ℕ -> ℂ) (z : ℂ)
  (h1 : z ∈ (Set.univ : Set ℂ))
  (h2 : ∀ n : ℕ, ((n ∈ (Set.univ : Set ℕ)) ∧ n > 0 ∧ n ∈ {n_1 : ℕ | 0 < n_1}) →
    c n = (((1 + Complex.I) ^ n) / (((n + 1) * (n + 2) : ℕ) : ℂ)))
  (h3 : Tendsto (fun n : ℕ => ‖c n / c (n + 1)‖) atTop (𝓝 ((1 : ℝ) / ‖(1 + Complex.I)‖)))
  : ‖(1 + Complex.I)‖ = Real.rpow (2 : ℝ) ((2 : ℝ)⁻¹) := by
  sorry

-- Exercise 2917, gap 3
theorem proof_gap_exercise_2917_3
  (c : ℕ -> ℂ) (z : ℂ)
  (h1 : z ∈ (Set.univ : Set ℂ))
  (h2 : ∀ n : ℕ, ((n ∈ (Set.univ : Set ℕ)) ∧ n > 0 ∧ n ∈ {n_1 : ℕ | 0 < n_1}) →
    c n = (((1 + Complex.I) ^ n) / (((n + 1) * (n + 2) : ℕ) : ℂ)))
  (h3 : Tendsto (fun n : ℕ => ‖c n / c (n + 1)‖) atTop (𝓝 ((1 : ℝ) / ‖(1 + Complex.I)‖)))
  (h4 : ‖(1 + Complex.I)‖ = Real.rpow (2 : ℝ) ((2 : ℝ)⁻¹))
  : lpRadiusOfConvergence c = ENNReal.ofReal ((1 : ℝ) / Real.rpow (2 : ℝ) ((2 : ℝ)⁻¹)) := by
  sorry

-- Exercise 2917, gap 4
theorem proof_gap_exercise_2917_4
  (c : ℕ -> ℂ) (z : ℂ)
  (h1 : z ∈ (Set.univ : Set ℂ))
  (h2 : ∀ n : ℕ, ((n ∈ (Set.univ : Set ℕ)) ∧ n > 0 ∧ n ∈ {n_1 : ℕ | 0 < n_1}) →
    c n = (((1 + Complex.I) ^ n) / (((n + 1) * (n + 2) : ℕ) : ℂ)))
  (h3 : Tendsto (fun n : ℕ => ‖c n / c (n + 1)‖) atTop (𝓝 ((1 : ℝ) / ‖(1 + Complex.I)‖)))
  (h4 : ‖(1 + Complex.I)‖ = Real.rpow (2 : ℝ) ((2 : ℝ)⁻¹))
  (h5 : lpRadiusOfConvergence c = ENNReal.ofReal ((1 : ℝ) / Real.rpow (2 : ℝ) ((2 : ℝ)⁻¹)))
  : (Summable (fun n : ℕ => if (1 : ℕ) ≤ n then c n * z ^ n else 0)) ↔
    ‖z‖ < ((1 : ℝ) / Real.rpow (2 : ℝ) ((2 : ℝ)⁻¹)) := by
  sorry

-- Exercise 2917, gap 5
theorem proof_gap_exercise_2917_5
  (c : ℕ -> ℂ) (z : ℂ)
  (h1 : z ∈ (Set.univ : Set ℂ))
  (h2 : ∀ n : ℕ, ((n ∈ (Set.univ : Set ℕ)) ∧ n > 0 ∧ n ∈ {n_1 : ℕ | 0 < n_1}) →
    c n = (((1 + Complex.I) ^ n) / (((n + 1) * (n + 2) : ℕ) : ℂ)))
  (h3 : Tendsto (fun n : ℕ => ‖c n / c (n + 1)‖) atTop (𝓝 ((1 : ℝ) / ‖(1 + Complex.I)‖)))
  (h4 : ‖(1 + Complex.I)‖ = Real.rpow (2 : ℝ) ((2 : ℝ)⁻¹))
  (h5 : lpRadiusOfConvergence c = ENNReal.ofReal ((1 : ℝ) / Real.rpow (2 : ℝ) ((2 : ℝ)⁻¹)))
  (h6 : (Summable (fun n : ℕ => if (1 : ℕ) ≤ n then c n * z ^ n else 0)) ↔
    ‖z‖ < ((1 : ℝ) / Real.rpow (2 : ℝ) ((2 : ℝ)⁻¹)))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → ∀ y : ℝ,
    (z = x + y * Complex.I ∧ x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ)) →
    (‖z‖ < ((1 : ℝ) / Real.rpow (2 : ℝ) ((2 : ℝ)⁻¹)) ↔ x ^ (2 : ℕ) + y ^ (2 : ℕ) < ((1 : ℝ) / 2)) := by
  sorry

-- Exercise 2917, gap 6
theorem proof_gap_exercise_2917_6
  (c : ℕ -> ℂ) (z : ℂ) (x y : ℝ)
  (h1 : z ∈ (Set.univ : Set ℂ))
  (h2 : ∀ n : ℕ, ((n ∈ (Set.univ : Set ℕ)) ∧ n > 0 ∧ n ∈ {n_1 : ℕ | 0 < n_1}) →
    c n = (((1 + Complex.I) ^ n) / (((n + 1) * (n + 2) : ℕ) : ℂ)))
  (h3 : Tendsto (fun n : ℕ => ‖c n / c (n + 1)‖) atTop (𝓝 ((1 : ℝ) / ‖(1 + Complex.I)‖)))
  (h4 : ‖(1 + Complex.I)‖ = Real.rpow (2 : ℝ) ((2 : ℝ)⁻¹))
  (h5 : lpRadiusOfConvergence c = ENNReal.ofReal ((1 : ℝ) / Real.rpow (2 : ℝ) ((2 : ℝ)⁻¹)))
  (h6 : (Summable (fun n : ℕ => if (1 : ℕ) ≤ n then c n * z ^ n else 0)) ↔
    ‖z‖ < ((1 : ℝ) / Real.rpow (2 : ℝ) ((2 : ℝ)⁻¹)))
  (h7 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → ∀ y : ℝ,
    (z = x + y * Complex.I ∧ x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ)) →
    (‖z‖ < ((1 : ℝ) / Real.rpow (2 : ℝ) ((2 : ℝ)⁻¹)) ↔ x ^ (2 : ℕ) + y ^ (2 : ℕ) < ((1 : ℝ) / 2)))
  : ({z_1 : ℂ | z_1 ∈ (Set.univ : Set ℂ) ∧ ‖z_1‖ < ((1 : ℝ) / Real.rpow (2 : ℝ) ((2 : ℝ)⁻¹))} =
    {w : ℂ | ∃ x : ℝ, ∃ y : ℝ, w = x + y * Complex.I ∧ x ∈ (Set.univ : Set ℝ) ∧
      y ∈ (Set.univ : Set ℝ) ∧ x ^ (2 : ℕ) + y ^ (2 : ℕ) < ((1 : ℝ) / 2)}) ↔
    Summable (fun n : ℕ => if (1 : ℕ) ≤ n then c n * z ^ n else 0) := by
  sorry

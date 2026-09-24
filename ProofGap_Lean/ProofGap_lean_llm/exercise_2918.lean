import Mathlib

set_option linter.style.longLine false
open scoped BigOperators Topology Nat
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

noncomputable def lpRadiusOfConvergence {𝕜 : Type*} [NormedField 𝕜] (a : ℕ -> 𝕜) : ENNReal :=
  ⨆ (r : NNReal), ⨆ (_h : Summable (fun n : ℕ => ‖a n‖ * (r : ℝ) ^ n)), (r : ENNReal)

noncomputable def exercise2918Coeff (n : ℕ) : ℂ :=
  ↑(Nat.factorial n) / ((Finset.Icc 1 n).prod (fun k => (1 + ↑k * Complex.I)))

noncomputable def exercise2918Ratio (n : ℕ) : ℂ :=
  (1 + ↑(n + 1) * Complex.I) / ↑(n + 1)

noncomputable def exercise2918AuxSeq (n : ℕ) : ℝ :=
  Real.rpow (1 + (n + 1) ^ 2) (2⁻¹) /. (n + 1)

-- exercise: exercise_2918
-- Exercise 2918, gap 1
theorem proof_gap_exercise_2918_1
  (c : ℕ -> ℂ) (z : ℂ)
  (h1 : z ∈ (Set.univ : Set ℂ))
  (h2 : ∀ k : ℕ, (k ∈ (Set.univ : Set ℕ) ∧ k > 0) →
    ∀ n : ℕ, (n ∈ (Set.univ : Set ℕ) ∧ n > 0 ∧ n ∈ {n_1 : ℕ | 0 < n_1}) →
      c n = exercise2918Coeff n)
  : ∀ n : ℕ, (n ∈ (Set.univ : Set ℕ) ∧ n > 0 ∧ n ∈ {n_1 : ℕ | 0 < n_1}) →
    c n / c (n + 1) = exercise2918Ratio n := by
  sorry

-- Exercise 2918, gap 2
theorem proof_gap_exercise_2918_2
  (c : ℕ -> ℂ) (z : ℂ)
  (h1 : z ∈ (Set.univ : Set ℂ))
  (h2 : ∀ k : ℕ, (k ∈ (Set.univ : Set ℕ) ∧ k > 0) →
    ∀ n : ℕ, (n ∈ (Set.univ : Set ℕ) ∧ n > 0 ∧ n ∈ {n_1 : ℕ | 0 < n_1}) →
      c n = exercise2918Coeff n)
  (h3 : ∀ n : ℕ, (n ∈ (Set.univ : Set ℕ) ∧ n > 0 ∧ n ∈ {n_1 : ℕ | 0 < n_1}) →
    c n / c (n + 1) = exercise2918Ratio n)
  : Tendsto (fun n => ‖c n / c (n + 1)‖) atTop
      (𝓝 (limUnder atTop exercise2918AuxSeq)) := by
  sorry

-- Exercise 2918, gap 3
theorem proof_gap_exercise_2918_3
  (c : ℕ -> ℂ) (z : ℂ)
  (h1 : z ∈ (Set.univ : Set ℂ))
  (h2 : ∀ k : ℕ, (k ∈ (Set.univ : Set ℕ) ∧ k > 0) → ∀ n : ℕ,
    (n ∈ (Set.univ : Set ℕ) ∧ n > 0 ∧ n ∈ {n_1 : ℕ | 0 < n_1}) →
      c n = exercise2918Coeff n)
  (h3 : ∀ n : ℕ, (n ∈ (Set.univ : Set ℕ) ∧ n > 0 ∧ n ∈ {n_1 : ℕ | 0 < n_1}) →
    c n / c (n + 1) = exercise2918Ratio n)
  (h4 : Tendsto (fun n => ‖c n / c (n + 1)‖) atTop
      (𝓝 (limUnder atTop exercise2918AuxSeq)))
  : Tendsto exercise2918AuxSeq atTop (𝓝 1) := by
  sorry

-- Exercise 2918, gap 4
theorem proof_gap_exercise_2918_4
  (c : ℕ -> ℂ) (z : ℂ)
  (h1 : z ∈ (Set.univ : Set ℂ))
  (h2 : ∀ k : ℕ, (k ∈ (Set.univ : Set ℕ) ∧ k > 0) → ∀ n : ℕ,
    (n ∈ (Set.univ : Set ℕ) ∧ n > 0 ∧ n ∈ {n_1 : ℕ | 0 < n_1}) →
      c n = exercise2918Coeff n)
  (h3 : ∀ n : ℕ, (n ∈ (Set.univ : Set ℕ) ∧ n > 0 ∧ n ∈ {n_1 : ℕ | 0 < n_1}) →
    c n / c (n + 1) = exercise2918Ratio n)
  (h4 : Tendsto (fun n => ‖c n / c (n + 1)‖) atTop
      (𝓝 (limUnder atTop exercise2918AuxSeq)))
  (h5 : Tendsto exercise2918AuxSeq atTop (𝓝 1))
  : Tendsto (fun n => ‖c n / c (n + 1)‖) atTop (𝓝 1) := by
  sorry

-- Exercise 2918, gap 5
theorem proof_gap_exercise_2918_5
  (c : ℕ -> ℂ) (z : ℂ)
  (h1 : z ∈ (Set.univ : Set ℂ))
  (h2 : ∀ k : ℕ, (k ∈ (Set.univ : Set ℕ) ∧ k > 0) → ∀ n : ℕ,
    (n ∈ (Set.univ : Set ℕ) ∧ n > 0 ∧ n ∈ {n_1 : ℕ | 0 < n_1}) →
      c n = exercise2918Coeff n)
  (h3 : ∀ n : ℕ, (n ∈ (Set.univ : Set ℕ) ∧ n > 0 ∧ n ∈ {n_1 : ℕ | 0 < n_1}) →
    c n / c (n + 1) = exercise2918Ratio n)
  (h4 : Tendsto (fun n => ‖c n / c (n + 1)‖) atTop
      (𝓝 (limUnder atTop exercise2918AuxSeq)))
  (h5 : Tendsto exercise2918AuxSeq atTop (𝓝 1))
  (h6 : Tendsto (fun n => ‖c n / c (n + 1)‖) atTop (𝓝 1))
  : lpRadiusOfConvergence c = 1 := by
  sorry

-- Exercise 2918, gap 6
theorem proof_gap_exercise_2918_6
  (c : ℕ -> ℂ) (z : ℂ)
  (h1 : z ∈ (Set.univ : Set ℂ))
  (h2 : ∀ k : ℕ, (k ∈ (Set.univ : Set ℕ) ∧ k > 0) → ∀ n : ℕ,
    (n ∈ (Set.univ : Set ℕ) ∧ n > 0 ∧ n ∈ {n_1 : ℕ | 0 < n_1}) →
      c n = exercise2918Coeff n)
  (h3 : ∀ n : ℕ, (n ∈ (Set.univ : Set ℕ) ∧ n > 0 ∧ n ∈ {n_1 : ℕ | 0 < n_1}) →
    c n / c (n + 1) = exercise2918Ratio n)
  (h4 : Tendsto (fun n => ‖c n / c (n + 1)‖) atTop
      (𝓝 (limUnder atTop exercise2918AuxSeq)))
  (h5 : Tendsto exercise2918AuxSeq atTop (𝓝 1))
  (h6 : Tendsto (fun n => ‖c n / c (n + 1)‖) atTop (𝓝 1))
  (h7 : lpRadiusOfConvergence c = 1)
  : (Summable (fun n => if 1 ≤ n then c n * z ^ n else 0)) ↔ ‖z‖ < 1 := by
  sorry

-- Exercise 2918, gap 7
theorem proof_gap_exercise_2918_7
  (c : ℕ -> ℂ) (z : ℂ)
  (h1 : z ∈ (Set.univ : Set ℂ))
  (h2 : ∀ k : ℕ, (k ∈ (Set.univ : Set ℕ) ∧ k > 0) → ∀ n : ℕ,
    (n ∈ (Set.univ : Set ℕ) ∧ n > 0 ∧ n ∈ {n_1 : ℕ | 0 < n_1}) →
      c n = exercise2918Coeff n)
  (h3 : ∀ n : ℕ, (n ∈ (Set.univ : Set ℕ) ∧ n > 0 ∧ n ∈ {n_1 : ℕ | 0 < n_1}) →
    c n / c (n + 1) = exercise2918Ratio n)
  (h4 : Tendsto (fun n => ‖c n / c (n + 1)‖) atTop
      (𝓝 (limUnder atTop exercise2918AuxSeq)))
  (h5 : Tendsto exercise2918AuxSeq atTop (𝓝 1))
  (h6 : Tendsto (fun n => ‖c n / c (n + 1)‖) atTop (𝓝 1))
  (h7 : lpRadiusOfConvergence c = 1)
  (h8 : (Summable (fun n => if 1 ≤ n then c n * z ^ n else 0)) ↔ ‖z‖ < 1)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → ∀ y : ℝ,
    (z = x + y * Complex.I ∧ x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ)) →
    (‖z‖ < 1 ↔ x ^ 2 + y ^ 2 < 1) := by
  sorry

-- Exercise 2918, gap 8
theorem proof_gap_exercise_2918_8
  (c : ℕ -> ℂ) (z : ℂ)
  (h1 : z ∈ (Set.univ : Set ℂ))
  (h2 : ∀ k : ℕ, (k ∈ (Set.univ : Set ℕ) ∧ k > 0) → ∀ n : ℕ,
    (n ∈ (Set.univ : Set ℕ) ∧ n > 0 ∧ n ∈ {n_1 : ℕ | 0 < n_1}) →
      c n = exercise2918Coeff n)
  (h3 : ∀ n : ℕ, (n ∈ (Set.univ : Set ℕ) ∧ n > 0 ∧ n ∈ {n_1 : ℕ | 0 < n_1}) →
    c n / c (n + 1) = exercise2918Ratio n)
  (h4 : Tendsto (fun n => ‖c n / c (n + 1)‖) atTop
      (𝓝 (limUnder atTop exercise2918AuxSeq)))
  (h5 : Tendsto exercise2918AuxSeq atTop (𝓝 1))
  (h6 : Tendsto (fun n => ‖c n / c (n + 1)‖) atTop (𝓝 1))
  (h7 : lpRadiusOfConvergence c = 1)
  (h8 : (Summable (fun n => if 1 ≤ n then c n * z ^ n else 0)) ↔ ‖z‖ < 1)
  (h9 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → ∀ y : ℝ,
    (z = x + y * Complex.I ∧ x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ)) →
    (‖z‖ < 1 ↔ x ^ 2 + y ^ 2 < 1))
  : ({z_1 : ℂ | z_1 ∈ (Set.univ : Set ℂ) ∧ ‖z_1‖ < 1} =
    {w : ℂ | ∃ x : ℝ, ∃ y : ℝ, w = x + y * Complex.I ∧ x ∈ (Set.univ : Set ℝ) ∧
      y ∈ (Set.univ : Set ℝ) ∧ x ^ 2 + y ^ 2 < 1}) ↔
    Summable (fun n => if 1 ≤ n then c n * z ^ n else 0) := by
  sorry

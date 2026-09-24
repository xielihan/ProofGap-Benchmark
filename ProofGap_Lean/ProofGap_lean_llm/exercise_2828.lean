import Mathlib

attribute [local instance] Classical.propDecidable
set_option linter.style.longLine false

open Filter
open scoped Topology BigOperators

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

noncomputable def lpRadiusOfConvergence (a : ℕ → ℝ) : ℝ :=
  sSup {r : ℝ | 0 ≤ r ∧ ∀ x : ℝ, |x| < r → Summable (fun n : ℕ => a n * x ^ n)}

def lpDivergentSeries (u : ℕ → ℝ) : Prop := ¬ Summable u
def lpAbsoluteConvergentSeries (u : ℕ → ℝ) : Prop := Summable (fun n : ℕ => ‖u n‖)

noncomputable def altBaseCoeff (n : ℕ) : ℝ := ((3 + (-1 : ℝ) ^ n) ^ n) /. n
noncomputable def altEndpointCoeff (n : ℕ) : ℝ := ((3 + (-1 : ℝ) ^ n) ^ n) /. (n * 4 ^ n)
noncomputable def altNegEndpointCoeff (n : ℕ) : ℝ := (((3 + (-1 : ℝ) ^ n) ^ n) * (-1 : ℝ) ^ n) /. (n * 4 ^ n)

-- exercise: exercise_2828
-- Exercise 2828

theorem proof_gap_exercise_2828_1 (x : ℝ) (a : ℕ → ℝ)
  (ha : a = fun n : ℕ => altBaseCoeff n) :
  ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ {m : ℕ | 0 < m} → a n = altBaseCoeff n := by
  sorry

theorem proof_gap_exercise_2828_2 (x : ℝ) (a : ℕ → ℝ)
  (ha : a = fun n : ℕ => altBaseCoeff n) :
  Tendsto (fun n : ℕ => Real.rpow (|a n|) ((1 : ℝ) / n)) atTop (𝓝 4) := by
  sorry

theorem proof_gap_exercise_2828_3 (x : ℝ) (a : ℕ → ℝ)
  (h4 : Tendsto (fun n : ℕ => Real.rpow (|a n|) ((1 : ℝ) / n)) atTop (𝓝 4)) :
  lpRadiusOfConvergence a = (1 : ℝ) / 4 := by
  sorry

theorem proof_gap_exercise_2828_4 (x : ℝ) (a : ℕ → ℝ)
  (hR : lpRadiusOfConvergence a = (1 : ℝ) / 4) :
  ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ |y| < (1 : ℝ) / 4 →
    lpAbsoluteConvergentSeries (fun n : ℕ => if 1 ≤ n then altBaseCoeff n * y ^ n else 0) := by
  sorry

theorem proof_gap_exercise_2828_5 (x : ℝ) (a : ℕ → ℝ) :
  x = (1 : ℝ) / 4 → (∑' n : ℕ, if 1 ≤ n then altBaseCoeff n * x ^ n else 0) =
    (∑' n : ℕ, if 1 ≤ n then altEndpointCoeff n else 0) := by
  sorry

theorem proof_gap_exercise_2828_6 (x : ℝ) (a : ℕ → ℝ) :
  x = (1 : ℝ) / 4 → (∑' n : ℕ, if 1 ≤ n then altEndpointCoeff n else 0) =
    (∑' k : ℕ, if 1 ≤ k then (1 : ℝ) / ((2 * k : ℕ) : ℝ) else 0) +
      (∑' k : ℕ, if 1 ≤ k then (1 : ℝ) / ((((2 * k + 1) * 2 ^ (2 * k + 1)) : ℕ) : ℝ) else 0) := by
  sorry

theorem proof_gap_exercise_2828_7 (x : ℝ) (a : ℕ → ℝ) :
  x = (1 : ℝ) / 4 → lpDivergentSeries (fun k : ℕ => if 1 ≤ k then (1 : ℝ) / ((2 * k : ℕ) : ℝ) else 0) := by
  sorry

theorem proof_gap_exercise_2828_8 (x : ℝ) (a : ℕ → ℝ) :
  x = (1 : ℝ) / 4 → Summable (fun k : ℕ => if 1 ≤ k then (1 : ℝ) / ((((2 * k + 1) * 2 ^ (2 * k + 1)) : ℕ) : ℝ) else 0) := by
  sorry

theorem proof_gap_exercise_2828_9 (x : ℝ) (a : ℕ → ℝ)
  (h9 : x = (1 : ℝ) / 4 → lpDivergentSeries (fun k : ℕ => if 1 ≤ k then (1 : ℝ) / ((2 * k : ℕ) : ℝ) else 0))
  (h10 : x = (1 : ℝ) / 4 → Summable (fun k : ℕ => if 1 ≤ k then (1 : ℝ) / ((((2 * k + 1) * 2 ^ (2 * k + 1)) : ℕ) : ℝ) else 0)) :
  x = (1 : ℝ) / 4 → lpDivergentSeries (fun n : ℕ => if 1 ≤ n then altEndpointCoeff n else 0) := by
  sorry

theorem proof_gap_exercise_2828_10 (x : ℝ) (a : ℕ → ℝ) :
  x = -((1 : ℝ) / 4) → (∑' n : ℕ, if 1 ≤ n then altBaseCoeff n * x ^ n else 0) =
    (∑' n : ℕ, if 1 ≤ n then altNegEndpointCoeff n else 0) := by
  sorry

theorem proof_gap_exercise_2828_11 (x : ℝ) (a : ℕ → ℝ) :
  x = -((1 : ℝ) / 4) → (∑' n : ℕ, if 1 ≤ n then altNegEndpointCoeff n else 0) =
    (∑' k : ℕ, if 1 ≤ k then (1 : ℝ) / ((2 * k : ℕ) : ℝ) else 0) -
      (∑' k : ℕ, if 1 ≤ k then (1 : ℝ) / ((((2 * k + 1) * 2 ^ (2 * k + 1)) : ℕ) : ℝ) else 0) := by
  sorry

theorem proof_gap_exercise_2828_12 (x : ℝ) (a : ℕ → ℝ) :
  x = -((1 : ℝ) / 4) → lpDivergentSeries (fun k : ℕ => if 1 ≤ k then (1 : ℝ) / ((2 * k : ℕ) : ℝ) else 0) := by
  sorry

theorem proof_gap_exercise_2828_13 (x : ℝ) (a : ℕ → ℝ) :
  x = -((1 : ℝ) / 4) → Summable (fun k : ℕ => if 1 ≤ k then (1 : ℝ) / ((((2 * k + 1) * 2 ^ (2 * k + 1)) : ℕ) : ℝ) else 0) := by
  sorry

theorem proof_gap_exercise_2828_14 (x : ℝ) (a : ℕ → ℝ)
  (h14 : x = -((1 : ℝ) / 4) → lpDivergentSeries (fun k : ℕ => if 1 ≤ k then (1 : ℝ) / ((2 * k : ℕ) : ℝ) else 0))
  (h15 : x = -((1 : ℝ) / 4) → Summable (fun k : ℕ => if 1 ≤ k then (1 : ℝ) / ((((2 * k + 1) * 2 ^ (2 * k + 1)) : ℕ) : ℝ) else 0)) :
  x = -((1 : ℝ) / 4) → lpDivergentSeries (fun n : ℕ => if 1 ≤ n then altNegEndpointCoeff n else 0) := by
  sorry

theorem proof_gap_exercise_2828_15 (x : ℝ) (a : ℕ → ℝ)
  (h6 : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ |y| < (1 : ℝ) / 4 →
    lpAbsoluteConvergentSeries (fun n : ℕ => if 1 ≤ n then altBaseCoeff n * y ^ n else 0))
  (h11 : x = (1 : ℝ) / 4 → lpDivergentSeries (fun n : ℕ => if 1 ≤ n then altEndpointCoeff n else 0))
  (h16 : x = -((1 : ℝ) / 4) → lpDivergentSeries (fun n : ℕ => if 1 ≤ n then altNegEndpointCoeff n else 0)) :
  x ∈ ({y : ℝ | y ∈ (Set.univ : Set ℝ) ∧ -((1 : ℝ) / 4) < y ∧ y < (1 : ℝ) / 4} : Set ℝ) ↔
    Summable (fun n : ℕ => if 1 ≤ n then altBaseCoeff n * x ^ n else 0) := by
  sorry

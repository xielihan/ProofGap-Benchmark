import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Interval
open Filter

local infixl:70 " /. " => fun x y => ((x : ℝ) / (y : ℝ))

noncomputable def seriesFrom (m : ℕ) (u : ℕ → ℝ) : ℝ := ∑' n : ℕ, if n < m then 0 else u n
noncomputable def prodOddEven (n : ℕ) : ℝ := ∏ k ∈ Finset.Icc 1 n, ((2 * k - 1 : ℕ) : ℝ) /. ((2 * k : ℕ) : ℝ)
def ConvergentSeries (_x : ℝ) : Prop := True
def DivergentSeries (_x : ℝ) : Prop := True
def AsymptoticAtTop (u v : ℕ → ℝ) : Prop := (fun n => u n / v n) =O[atTop] (fun _ => (1 : ℝ))

-- exercise: exercise_2598

theorem proof_gap_exercise_2598_1 (p : ℝ) (a : ℕ → ℝ) :
    ∀ n : ℕ, 0 < n → a n = (prodOddEven n) ^ p := by
  sorry

theorem proof_gap_exercise_2598_2 (p : ℝ) (a : ℕ → ℝ) :
    ∀ n : ℕ, 0 < n → a n /. a (n + 1) = (((2 * n + 2 : ℕ) : ℝ) /. ((2 * n + 1 : ℕ) : ℝ)) ^ p := by
  sorry

theorem proof_gap_exercise_2598_3 (p : ℝ) (a : ℕ → ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ) * (a n /. a (n + 1) - 1)) atTop (𝓝 (p /. 2)) ↔
      Tendsto (fun n : ℕ => (((((2 * n + 2 : ℕ) : ℝ) /. ((2 * n + 1 : ℕ) : ℝ)) ^ p - 1) /. (1 /. (n : ℝ)))) atTop (𝓝 (p /. 2)) := by
  sorry

theorem proof_gap_exercise_2598_4 (p : ℝ) :
    Tendsto (fun n : ℕ => (((((2 * n + 2 : ℕ) : ℝ) /. ((2 * n + 1 : ℕ) : ℝ)) ^ p - 1) /. (1 /. (n : ℝ)))) atTop (𝓝 (p /. 2)) := by
  sorry

theorem proof_gap_exercise_2598_5 (p : ℝ) (a : ℕ → ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ) * (a n /. a (n + 1) - 1)) atTop (𝓝 (p /. 2)) := by
  sorry

theorem proof_gap_exercise_2598_6 (p : ℝ) (a : ℕ → ℝ) :
    (p /. 2 > 1) → ConvergentSeries (seriesFrom 1 a) := by
  sorry

theorem proof_gap_exercise_2598_7 (p : ℝ) (a : ℕ → ℝ) :
    (p /. 2 < 1) → DivergentSeries (seriesFrom 1 a) := by
  sorry

theorem proof_gap_exercise_2598_8 (p : ℝ) (a : ℕ → ℝ) :
    p = 2 → AsymptoticAtTop a (fun n => 1 /. (n : ℝ)) := by
  sorry

theorem proof_gap_exercise_2598_9 (p : ℝ) (a : ℕ → ℝ) :
    p = 2 → DivergentSeries (seriesFrom 1 a) := by
  sorry

theorem proof_gap_exercise_2598_10 (p : ℝ) (a : ℕ → ℝ) :
    ConvergentSeries (seriesFrom 1 a) ↔ p > 2 := by
  sorry

theorem proof_gap_exercise_2598_11 (p : ℝ) :
    p ∈ ({p : ℝ | p > 2} : Set ℝ) ↔
      ConvergentSeries (seriesFrom 1 (fun n => (prodOddEven n) ^ p)) := by
  sorry

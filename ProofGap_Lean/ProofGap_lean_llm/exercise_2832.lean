import Mathlib

attribute [local instance] Classical.propDecidable
set_option linter.style.longLine false

open Filter
open scoped Topology BigOperators

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

def ConvergentSeries (u : ℕ -> ℝ) : Prop := Summable u
def DivergentSeries (u : ℕ -> ℝ) : Prop := ¬ Summable u
def AbsoluteConvergentSeries (u : ℕ -> ℝ) : Prop := Summable (fun n => ‖u n‖)
def ConditionalConvergentSeries (u : ℕ -> ℝ) : Prop := Summable u ∧ ¬ Summable (fun n => ‖u n‖)

noncomputable def lpRadiusOfConvergence (a : ℕ -> ℝ) : ENNReal :=
  ⨆ r : NNReal, if Summable (fun n : ℕ => ‖a n‖ * (r : ℝ) ^ n) then (r : ENNReal) else 0

noncomputable def hyperCoeff (α β γ : ℝ) (n : ℕ) : ℝ :=
  ((Finset.prod (Finset.range n) (fun k : ℕ => α + (k : ℝ))) *
      (Finset.prod (Finset.range n) (fun k : ℕ => β + (k : ℝ)))) /
    ((Nat.factorial n : ℝ) * (Finset.prod (Finset.range n) (fun k : ℕ => γ + (k : ℝ))))

def hyperConvergenceSet (α β γ : ℝ) : Set ℝ :=
  if γ - α - β > 0 then Set.Icc (-1 : ℝ) 1
  else if -1 < γ - α - β ∧ γ - α - β ≤ 0 then Set.Ico (-1 : ℝ) 1
  else Set.Ioo (-1 : ℝ) 1

-- exercise: exercise_2832

theorem proof_gap_exercise_2832_1
  (α β γ : ℝ) (a : ℕ -> ℝ) (x : ℝ)
  (hγ : ∀ k : ℕ, γ + k ≠ 0)
  (ha : ∀ n : ℕ, 0 < n -> a n = hyperCoeff α β γ n)
  : Tendsto (fun n : ℕ => |(a n /. a (n + 1))|) atTop
      (𝓝 (atTop.limUnder (fun n : ℕ => ((n + 1) * (γ + n)) /. ((α + n) * (β + n))))) := by
  sorry

theorem proof_gap_exercise_2832_2
  (α β γ : ℝ) (a : ℕ -> ℝ) (x : ℝ)
  (hγ : ∀ k : ℕ, γ + k ≠ 0)
  (ha : ∀ n : ℕ, 0 < n -> a n = hyperCoeff α β γ n)
  (h1 : Tendsto (fun n : ℕ => |(a n /. a (n + 1))|) atTop
      (𝓝 (atTop.limUnder (fun n : ℕ => ((n + 1) * (γ + n)) /. ((α + n) * (β + n))))))
  : Tendsto (fun n : ℕ => ((n + 1) * (γ + n)) /. ((α + n) * (β + n))) atTop (𝓝 1) := by
  sorry

theorem proof_gap_exercise_2832_3
  (α β γ : ℝ) (a : ℕ -> ℝ) (x : ℝ)
  (hγ : ∀ k : ℕ, γ + k ≠ 0)
  (ha : ∀ n : ℕ, 0 < n -> a n = hyperCoeff α β γ n)
  (h1 : Tendsto (fun n : ℕ => |(a n /. a (n + 1))|) atTop
      (𝓝 (atTop.limUnder (fun n : ℕ => ((n + 1) * (γ + n)) /. ((α + n) * (β + n))))))
  (h2 : Tendsto (fun n : ℕ => ((n + 1) * (γ + n)) /. ((α + n) * (β + n))) atTop (𝓝 1))
  : Tendsto (fun n : ℕ => |(a n /. a (n + 1))|) atTop (𝓝 1) := by
  sorry

theorem proof_gap_exercise_2832_4
  (α β γ : ℝ) (a : ℕ -> ℝ) (x : ℝ)
  (hγ : ∀ k : ℕ, γ + k ≠ 0)
  (ha : ∀ n : ℕ, 0 < n -> a n = hyperCoeff α β γ n)
  (h3 : Tendsto (fun n : ℕ => |(a n /. a (n + 1))|) atTop (𝓝 1))
  : lpRadiusOfConvergence a = 1 := by
  sorry

theorem proof_gap_exercise_2832_5
  (α β γ : ℝ) (a : ℕ -> ℝ) (x : ℝ)
  (hγ : ∀ k : ℕ, γ + k ≠ 0)
  (ha : ∀ n : ℕ, 0 < n -> a n = hyperCoeff α β γ n)
  (hr : lpRadiusOfConvergence a = 1)
  : ∀ x : ℝ, |x| < 1 -> AbsoluteConvergentSeries (fun n : ℕ => a n * x ^ n) := by
  sorry

theorem proof_gap_exercise_2832_6
  (α β γ : ℝ) (a : ℕ -> ℝ) (x : ℝ)
  (hγ : ∀ k : ℕ, γ + k ≠ 0)
  (ha : ∀ n : ℕ, 0 < n -> a n = hyperCoeff α β γ n)
  (hr : lpRadiusOfConvergence a = 1)
  (hinside : ∀ x : ℝ, |x| < 1 -> AbsoluteConvergentSeries (fun n : ℕ => a n * x ^ n))
  : ∀ x : ℝ, |x| > 1 -> DivergentSeries (fun n : ℕ => a n * x ^ n) := by
  sorry

theorem proof_gap_exercise_2832_7
  (α β γ : ℝ) (a : ℕ -> ℝ) (x : ℝ)
  (hγ : ∀ k : ℕ, γ + k ≠ 0)
  (ha : ∀ n : ℕ, 0 < n -> a n = hyperCoeff α β γ n)
  : x = 1 -> ∃ θ : ℕ -> ℝ, ∀ n : ℕ, 0 < n ->
      (a n /. a (n - 1)) = 1 + ((γ - α - β + 1) /. n) + ((θ n) /. (n ^ 2)) := by
  sorry

theorem proof_gap_exercise_2832_8
  (α β γ : ℝ) (a : ℕ -> ℝ) (x : ℝ)
  (hγ : ∀ k : ℕ, γ + k ≠ 0)
  (ha : ∀ n : ℕ, 0 < n -> a n = hyperCoeff α β γ n)
  (h7 : x = 1 -> ∃ θ : ℕ -> ℝ, ∀ n : ℕ, 0 < n ->
      (a n /. a (n - 1)) = 1 + ((γ - α - β + 1) /. n) + ((θ n) /. (n ^ 2)))
  : x = 1 -> ∃ θ : ℕ -> ℝ, ∃ L : ℝ, L ≥ 0 ∧ ∀ n : ℕ, 0 < n -> |θ n| ≤ L := by
  sorry

theorem proof_gap_exercise_2832_9
  (α β γ : ℝ) (a : ℕ -> ℝ) (x : ℝ)
  (hγ : ∀ k : ℕ, γ + k ≠ 0)
  (ha : ∀ n : ℕ, 0 < n -> a n = hyperCoeff α β γ n)
  : x = 1 -> γ - α - β > 0 -> AbsoluteConvergentSeries a := by
  sorry

theorem proof_gap_exercise_2832_10
  (α β γ : ℝ) (a : ℕ -> ℝ) (x : ℝ)
  (hγ : ∀ k : ℕ, γ + k ≠ 0)
  (ha : ∀ n : ℕ, 0 < n -> a n = hyperCoeff α β γ n)
  (h9 : x = 1 -> γ - α - β > 0 -> AbsoluteConvergentSeries a)
  : x = 1 -> γ - α - β ≤ 0 -> DivergentSeries a := by
  sorry

theorem proof_gap_exercise_2832_11
  (α β γ : ℝ) (a : ℕ -> ℝ) (x : ℝ)
  (hγ : ∀ k : ℕ, γ + k ≠ 0)
  (ha : ∀ n : ℕ, 0 < n -> a n = hyperCoeff α β γ n)
  : x = -1 -> ∃ θ : ℕ -> ℝ, ∀ n : ℕ, 0 < n ->
      |(a n /. a (n + 1))| = 1 + ((γ - α - β + 1) /. n) + ((θ n) /. (n ^ 2)) := by
  sorry

theorem proof_gap_exercise_2832_12
  (α β γ : ℝ) (a : ℕ -> ℝ) (x : ℝ)
  (hγ : ∀ k : ℕ, γ + k ≠ 0)
  (ha : ∀ n : ℕ, 0 < n -> a n = hyperCoeff α β γ n)
  (h11 : x = -1 -> ∃ θ : ℕ -> ℝ, ∀ n : ℕ, 0 < n ->
      |(a n /. a (n + 1))| = 1 + ((γ - α - β + 1) /. n) + ((θ n) /. (n ^ 2)))
  : x = -1 -> γ - α - β > 0 -> AbsoluteConvergentSeries (fun n : ℕ => a n * (-1 : ℝ) ^ n) := by
  sorry

theorem proof_gap_exercise_2832_13
  (α β γ : ℝ) (a : ℕ -> ℝ) (x : ℝ)
  (hγ : ∀ k : ℕ, γ + k ≠ 0)
  (ha : ∀ n : ℕ, 0 < n -> a n = hyperCoeff α β γ n)
  : x = -1 -> -1 < γ - α - β -> γ - α - β ≤ 0 ->
      ConvergentSeries (fun n : ℕ => a n * (-1 : ℝ) ^ n) := by
  sorry

theorem proof_gap_exercise_2832_14
  (α β γ : ℝ) (a : ℕ -> ℝ) (x : ℝ)
  (hγ : ∀ k : ℕ, γ + k ≠ 0)
  (ha : ∀ n : ℕ, 0 < n -> a n = hyperCoeff α β γ n)
  (h13 : x = -1 -> -1 < γ - α - β -> γ - α - β ≤ 0 ->
      ConvergentSeries (fun n : ℕ => a n * (-1 : ℝ) ^ n))
  : x = -1 -> -1 < γ - α - β -> γ - α - β ≤ 0 ->
      ¬ AbsoluteConvergentSeries (fun n : ℕ => a n * (-1 : ℝ) ^ n) := by
  sorry

theorem proof_gap_exercise_2832_15
  (α β γ : ℝ) (a : ℕ -> ℝ) (x : ℝ)
  (hγ : ∀ k : ℕ, γ + k ≠ 0)
  (ha : ∀ n : ℕ, 0 < n -> a n = hyperCoeff α β γ n)
  (h13 : x = -1 -> -1 < γ - α - β -> γ - α - β ≤ 0 ->
      ConvergentSeries (fun n : ℕ => a n * (-1 : ℝ) ^ n))
  (h14 : x = -1 -> -1 < γ - α - β -> γ - α - β ≤ 0 ->
      ¬ AbsoluteConvergentSeries (fun n : ℕ => a n * (-1 : ℝ) ^ n))
  : x = -1 -> -1 < γ - α - β -> γ - α - β ≤ 0 ->
      ConditionalConvergentSeries (fun n : ℕ => a n * (-1 : ℝ) ^ n) := by
  sorry

theorem proof_gap_exercise_2832_16
  (α β γ : ℝ) (a : ℕ -> ℝ) (x : ℝ)
  (hγ : ∀ k : ℕ, γ + k ≠ 0)
  (ha : ∀ n : ℕ, 0 < n -> a n = hyperCoeff α β γ n)
  : x = -1 -> γ - α - β ≤ -1 -> DivergentSeries (fun n : ℕ => a n * (-1 : ℝ) ^ n) := by
  sorry

theorem proof_gap_exercise_2832_17
  (α β γ : ℝ) (a : ℕ -> ℝ) (x : ℝ)
  (hγ : ∀ k : ℕ, γ + k ≠ 0)
  (ha : ∀ n : ℕ, 0 < n -> a n = hyperCoeff α β γ n)
  (hinside : ∀ x : ℝ, |x| < 1 -> AbsoluteConvergentSeries (fun n : ℕ => a n * x ^ n))
  (houtside : ∀ x : ℝ, |x| > 1 -> DivergentSeries (fun n : ℕ => a n * x ^ n))
  (honeabs : x = 1 -> γ - α - β > 0 -> AbsoluteConvergentSeries a)
  (honediv : x = 1 -> γ - α - β ≤ 0 -> DivergentSeries a)
  (hnegabs : x = -1 -> γ - α - β > 0 -> AbsoluteConvergentSeries (fun n : ℕ => a n * (-1 : ℝ) ^ n))
  (hnegcond : x = -1 -> -1 < γ - α - β -> γ - α - β ≤ 0 ->
      ConditionalConvergentSeries (fun n : ℕ => a n * (-1 : ℝ) ^ n))
  (hnegdiv : x = -1 -> γ - α - β ≤ -1 -> DivergentSeries (fun n : ℕ => a n * (-1 : ℝ) ^ n))
  : x ∈ hyperConvergenceSet α β γ ↔ ConvergentSeries (fun n : ℕ => a n * x ^ n) := by
  sorry

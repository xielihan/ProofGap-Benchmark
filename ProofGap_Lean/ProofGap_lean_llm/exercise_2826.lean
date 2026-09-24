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
def lpConditionalConvergentSeries (u : ℕ → ℝ) : Prop := Summable u ∧ ¬ lpAbsoluteConvergentSeries u

noncomputable def stirlingTerm (n : ℕ) : ℝ := (1 : ℝ) / Real.sqrt (2 * Real.pi * n)
noncomputable def expPowerCoeff (n : ℕ) : ℝ := (((-1 : ℝ) ^ n) / (n.factorial : ℝ)) * (((n : ℝ) / Real.exp 1) ^ n)
noncomputable def expPowerAbsCoeff (n : ℕ) : ℝ := ((1 : ℝ) / (n.factorial : ℝ)) * (((n : ℝ) / Real.exp 1) ^ n)

-- exercise: exercise_2826
-- Exercise 2826

theorem proof_gap_exercise_2826_1 (x : ℝ) (a : ℕ → ℝ)
  (ha : a = fun n : ℕ => expPowerCoeff n) :
  ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ {m : ℕ | 0 < m} → a n = expPowerCoeff n := by
  sorry

theorem proof_gap_exercise_2826_2 (x : ℝ) (a : ℕ → ℝ)
  (ha : a = fun n : ℕ => expPowerCoeff n)
  (h3 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ {m : ℕ | 0 < m} → a n = expPowerCoeff n) :
  Tendsto (fun n : ℕ => |(a n /. a (n + 1))|) atTop
    (𝓝 (atTop.limUnder (fun n : ℕ => (Real.exp 1) /. ((1 + (1 /. n)) ^ n)))) := by
  sorry

theorem proof_gap_exercise_2826_3 (x : ℝ) (a : ℕ → ℝ)
  (ha : a = fun n : ℕ => expPowerCoeff n)
  (h4 : Tendsto (fun n : ℕ => |(a n /. a (n + 1))|) atTop
    (𝓝 (atTop.limUnder (fun n : ℕ => (Real.exp 1) /. ((1 + (1 /. n)) ^ n))))) :
  Tendsto (fun n : ℕ => (Real.exp 1) /. ((1 + (1 /. n)) ^ n)) atTop (𝓝 1) := by
  sorry

theorem proof_gap_exercise_2826_4 (x : ℝ) (a : ℕ → ℝ)
  (h4 : Tendsto (fun n : ℕ => |(a n /. a (n + 1))|) atTop
    (𝓝 (atTop.limUnder (fun n : ℕ => (Real.exp 1) /. ((1 + (1 /. n)) ^ n)))))
  (h5 : Tendsto (fun n : ℕ => (Real.exp 1) /. ((1 + (1 /. n)) ^ n)) atTop (𝓝 1)) :
  Tendsto (fun n : ℕ => |(a n /. a (n + 1))|) atTop (𝓝 1) := by
  sorry

theorem proof_gap_exercise_2826_5 (x : ℝ) (a : ℕ → ℝ)
  (h6 : Tendsto (fun n : ℕ => |(a n /. a (n + 1))|) atTop (𝓝 1)) :
  lpRadiusOfConvergence a = 1 := by
  sorry

theorem proof_gap_exercise_2826_6 (x : ℝ) (a : ℕ → ℝ)
  (hR : lpRadiusOfConvergence a = 1) :
  ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ |y| < 1 →
    lpAbsoluteConvergentSeries (fun n : ℕ => if 1 ≤ n then expPowerCoeff n * y ^ n else 0) := by
  sorry

theorem proof_gap_exercise_2826_7 (x : ℝ) (a : ℕ → ℝ) :
  x = -1 → (∑' n : ℕ, if 1 ≤ n then expPowerCoeff n * x ^ n else 0) =
    (∑' n : ℕ, if 1 ≤ n then expPowerAbsCoeff n else 0) := by
  sorry

theorem proof_gap_exercise_2826_8 (x : ℝ) (a : ℕ → ℝ) :
  x = -1 → Asymptotics.IsEquivalent atTop expPowerAbsCoeff stirlingTerm := by
  sorry

theorem proof_gap_exercise_2826_9 (x : ℝ) (a : ℕ → ℝ)
  (h10 : x = -1 → Asymptotics.IsEquivalent atTop expPowerAbsCoeff stirlingTerm) :
  x = -1 → ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ {m : ℕ | 0 < m} →
    stirlingTerm n ≥ (1 /. (2 * Real.pi)) * (1 /. n) := by
  sorry

theorem proof_gap_exercise_2826_10 (x : ℝ) (a : ℕ → ℝ) :
  x = -1 → ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ {m : ℕ | 0 < m} →
    (1 /. (2 * Real.pi)) * (1 /. n) > 0 := by
  sorry

theorem proof_gap_exercise_2826_11 (x : ℝ) (a : ℕ → ℝ)
  (h11 : x = -1 → ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ {m : ℕ | 0 < m} →
    stirlingTerm n ≥ (1 /. (2 * Real.pi)) * (1 /. n))
  (h12 : x = -1 → ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ {m : ℕ | 0 < m} →
    (1 /. (2 * Real.pi)) * (1 /. n) > 0) :
  x = -1 → ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ {m : ℕ | 0 < m} → stirlingTerm n > 0 := by
  sorry

theorem proof_gap_exercise_2826_12 (x : ℝ) (a : ℕ → ℝ) :
  x = -1 → lpDivergentSeries (fun n : ℕ => if 1 ≤ n then 1 /. n else 0) := by
  sorry

theorem proof_gap_exercise_2826_13 (x : ℝ) (a : ℕ → ℝ)
  (h14 : x = -1 → lpDivergentSeries (fun n : ℕ => if 1 ≤ n then 1 /. n else 0)) :
  x = -1 → lpDivergentSeries (fun n : ℕ => if 1 ≤ n then expPowerAbsCoeff n else 0) := by
  sorry

theorem proof_gap_exercise_2826_14 (x : ℝ) (a : ℕ → ℝ) :
  x = 1 → (∑' n : ℕ, if 1 ≤ n then expPowerCoeff n * x ^ n else 0) =
    (∑' n : ℕ, if 1 ≤ n then (-1 : ℝ) ^ n * expPowerAbsCoeff n else 0) := by
  sorry

theorem proof_gap_exercise_2826_15 (x : ℝ) (a : ℕ → ℝ) :
  x = 1 → Asymptotics.IsEquivalent atTop expPowerAbsCoeff stirlingTerm := by
  sorry

theorem proof_gap_exercise_2826_16 (x : ℝ) (a : ℕ → ℝ)
  (h17 : x = 1 → Asymptotics.IsEquivalent atTop expPowerAbsCoeff stirlingTerm) :
  x = 1 → Tendsto expPowerAbsCoeff atTop (𝓝 0) := by
  sorry

theorem proof_gap_exercise_2826_17 (x : ℝ) (a : ℕ → ℝ)
  (ha : a = fun n : ℕ => expPowerCoeff n) :
  x = 1 → ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ {m : ℕ | 0 < m} →
    |(a n /. a (n + 1))| = ((Real.exp 1) /. ((1 + (1 /. n)) ^ n)) ∧
      ((Real.exp 1) /. ((1 + (1 /. n)) ^ n)) > 1 := by
  sorry

theorem proof_gap_exercise_2826_18 (x : ℝ) (a : ℕ → ℝ)
  (h19 : x = 1 → ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ {m : ℕ | 0 < m} →
    |(a n /. a (n + 1))| = ((Real.exp 1) /. ((1 + (1 /. n)) ^ n)) ∧
      ((Real.exp 1) /. ((1 + (1 /. n)) ^ n)) > 1) :
  x = 1 → ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ {m : ℕ | 0 < m} → |a n| > |a (n + 1)| := by
  sorry

theorem proof_gap_exercise_2826_19 (x : ℝ) (a : ℕ → ℝ)
  (h18 : x = 1 → Tendsto expPowerAbsCoeff atTop (𝓝 0))
  (h20 : x = 1 → ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ {m : ℕ | 0 < m} → |a n| > |a (n + 1)|) :
  x = 1 → Summable (fun n : ℕ => if 1 ≤ n then (-1 : ℝ) ^ n * expPowerAbsCoeff n else 0) := by
  sorry

theorem proof_gap_exercise_2826_20 (x : ℝ) (a : ℕ → ℝ)
  (h15 : x = -1 → lpDivergentSeries (fun n : ℕ => if 1 ≤ n then expPowerAbsCoeff n else 0)) :
  x = 1 → ¬ lpAbsoluteConvergentSeries (fun n : ℕ => if 1 ≤ n then (-1 : ℝ) ^ n * expPowerAbsCoeff n else 0) := by
  sorry

theorem proof_gap_exercise_2826_21 (x : ℝ) (a : ℕ → ℝ)
  (h21 : x = 1 → Summable (fun n : ℕ => if 1 ≤ n then (-1 : ℝ) ^ n * expPowerAbsCoeff n else 0))
  (h22 : x = 1 → ¬ lpAbsoluteConvergentSeries (fun n : ℕ => if 1 ≤ n then (-1 : ℝ) ^ n * expPowerAbsCoeff n else 0)) :
  x = 1 → lpConditionalConvergentSeries (fun n : ℕ => if 1 ≤ n then (-1 : ℝ) ^ n * expPowerAbsCoeff n else 0) := by
  sorry

theorem proof_gap_exercise_2826_22 (x : ℝ) (a : ℕ → ℝ)
  (h8 : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ |y| < 1 →
    lpAbsoluteConvergentSeries (fun n : ℕ => if 1 ≤ n then expPowerCoeff n * y ^ n else 0))
  (h15 : x = -1 → lpDivergentSeries (fun n : ℕ => if 1 ≤ n then expPowerAbsCoeff n else 0))
  (h23 : x = 1 → lpConditionalConvergentSeries (fun n : ℕ => if 1 ≤ n then (-1 : ℝ) ^ n * expPowerAbsCoeff n else 0)) :
  x ∈ {y : ℝ | y ∈ (Set.univ : Set ℝ) ∧ -1 < y ∧ y ≤ 1} ↔
    Summable (fun n : ℕ => if 1 ≤ n then expPowerCoeff n * x ^ n else 0) := by
  sorry

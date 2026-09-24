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

noncomputable def harmonicPrefix (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, (1 /. k)

-- exercise: exercise_2827
-- Exercise 2827

theorem proof_gap_exercise_2827_1 (x : ℝ) (a : ℕ → ℝ)
  (ha : a = fun n : ℕ => harmonicPrefix n) :
  ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ {m : ℕ | 0 < m} → a n = harmonicPrefix n := by
  sorry

theorem proof_gap_exercise_2827_2 (x : ℝ) (a : ℕ → ℝ)
  (ha : a = fun n : ℕ => harmonicPrefix n)
  (h3 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ {m : ℕ | 0 < m} → a n = harmonicPrefix n) :
  ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ {m : ℕ | 0 < m} → a (n + 1) ≠ 0 := by
  sorry

theorem proof_gap_exercise_2827_3 (x : ℝ) (a : ℕ → ℝ)
  (ha : a = fun n : ℕ => harmonicPrefix n)
  (h3 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ {m : ℕ | 0 < m} → a n = harmonicPrefix n)
  (h4 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ {m : ℕ | 0 < m} → a (n + 1) ≠ 0) :
  Tendsto (fun n : ℕ => |(a n /. a (n + 1))|) atTop (𝓝 1) := by
  sorry

theorem proof_gap_exercise_2827_4 (x : ℝ) (a : ℕ → ℝ)
  (ha : a = fun n : ℕ => harmonicPrefix n)
  (h5 : Tendsto (fun n : ℕ => |(a n /. a (n + 1))|) atTop (𝓝 1)) :
  lpRadiusOfConvergence a = 1 := by
  sorry

theorem proof_gap_exercise_2827_5 (x : ℝ) (a : ℕ → ℝ)
  (ha : a = fun n : ℕ => harmonicPrefix n)
  (h6 : lpRadiusOfConvergence a = 1) :
  ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ |y| < 1 →
    lpAbsoluteConvergentSeries (fun n : ℕ => if 1 ≤ n then harmonicPrefix n * y ^ n else 0) := by
  sorry

theorem proof_gap_exercise_2827_6 (x : ℝ) (a : ℕ → ℝ)
  (ha : a = fun n : ℕ => harmonicPrefix n) :
  |x| = 1 → Tendsto a atTop atTop := by
  sorry

theorem proof_gap_exercise_2827_7 (x : ℝ) (a : ℕ → ℝ)
  (ha : a = fun n : ℕ => harmonicPrefix n)
  (h8 : |x| = 1 → Tendsto a atTop atTop) :
  |x| = 1 → ¬ Tendsto (fun n : ℕ => a n * x ^ n) atTop (𝓝 0) := by
  sorry

theorem proof_gap_exercise_2827_8 (x : ℝ) (a : ℕ → ℝ)
  (ha : a = fun n : ℕ => harmonicPrefix n)
  (h9 : |x| = 1 → ¬ Tendsto (fun n : ℕ => a n * x ^ n) atTop (𝓝 0)) :
  |x| = 1 → lpDivergentSeries (fun n : ℕ => if 1 ≤ n then harmonicPrefix n * x ^ n else 0) := by
  sorry

theorem proof_gap_exercise_2827_9 (x : ℝ) (a : ℕ → ℝ)
  (ha : a = fun n : ℕ => harmonicPrefix n)
  (h7 : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ |y| < 1 →
    lpAbsoluteConvergentSeries (fun n : ℕ => if 1 ≤ n then harmonicPrefix n * y ^ n else 0))
  (h10 : |x| = 1 → lpDivergentSeries (fun n : ℕ => if 1 ≤ n then harmonicPrefix n * x ^ n else 0)) :
  x ∈ ({y : ℝ | y ∈ (Set.univ : Set ℝ) ∧ -1 < y ∧ y < 1} : Set ℝ) ↔
    Summable (fun n : ℕ => if 1 ≤ n then harmonicPrefix n * x ^ n else 0) := by
  sorry

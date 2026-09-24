import Mathlib

attribute [local instance] Classical.propDecidable
set_option linter.style.longLine false

open Filter
open scoped Topology

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

def ConvergentSeries (u : ℕ -> ℝ) : Prop := Summable u
def DivergentSeries (u : ℕ -> ℝ) : Prop := ¬ Summable u
def AbsoluteConvergentSeries (u : ℕ -> ℝ) : Prop := Summable (fun n => ‖u n‖)

-- exercise: exercise_2833

theorem proof_gap_exercise_2833_1
  (a : ℕ -> ℝ) (x : ℝ)
  (hx : x ≠ -1)
  (ha : ∀ n : ℕ, a n = 1 /. (2 * n + 1))
  : Tendsto (fun n : ℕ => |(a n /. a (n + 1))|) atTop (𝓝 1) := by
  sorry

theorem proof_gap_exercise_2833_2
  (a : ℕ -> ℝ) (x : ℝ)
  (hx : x ≠ -1)
  (ha : ∀ n : ℕ, a n = 1 /. (2 * n + 1))
  (hlim : Tendsto (fun n : ℕ => |(a n /. a (n + 1))|) atTop (𝓝 1))
  : |((1 - x) /. (1 + x))| < 1 ↔ x > 0 := by
  sorry

theorem proof_gap_exercise_2833_3
  (a : ℕ -> ℝ) (x : ℝ)
  (hx : x ≠ -1)
  (ha : ∀ n : ℕ, a n = 1 /. (2 * n + 1))
  (hlim : Tendsto (fun n : ℕ => |(a n /. a (n + 1))|) atTop (𝓝 1))
  (hineq : |((1 - x) /. (1 + x))| < 1 ↔ x > 0)
  : x > 0 -> AbsoluteConvergentSeries (fun n : ℕ => (1 /. (2 * n + 1)) * (((1 - x) /. (1 + x)) ^ n)) := by
  sorry

theorem proof_gap_exercise_2833_4
  (a : ℕ -> ℝ) (x : ℝ)
  (hx : x ≠ -1)
  (ha : ∀ n : ℕ, a n = 1 /. (2 * n + 1))
  (hlim : Tendsto (fun n : ℕ => |(a n /. a (n + 1))|) atTop (𝓝 1))
  (hineq : |((1 - x) /. (1 + x))| < 1 ↔ x > 0)
  (habs : x > 0 -> AbsoluteConvergentSeries (fun n : ℕ => (1 /. (2 * n + 1)) * (((1 - x) /. (1 + x)) ^ n)))
  : x < 0 -> x ≠ -1 -> DivergentSeries (fun n : ℕ => (1 /. (2 * n + 1)) * (((1 - x) /. (1 + x)) ^ n)) := by
  sorry

theorem proof_gap_exercise_2833_5
  (a : ℕ -> ℝ) (x : ℝ)
  (hx : x ≠ -1)
  (ha : ∀ n : ℕ, a n = 1 /. (2 * n + 1))
  (hlim : Tendsto (fun n : ℕ => |(a n /. a (n + 1))|) atTop (𝓝 1))
  (hineq : |((1 - x) /. (1 + x))| < 1 ↔ x > 0)
  (habs : x > 0 -> AbsoluteConvergentSeries (fun n : ℕ => (1 /. (2 * n + 1)) * (((1 - x) /. (1 + x)) ^ n)))
  (hdivneg : x < 0 -> x ≠ -1 -> DivergentSeries (fun n : ℕ => (1 /. (2 * n + 1)) * (((1 - x) /. (1 + x)) ^ n)))
  : x = 0 -> (∑' n : ℕ, (1 /. (2 * n + 1)) * (((1 - x) /. (1 + x)) ^ n)) =
      (∑' n : ℕ, 1 /. (2 * n + 1)) := by
  sorry

theorem proof_gap_exercise_2833_6
  (a : ℕ -> ℝ) (x : ℝ)
  (hx : x ≠ -1)
  (ha : ∀ n : ℕ, a n = 1 /. (2 * n + 1))
  (hlim : Tendsto (fun n : ℕ => |(a n /. a (n + 1))|) atTop (𝓝 1))
  (hineq : |((1 - x) /. (1 + x))| < 1 ↔ x > 0)
  (habs : x > 0 -> AbsoluteConvergentSeries (fun n : ℕ => (1 /. (2 * n + 1)) * (((1 - x) /. (1 + x)) ^ n)))
  (hdivneg : x < 0 -> x ≠ -1 -> DivergentSeries (fun n : ℕ => (1 /. (2 * n + 1)) * (((1 - x) /. (1 + x)) ^ n)))
  (hzeroeq : x = 0 -> (∑' n : ℕ, (1 /. (2 * n + 1)) * (((1 - x) /. (1 + x)) ^ n)) =
      (∑' n : ℕ, 1 /. (2 * n + 1)))
  : x = 0 -> DivergentSeries (fun n : ℕ => 1 /. (2 * n + 1)) := by
  sorry

theorem proof_gap_exercise_2833_7
  (a : ℕ -> ℝ) (x : ℝ)
  (hx : x ≠ -1)
  (ha : ∀ n : ℕ, a n = 1 /. (2 * n + 1))
  (hlim : Tendsto (fun n : ℕ => |(a n /. a (n + 1))|) atTop (𝓝 1))
  (hineq : |((1 - x) /. (1 + x))| < 1 ↔ x > 0)
  (habs : x > 0 -> AbsoluteConvergentSeries (fun n : ℕ => (1 /. (2 * n + 1)) * (((1 - x) /. (1 + x)) ^ n)))
  (hdivneg : x < 0 -> x ≠ -1 -> DivergentSeries (fun n : ℕ => (1 /. (2 * n + 1)) * (((1 - x) /. (1 + x)) ^ n)))
  (hzeroeq : x = 0 -> (∑' n : ℕ, (1 /. (2 * n + 1)) * (((1 - x) /. (1 + x)) ^ n)) =
      (∑' n : ℕ, 1 /. (2 * n + 1)))
  (hzerodiv : x = 0 -> DivergentSeries (fun n : ℕ => 1 /. (2 * n + 1)))
  : x ∈ Set.Ioi (0 : ℝ) ↔ ConvergentSeries (fun n : ℕ => a n * (((1 - x) /. (1 + x)) ^ n)) := by
  sorry

import Mathlib

attribute [local instance] Classical.propDecidable
set_option linter.style.longLine false

open Real
open scoped Nat

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

noncomputable def cosSqPowerSeries (x : ℝ) : ℝ :=
  1 + (∑' n : ℕ, if 1 ≤ n then ((-1 : ℝ) ^ n) * ((2 : ℝ) ^ (2 * n - 1) /. ((2 * n)!)) * x ^ (2 * n) else 0)

-- exercise: exercise_2852

theorem proof_gap_exercise_2852_1
  (x : ℝ)
  : cos x ^ 2 = (1 + cos (2 * x)) /. 2 := by
  sorry

theorem proof_gap_exercise_2852_2
  (x : ℝ)
  (h1 : cos x ^ 2 = (1 + cos (2 * x)) /. 2)
  : cos x ^ 2 =
      (1 /. 2) + (1 /. 2) * (∑' n : ℕ, ((-1 : ℝ) ^ n) * (((2 * x) ^ (2 * n)) /. ((2 * n)!))) := by
  sorry

theorem proof_gap_exercise_2852_3
  (x : ℝ)
  (h1 : cos x ^ 2 = (1 + cos (2 * x)) /. 2)
  (h2 : cos x ^ 2 =
      (1 /. 2) + (1 /. 2) * (∑' n : ℕ, ((-1 : ℝ) ^ n) * (((2 * x) ^ (2 * n)) /. ((2 * n)!))))
  : cos x ^ 2 = cosSqPowerSeries x := by
  sorry

theorem proof_gap_exercise_2852_4
  (x : ℝ)
  (h1 : cos x ^ 2 = (1 + cos (2 * x)) /. 2)
  (h2 : cos x ^ 2 =
      (1 /. 2) + (1 /. 2) * (∑' n : ℕ, ((-1 : ℝ) ^ n) * (((2 * x) ^ (2 * n)) /. ((2 * n)!))))
  (h3 : cos x ^ 2 = cosSqPowerSeries x)
  : {x : ℝ | Summable (fun n : ℕ => if 1 ≤ n then ((-1 : ℝ) ^ n) * ((2 : ℝ) ^ (2 * n - 1) /. ((2 * n)!)) * x ^ (2 * n) else 0)} = Set.univ := by
  sorry

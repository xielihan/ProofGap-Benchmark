import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

def lpUniformConvergentOn (u : ℕ -> ℝ -> ℝ) (s : Set ℝ) (f : ℝ -> ℝ) : Prop :=
  TendstoUniformlyOn (fun N x => (Finset.Icc 1 N).sum (fun n => u n x)) f atTop s

-- exercise: exercise_2966

theorem proof_gap_exercise_2966_1
  (f : ℝ -> ℝ)
  (q : ℝ)
  (hq : q ∈ (Set.univ : Set ℝ) ∧ |q| < 1)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) -> f x = (q * Real.sin x) /. (1 - 2 * q * Real.cos x + q ^ (2 : ℕ)))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ->
      (1 : ℂ) - (q : ℂ) * Complex.exp (Complex.I * (x : ℂ)) ≠ 0 ∧
      (1 : ℂ) - (q : ℂ) * Complex.exp (-Complex.I * (x : ℂ)) ≠ 0 := by
  sorry

theorem proof_gap_exercise_2966_2
  (f : ℝ -> ℝ)
  (q : ℝ)
  (hq : q ∈ (Set.univ : Set ℝ) ∧ |q| < 1)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) -> f x = (q * Real.sin x) /. (1 - 2 * q * Real.cos x + q ^ (2 : ℕ)))
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ->
      (1 : ℂ) - (q : ℂ) * Complex.exp (Complex.I * (x : ℂ)) ≠ 0 ∧
      (1 : ℂ) - (q : ℂ) * Complex.exp (-Complex.I * (x : ℂ)) ≠ 0)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ->
      (f x : ℂ) =
        (((q : ℂ) / (2 * Complex.I)) *
          (Complex.exp (Complex.I * (x : ℂ)) - Complex.exp (-Complex.I * (x : ℂ)))) /
        (1 - (q : ℂ) * (Complex.exp (Complex.I * (x : ℂ)) + Complex.exp (-Complex.I * (x : ℂ))) + (q : ℂ) ^ (2 : ℕ)) := by
  sorry

theorem proof_gap_exercise_2966_3
  (f : ℝ -> ℝ) (q : ℝ)
  (hq : q ∈ (Set.univ : Set ℝ) ∧ |q| < 1)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) -> f x = (q * Real.sin x) /. (1 - 2 * q * Real.cos x + q ^ (2 : ℕ)))
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) -> (1 : ℂ) - (q : ℂ) * Complex.exp (Complex.I * (x : ℂ)) ≠ 0 ∧ (1 : ℂ) - (q : ℂ) * Complex.exp (-Complex.I * (x : ℂ)) ≠ 0)
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) -> (f x : ℂ) = (((q : ℂ) / (2 * Complex.I)) * (Complex.exp (Complex.I * (x : ℂ)) - Complex.exp (-Complex.I * (x : ℂ)))) / (1 - (q : ℂ) * (Complex.exp (Complex.I * (x : ℂ)) + Complex.exp (-Complex.I * (x : ℂ))) + (q : ℂ) ^ (2 : ℕ)))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ->
      (f x : ℂ) = (1 / (2 * Complex.I)) *
        (1 / (1 - (q : ℂ) * Complex.exp (Complex.I * (x : ℂ))) -
         1 / (1 - (q : ℂ) * Complex.exp (-Complex.I * (x : ℂ)))) := by
  sorry

theorem proof_gap_exercise_2966_4
  (f : ℝ -> ℝ) (q : ℝ)
  (hq : q ∈ (Set.univ : Set ℝ) ∧ |q| < 1)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) -> f x = (q * Real.sin x) /. (1 - 2 * q * Real.cos x + q ^ (2 : ℕ)))
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) -> (1 : ℂ) - (q : ℂ) * Complex.exp (Complex.I * (x : ℂ)) ≠ 0 ∧ (1 : ℂ) - (q : ℂ) * Complex.exp (-Complex.I * (x : ℂ)) ≠ 0)
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) -> (f x : ℂ) = (((q : ℂ) / (2 * Complex.I)) * (Complex.exp (Complex.I * (x : ℂ)) - Complex.exp (-Complex.I * (x : ℂ)))) / (1 - (q : ℂ) * (Complex.exp (Complex.I * (x : ℂ)) + Complex.exp (-Complex.I * (x : ℂ))) + (q : ℂ) ^ (2 : ℕ)))
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) -> (f x : ℂ) = (1 / (2 * Complex.I)) * (1 / (1 - (q : ℂ) * Complex.exp (Complex.I * (x : ℂ))) - 1 / (1 - (q : ℂ) * Complex.exp (-Complex.I * (x : ℂ)))))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ->
      1 / (1 - (q : ℂ) * Complex.exp (Complex.I * (x : ℂ))) =
        ∑' n : ℕ, (q : ℂ) ^ n * Complex.exp (Complex.I * (n : ℂ) * (x : ℂ)) := by
  sorry

theorem proof_gap_exercise_2966_5
  (f : ℝ -> ℝ) (q : ℝ)
  (hq : q ∈ (Set.univ : Set ℝ) ∧ |q| < 1)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) -> f x = (q * Real.sin x) /. (1 - 2 * q * Real.cos x + q ^ (2 : ℕ)))
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) -> (1 : ℂ) - (q : ℂ) * Complex.exp (Complex.I * (x : ℂ)) ≠ 0 ∧ (1 : ℂ) - (q : ℂ) * Complex.exp (-Complex.I * (x : ℂ)) ≠ 0)
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) -> (f x : ℂ) = (((q : ℂ) / (2 * Complex.I)) * (Complex.exp (Complex.I * (x : ℂ)) - Complex.exp (-Complex.I * (x : ℂ)))) / (1 - (q : ℂ) * (Complex.exp (Complex.I * (x : ℂ)) + Complex.exp (-Complex.I * (x : ℂ))) + (q : ℂ) ^ (2 : ℕ)))
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) -> (f x : ℂ) = (1 / (2 * Complex.I)) * (1 / (1 - (q : ℂ) * Complex.exp (Complex.I * (x : ℂ))) - 1 / (1 - (q : ℂ) * Complex.exp (-Complex.I * (x : ℂ)))))
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) -> 1 / (1 - (q : ℂ) * Complex.exp (Complex.I * (x : ℂ))) = ∑' n : ℕ, (q : ℂ) ^ n * Complex.exp (Complex.I * (n : ℂ) * (x : ℂ)))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ->
      1 / (1 - (q : ℂ) * Complex.exp (-Complex.I * (x : ℂ))) =
        ∑' n : ℕ, (q : ℂ) ^ n * Complex.exp (-Complex.I * (n : ℂ) * (x : ℂ)) := by
  sorry

theorem proof_gap_exercise_2966_6
  (f : ℝ -> ℝ) (q : ℝ)
  (hq : q ∈ (Set.univ : Set ℝ) ∧ |q| < 1)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) -> f x = (q * Real.sin x) /. (1 - 2 * q * Real.cos x + q ^ (2 : ℕ)))
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) -> (1 : ℂ) - (q : ℂ) * Complex.exp (Complex.I * (x : ℂ)) ≠ 0 ∧ (1 : ℂ) - (q : ℂ) * Complex.exp (-Complex.I * (x : ℂ)) ≠ 0)
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) -> (f x : ℂ) = (((q : ℂ) / (2 * Complex.I)) * (Complex.exp (Complex.I * (x : ℂ)) - Complex.exp (-Complex.I * (x : ℂ)))) / (1 - (q : ℂ) * (Complex.exp (Complex.I * (x : ℂ)) + Complex.exp (-Complex.I * (x : ℂ))) + (q : ℂ) ^ (2 : ℕ)))
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) -> (f x : ℂ) = (1 / (2 * Complex.I)) * (1 / (1 - (q : ℂ) * Complex.exp (Complex.I * (x : ℂ))) - 1 / (1 - (q : ℂ) * Complex.exp (-Complex.I * (x : ℂ)))))
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) -> 1 / (1 - (q : ℂ) * Complex.exp (Complex.I * (x : ℂ))) = ∑' n : ℕ, (q : ℂ) ^ n * Complex.exp (Complex.I * (n : ℂ) * (x : ℂ)))
  (h6 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) -> 1 / (1 - (q : ℂ) * Complex.exp (-Complex.I * (x : ℂ))) = ∑' n : ℕ, (q : ℂ) ^ n * Complex.exp (-Complex.I * (n : ℂ) * (x : ℂ)))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ->
      f x = ∑' n : ℕ, if 1 ≤ n then q ^ n * Real.sin (n * x) else 0 := by
  sorry

theorem proof_gap_exercise_2966_7
  (f : ℝ -> ℝ) (q : ℝ)
  (hq : q ∈ (Set.univ : Set ℝ) ∧ |q| < 1)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) -> f x = (q * Real.sin x) /. (1 - 2 * q * Real.cos x + q ^ (2 : ℕ)))
  (h7 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) -> f x = ∑' n : ℕ, if 1 ≤ n then q ^ n * Real.sin (n * x) else 0)
  : ∀ n : ℕ, ∀ x : ℝ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ {n : ℕ | 0 < n} ∧ x ∈ (Set.univ : Set ℝ) ->
      |q ^ n * Real.sin (n * x)| ≤ |q| ^ n := by
  sorry

theorem proof_gap_exercise_2966_8
  (f : ℝ -> ℝ) (q : ℝ)
  (hq : q ∈ (Set.univ : Set ℝ) ∧ |q| < 1)
  : Summable (fun n : ℕ => if 1 ≤ n then |q| ^ n else 0) := by
  sorry

theorem proof_gap_exercise_2966_9
  (f : ℝ -> ℝ) (q : ℝ)
  (hq : q ∈ (Set.univ : Set ℝ) ∧ |q| < 1)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) -> f x = (q * Real.sin x) /. (1 - 2 * q * Real.cos x + q ^ (2 : ℕ)))
  (h7 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) -> f x = ∑' n : ℕ, if 1 ≤ n then q ^ n * Real.sin (n * x) else 0)
  (h8 : ∀ n : ℕ, ∀ x : ℝ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ {n : ℕ | 0 < n} ∧ x ∈ (Set.univ : Set ℝ) -> |q ^ n * Real.sin (n * x)| ≤ |q| ^ n)
  (h9 : Summable (fun n : ℕ => if 1 ≤ n then |q| ^ n else 0))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ->
      lpUniformConvergentOn (fun n x => q ^ n * Real.sin (n * x)) (Set.univ : Set ℝ) f := by
  sorry

theorem proof_gap_exercise_2966_10
  (f : ℝ -> ℝ) (q : ℝ)
  (hq : q ∈ (Set.univ : Set ℝ) ∧ |q| < 1)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) -> f x = (q * Real.sin x) /. (1 - 2 * q * Real.cos x + q ^ (2 : ℕ)))
  : Function.Periodic f (2 * Real.pi) := by
  sorry

theorem proof_gap_exercise_2966_11
  (f : ℝ -> ℝ) (q : ℝ)
  (hq : q ∈ (Set.univ : Set ℝ) ∧ |q| < 1)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) -> f x = (q * Real.sin x) /. (1 - 2 * q * Real.cos x + q ^ (2 : ℕ)))
  (h10 : Function.Periodic f (2 * Real.pi))
  : Function.Odd f := by
  sorry

theorem proof_gap_exercise_2966_12
  (f : ℝ -> ℝ) (q : ℝ)
  (hq : q ∈ (Set.univ : Set ℝ) ∧ |q| < 1)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) -> f x = (q * Real.sin x) /. (1 - 2 * q * Real.cos x + q ^ (2 : ℕ)))
  (h7 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) -> f x = ∑' n : ℕ, if 1 ≤ n then q ^ n * Real.sin (n * x) else 0)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ->
      (∑' n : ℕ, if 1 ≤ n then q ^ n * Real.sin (n * x) else 0) =
        (q * Real.sin x) /. (1 - 2 * q * Real.cos x + q ^ (2 : ℕ)) := by
  sorry

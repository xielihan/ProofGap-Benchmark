import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat

open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

open scoped RealInnerProductSpace

noncomputable def lpFunDeri {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] (f g : E -> ℝ) : E -> ℝ :=
  fun x => (inner ℝ (gradient f x) (gradient g x)) /. (‖gradient g x‖ ^ 2)

def lpLeftDifferentiable (f : ℝ -> ℝ) : Prop :=
  ∀ x, DifferentiableWithinAt ℝ f (Set.Iio x) x

def lpRightDifferentiable (f : ℝ -> ℝ) : Prop :=
  ∀ x, DifferentiableWithinAt ℝ f (Set.Ioi x) x

def lpLeftDifferentiableOn (f : ℝ -> ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, DifferentiableWithinAt ℝ f (s ∩ Set.Iio x) x

def lpRightDifferentiableOn (f : ℝ -> ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, DifferentiableWithinAt ℝ f (s ∩ Set.Ioi x) x

def lpMaximumPoints {α β : Type*} [Preorder β] (f : α -> β) : Set α :=
  {x | ∀ y, f y ≤ f x}

def lpMinimumPoints {α β : Type*} [Preorder β] (f : α -> β) : Set α :=
  {x | ∀ y, f x ≤ f y}

def lpMaximumPointsOn {α β : Type*} [Preorder β] (f : α -> β) (s : Set α) : Set α :=
  {x | x ∈ s ∧ ∀ y ∈ s, f y ≤ f x}

def lpMinimumPointsOn {α β : Type*} [Preorder β] (f : α -> β) (s : Set α) : Set α :=
  {x | x ∈ s ∧ ∀ y ∈ s, f x ≤ f y}

noncomputable def lpRadiusOfConvergence {𝕜 : Type*} [NormedField 𝕜] (a : ℕ -> 𝕜) : ENNReal :=
  ⨆ (r : NNReal), ⨆ (_h : Summable (fun n : ℕ => ‖a n‖ * (r : ℝ) ^ n)), (r : ENNReal)

-- exercise: exercise_2867

theorem proof_gap_exercise_2867_1
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (((1 + x) + (x ^ (2 : ℕ))) + (x ^ (3 : ℕ))) > 0)
  : (Real.log (((1 + x) + (x ^ (2 : ℕ))) + (x ^ (3 : ℕ)))) = (Real.log ((1 + x) * (1 + (x ^ (2 : ℕ))))) := by
  sorry

theorem proof_gap_exercise_2867_2
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (((1 + x) + (x ^ (2 : ℕ))) + (x ^ (3 : ℕ))) > 0)
  (h3 : (Real.log (((1 + x) + (x ^ (2 : ℕ))) + (x ^ (3 : ℕ)))) = (Real.log ((1 + x) * (1 + (x ^ (2 : ℕ))))))
  : (Real.log ((1 + x) * (1 + (x ^ (2 : ℕ))))) = ((Real.log (1 + x)) + (Real.log (1 + (x ^ (2 : ℕ))))) := by
  sorry

theorem proof_gap_exercise_2867_3
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (((1 + x) + (x ^ (2 : ℕ))) + (x ^ (3 : ℕ))) > 0)
  (h3 : (Real.log (((1 + x) + (x ^ (2 : ℕ))) + (x ^ (3 : ℕ)))) = (Real.log ((1 + x) * (1 + (x ^ (2 : ℕ))))))
  (h4 : (Real.log ((1 + x) * (1 + (x ^ (2 : ℕ))))) = ((Real.log (1 + x)) + (Real.log (1 + (x ^ (2 : ℕ))))))
  : (Real.log (((1 + x) + (x ^ (2 : ℕ))) + (x ^ (3 : ℕ)))) = ((Real.log (1 + x)) + (Real.log (1 + (x ^ (2 : ℕ))))) := by
  sorry

theorem proof_gap_exercise_2867_4
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (((1 + x) + (x ^ (2 : ℕ))) + (x ^ (3 : ℕ))) > 0)
  (h3 : (Real.log (((1 + x) + (x ^ (2 : ℕ))) + (x ^ (3 : ℕ)))) = (Real.log ((1 + x) * (1 + (x ^ (2 : ℕ))))))
  (h4 : (Real.log ((1 + x) * (1 + (x ^ (2 : ℕ))))) = ((Real.log (1 + x)) + (Real.log (1 + (x ^ (2 : ℕ))))))
  (h5 : (Real.log (((1 + x) + (x ^ (2 : ℕ))) + (x ^ (3 : ℕ)))) = ((Real.log (1 + x)) + (Real.log (1 + (x ^ (2 : ℕ))))))
  : (((-(1 : ℝ)) < x) ∧ (x ≤ 1)) → ((Real.log (1 + x)) = (∑' n, if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ (n - 1)) * ((x ^ n) /. n)) else 0)) := by
  sorry

theorem proof_gap_exercise_2867_5
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (((1 + x) + (x ^ (2 : ℕ))) + (x ^ (3 : ℕ))) > 0)
  (h3 : (Real.log (((1 + x) + (x ^ (2 : ℕ))) + (x ^ (3 : ℕ)))) = (Real.log ((1 + x) * (1 + (x ^ (2 : ℕ))))))
  (h4 : (Real.log ((1 + x) * (1 + (x ^ (2 : ℕ))))) = ((Real.log (1 + x)) + (Real.log (1 + (x ^ (2 : ℕ))))))
  (h5 : (Real.log (((1 + x) + (x ^ (2 : ℕ))) + (x ^ (3 : ℕ)))) = ((Real.log (1 + x)) + (Real.log (1 + (x ^ (2 : ℕ))))))
  (h6 : (((-(1 : ℝ)) < x) ∧ (x ≤ 1)) → ((Real.log (1 + x)) = (∑' n, if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ (n - 1)) * ((x ^ n) /. n)) else 0)))
  : (((-(1 : ℝ)) ≤ x) ∧ (x ≤ 1)) → ((Real.log (1 + (x ^ (2 : ℕ)))) = (∑' n, if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ (n - 1)) * ((x ^ (2 * n)) /. n)) else 0)) := by
  sorry

theorem proof_gap_exercise_2867_6
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (((1 + x) + (x ^ (2 : ℕ))) + (x ^ (3 : ℕ))) > 0)
  (h3 : (Real.log (((1 + x) + (x ^ (2 : ℕ))) + (x ^ (3 : ℕ)))) = (Real.log ((1 + x) * (1 + (x ^ (2 : ℕ))))))
  (h4 : (Real.log ((1 + x) * (1 + (x ^ (2 : ℕ))))) = ((Real.log (1 + x)) + (Real.log (1 + (x ^ (2 : ℕ))))))
  (h5 : (Real.log (((1 + x) + (x ^ (2 : ℕ))) + (x ^ (3 : ℕ)))) = ((Real.log (1 + x)) + (Real.log (1 + (x ^ (2 : ℕ))))))
  (h6 : (((-(1 : ℝ)) < x) ∧ (x ≤ 1)) → ((Real.log (1 + x)) = (∑' n, if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ (n - 1)) * ((x ^ n) /. n)) else 0)))
  (h7 : (((-(1 : ℝ)) ≤ x) ∧ (x ≤ 1)) → ((Real.log (1 + (x ^ (2 : ℕ)))) = (∑' n, if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ (n - 1)) * ((x ^ (2 * n)) /. n)) else 0)))
  : ((-(1 : ℝ)) < x) → ((x ≤ 1) → ((Real.log (((1 + x) + (x ^ (2 : ℕ))) + (x ^ (3 : ℕ)))) = ((∑' n, if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ (n - 1)) * ((x ^ n) /. n)) else 0) + (∑' n, if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ (n - 1)) * ((x ^ (2 * n)) /. n)) else 0)))) := by
  sorry

theorem proof_gap_exercise_2867_7
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (((1 + x) + (x ^ (2 : ℕ))) + (x ^ (3 : ℕ))) > 0)
  (h3 : (Real.log (((1 + x) + (x ^ (2 : ℕ))) + (x ^ (3 : ℕ)))) = (Real.log ((1 + x) * (1 + (x ^ (2 : ℕ))))))
  (h4 : (Real.log ((1 + x) * (1 + (x ^ (2 : ℕ))))) = ((Real.log (1 + x)) + (Real.log (1 + (x ^ (2 : ℕ))))))
  (h5 : (Real.log (((1 + x) + (x ^ (2 : ℕ))) + (x ^ (3 : ℕ)))) = ((Real.log (1 + x)) + (Real.log (1 + (x ^ (2 : ℕ))))))
  (h6 : (((-(1 : ℝ)) < x) ∧ (x ≤ 1)) → ((Real.log (1 + x)) = (∑' n, if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ (n - 1)) * ((x ^ n) /. n)) else 0)))
  (h7 : (((-(1 : ℝ)) ≤ x) ∧ (x ≤ 1)) → ((Real.log (1 + (x ^ (2 : ℕ)))) = (∑' n, if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ (n - 1)) * ((x ^ (2 * n)) /. n)) else 0)))
  (h8 : ((-(1 : ℝ)) < x) → ((x ≤ 1) → ((Real.log (((1 + x) + (x ^ (2 : ℕ))) + (x ^ (3 : ℕ)))) = ((∑' n, if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ (n - 1)) * ((x ^ n) /. n)) else 0) + (∑' n, if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ (n - 1)) * ((x ^ (2 * n)) /. n)) else 0)))))
  : ((-(1 : ℝ)) < x) → ((x ≤ 1) → ((Real.log (((1 + x) + (x ^ (2 : ℕ))) + (x ^ (3 : ℕ)))) = (∑' m, if (1 : ℕ) ≤ m then (((((-(1 : ℤ)) ^ (m - 1)) + (((-(1 : ℝ)) ^ (⌊(m /. 2)⌋ - 1)) * (1 + ((-(1 : ℤ)) ^ m)))) /. m) * (x ^ m)) else 0))) := by
  sorry

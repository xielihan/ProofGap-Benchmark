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

-- exercise: exercise_3003

theorem proof_gap_exercise_3003_1
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 2)) → (((n ^ (3 : ℕ)) /. ((n + 1))!) = (((1 /. ((n - 2))!) + (1 /. (n)!)) - (1 /. ((n + 1))!))))) := by
  sorry

theorem proof_gap_exercise_3003_2
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 2)) → (((n ^ (3 : ℕ)) /. ((n + 1))!) = (((1 /. ((n - 2))!) + (1 /. (n)!)) - (1 /. ((n + 1))!))))))
  : (∑' n, if (0 : ℕ) ≤ n then (((((-(1 : ℤ)) ^ n) * (n ^ (3 : ℕ))) /. ((n + 1))!) * (x ^ n)) else 0) = (∑' n, if (0 : ℕ) ≤ n then (((n ^ (3 : ℕ)) /. ((n + 1))!) * ((-x) ^ n)) else 0) := by
  sorry

theorem proof_gap_exercise_3003_3
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 2)) → (((n ^ (3 : ℕ)) /. ((n + 1))!) = (((1 /. ((n - 2))!) + (1 /. (n)!)) - (1 /. ((n + 1))!))))))
  (h3 : (∑' n, if (0 : ℕ) ≤ n then (((((-(1 : ℤ)) ^ n) * (n ^ (3 : ℕ))) /. ((n + 1))!) * (x ^ n)) else 0) = (∑' n, if (0 : ℕ) ≤ n then (((n ^ (3 : ℕ)) /. ((n + 1))!) * ((-x) ^ n)) else 0))
  : (∑' n, if (0 : ℕ) ≤ n then (((n ^ (3 : ℕ)) /. ((n + 1))!) * ((-x) ^ n)) else 0) = ((((-(x /. 2)) + (∑' n, if (2 : ℕ) ≤ n then (((-x) ^ n) /. ((n - 2))!) else 0)) + (∑' n, if (2 : ℕ) ≤ n then (((-x) ^ n) /. (n)!) else 0)) - (∑' n, if (2 : ℕ) ≤ n then (((-x) ^ n) /. ((n + 1))!) else 0)) := by
  sorry

theorem proof_gap_exercise_3003_4
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 2)) → (((n ^ (3 : ℕ)) /. ((n + 1))!) = (((1 /. ((n - 2))!) + (1 /. (n)!)) - (1 /. ((n + 1))!))))))
  (h3 : (∑' n, if (0 : ℕ) ≤ n then (((((-(1 : ℤ)) ^ n) * (n ^ (3 : ℕ))) /. ((n + 1))!) * (x ^ n)) else 0) = (∑' n, if (0 : ℕ) ≤ n then (((n ^ (3 : ℕ)) /. ((n + 1))!) * ((-x) ^ n)) else 0))
  (h4 : (∑' n, if (0 : ℕ) ≤ n then (((n ^ (3 : ℕ)) /. ((n + 1))!) * ((-x) ^ n)) else 0) = ((((-(x /. 2)) + (∑' n, if (2 : ℕ) ≤ n then (((-x) ^ n) /. ((n - 2))!) else 0)) + (∑' n, if (2 : ℕ) ≤ n then (((-x) ^ n) /. (n)!) else 0)) - (∑' n, if (2 : ℕ) ≤ n then (((-x) ^ n) /. ((n + 1))!) else 0)))
  : (x ≠ 0) → ((∑' n, if (0 : ℕ) ≤ n then (((((-(1 : ℤ)) ^ n) * (n ^ (3 : ℕ))) /. ((n + 1))!) * (x ^ n)) else 0) = ((((-(x /. 2)) + ((x ^ (2 : ℕ)) * (∑' n, if (2 : ℕ) ≤ n then (((-x) ^ (n - 2)) /. ((n - 2))!) else 0))) + (∑' n, if (2 : ℕ) ≤ n then (((-x) ^ n) /. (n)!) else 0)) + ((1 /. x) * (∑' n, if (2 : ℕ) ≤ n then (((-x) ^ (n + 1)) /. ((n + 1))!) else 0)))) := by
  sorry

theorem proof_gap_exercise_3003_5
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 2)) → (((n ^ (3 : ℕ)) /. ((n + 1))!) = (((1 /. ((n - 2))!) + (1 /. (n)!)) - (1 /. ((n + 1))!))))))
  (h3 : (∑' n, if (0 : ℕ) ≤ n then (((((-(1 : ℤ)) ^ n) * (n ^ (3 : ℕ))) /. ((n + 1))!) * (x ^ n)) else 0) = (∑' n, if (0 : ℕ) ≤ n then (((n ^ (3 : ℕ)) /. ((n + 1))!) * ((-x) ^ n)) else 0))
  (h4 : (∑' n, if (0 : ℕ) ≤ n then (((n ^ (3 : ℕ)) /. ((n + 1))!) * ((-x) ^ n)) else 0) = ((((-(x /. 2)) + (∑' n, if (2 : ℕ) ≤ n then (((-x) ^ n) /. ((n - 2))!) else 0)) + (∑' n, if (2 : ℕ) ≤ n then (((-x) ^ n) /. (n)!) else 0)) - (∑' n, if (2 : ℕ) ≤ n then (((-x) ^ n) /. ((n + 1))!) else 0)))
  (h5 : (x ≠ 0) → ((∑' n, if (0 : ℕ) ≤ n then (((((-(1 : ℤ)) ^ n) * (n ^ (3 : ℕ))) /. ((n + 1))!) * (x ^ n)) else 0) = ((((-(x /. 2)) + ((x ^ (2 : ℕ)) * (∑' n, if (2 : ℕ) ≤ n then (((-x) ^ (n - 2)) /. ((n - 2))!) else 0))) + (∑' n, if (2 : ℕ) ≤ n then (((-x) ^ n) /. (n)!) else 0)) + ((1 /. x) * (∑' n, if (2 : ℕ) ≤ n then (((-x) ^ (n + 1)) /. ((n + 1))!) else 0)))))
  : (x ≠ 0) → ((∑' n, if (0 : ℕ) ≤ n then (((((-(1 : ℤ)) ^ n) * (n ^ (3 : ℕ))) /. ((n + 1))!) * (x ^ n)) else 0) = ((((((-(x /. 2)) + ((x ^ (2 : ℕ)) * (Real.exp (-x)))) + (Real.exp (-x))) - 1) + x) + ((1 /. x) * ((((Real.exp (-x)) - 1) + x) - ((x ^ (2 : ℕ)) /. ((2 : ℕ))!))))) := by
  sorry

theorem proof_gap_exercise_3003_6
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 2)) → (((n ^ (3 : ℕ)) /. ((n + 1))!) = (((1 /. ((n - 2))!) + (1 /. (n)!)) - (1 /. ((n + 1))!))))))
  (h3 : (∑' n, if (0 : ℕ) ≤ n then (((((-(1 : ℤ)) ^ n) * (n ^ (3 : ℕ))) /. ((n + 1))!) * (x ^ n)) else 0) = (∑' n, if (0 : ℕ) ≤ n then (((n ^ (3 : ℕ)) /. ((n + 1))!) * ((-x) ^ n)) else 0))
  (h4 : (∑' n, if (0 : ℕ) ≤ n then (((n ^ (3 : ℕ)) /. ((n + 1))!) * ((-x) ^ n)) else 0) = ((((-(x /. 2)) + (∑' n, if (2 : ℕ) ≤ n then (((-x) ^ n) /. ((n - 2))!) else 0)) + (∑' n, if (2 : ℕ) ≤ n then (((-x) ^ n) /. (n)!) else 0)) - (∑' n, if (2 : ℕ) ≤ n then (((-x) ^ n) /. ((n + 1))!) else 0)))
  (h5 : (x ≠ 0) → ((∑' n, if (0 : ℕ) ≤ n then (((((-(1 : ℤ)) ^ n) * (n ^ (3 : ℕ))) /. ((n + 1))!) * (x ^ n)) else 0) = ((((-(x /. 2)) + ((x ^ (2 : ℕ)) * (∑' n, if (2 : ℕ) ≤ n then (((-x) ^ (n - 2)) /. ((n - 2))!) else 0))) + (∑' n, if (2 : ℕ) ≤ n then (((-x) ^ n) /. (n)!) else 0)) + ((1 /. x) * (∑' n, if (2 : ℕ) ≤ n then (((-x) ^ (n + 1)) /. ((n + 1))!) else 0)))))
  (h6 : (x ≠ 0) → ((∑' n, if (0 : ℕ) ≤ n then (((((-(1 : ℤ)) ^ n) * (n ^ (3 : ℕ))) /. ((n + 1))!) * (x ^ n)) else 0) = ((((((-(x /. 2)) + ((x ^ (2 : ℕ)) * (Real.exp (-x)))) + (Real.exp (-x))) - 1) + x) + ((1 /. x) * ((((Real.exp (-x)) - 1) + x) - ((x ^ (2 : ℕ)) /. ((2 : ℕ))!))))))
  : (x ≠ 0) → ((∑' n, if (0 : ℕ) ≤ n then (((((-(1 : ℤ)) ^ n) * (n ^ (3 : ℕ))) /. ((n + 1))!) * (x ^ n)) else 0) = (((Real.exp (-x)) * (((x ^ (2 : ℕ)) + 1) + (1 /. x))) - (1 /. x))) := by
  sorry

theorem proof_gap_exercise_3003_7
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 2)) → (((n ^ (3 : ℕ)) /. ((n + 1))!) = (((1 /. ((n - 2))!) + (1 /. (n)!)) - (1 /. ((n + 1))!))))))
  (h3 : (∑' n, if (0 : ℕ) ≤ n then (((((-(1 : ℤ)) ^ n) * (n ^ (3 : ℕ))) /. ((n + 1))!) * (x ^ n)) else 0) = (∑' n, if (0 : ℕ) ≤ n then (((n ^ (3 : ℕ)) /. ((n + 1))!) * ((-x) ^ n)) else 0))
  (h4 : (∑' n, if (0 : ℕ) ≤ n then (((n ^ (3 : ℕ)) /. ((n + 1))!) * ((-x) ^ n)) else 0) = ((((-(x /. 2)) + (∑' n, if (2 : ℕ) ≤ n then (((-x) ^ n) /. ((n - 2))!) else 0)) + (∑' n, if (2 : ℕ) ≤ n then (((-x) ^ n) /. (n)!) else 0)) - (∑' n, if (2 : ℕ) ≤ n then (((-x) ^ n) /. ((n + 1))!) else 0)))
  (h5 : (x ≠ 0) → ((∑' n, if (0 : ℕ) ≤ n then (((((-(1 : ℤ)) ^ n) * (n ^ (3 : ℕ))) /. ((n + 1))!) * (x ^ n)) else 0) = ((((-(x /. 2)) + ((x ^ (2 : ℕ)) * (∑' n, if (2 : ℕ) ≤ n then (((-x) ^ (n - 2)) /. ((n - 2))!) else 0))) + (∑' n, if (2 : ℕ) ≤ n then (((-x) ^ n) /. (n)!) else 0)) + ((1 /. x) * (∑' n, if (2 : ℕ) ≤ n then (((-x) ^ (n + 1)) /. ((n + 1))!) else 0)))))
  (h6 : (x ≠ 0) → ((∑' n, if (0 : ℕ) ≤ n then (((((-(1 : ℤ)) ^ n) * (n ^ (3 : ℕ))) /. ((n + 1))!) * (x ^ n)) else 0) = ((((((-(x /. 2)) + ((x ^ (2 : ℕ)) * (Real.exp (-x)))) + (Real.exp (-x))) - 1) + x) + ((1 /. x) * ((((Real.exp (-x)) - 1) + x) - ((x ^ (2 : ℕ)) /. ((2 : ℕ))!))))))
  (h7 : (x ≠ 0) → ((∑' n, if (0 : ℕ) ≤ n then (((((-(1 : ℤ)) ^ n) * (n ^ (3 : ℕ))) /. ((n + 1))!) * (x ^ n)) else 0) = (((Real.exp (-x)) * (((x ^ (2 : ℕ)) + 1) + (1 /. x))) - (1 /. x))))
  : (x = 0) → ((∑' n, if (0 : ℕ) ≤ n then (((((-(1 : ℤ)) ^ n) * (n ^ (3 : ℕ))) /. ((n + 1))!) * (x ^ n)) else 0) = 0) := by
  sorry

theorem proof_gap_exercise_3003_8
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 2)) → (((n ^ (3 : ℕ)) /. ((n + 1))!) = (((1 /. ((n - 2))!) + (1 /. (n)!)) - (1 /. ((n + 1))!))))))
  (h3 : (∑' n, if (0 : ℕ) ≤ n then (((((-(1 : ℤ)) ^ n) * (n ^ (3 : ℕ))) /. ((n + 1))!) * (x ^ n)) else 0) = (∑' n, if (0 : ℕ) ≤ n then (((n ^ (3 : ℕ)) /. ((n + 1))!) * ((-x) ^ n)) else 0))
  (h4 : (∑' n, if (0 : ℕ) ≤ n then (((n ^ (3 : ℕ)) /. ((n + 1))!) * ((-x) ^ n)) else 0) = ((((-(x /. 2)) + (∑' n, if (2 : ℕ) ≤ n then (((-x) ^ n) /. ((n - 2))!) else 0)) + (∑' n, if (2 : ℕ) ≤ n then (((-x) ^ n) /. (n)!) else 0)) - (∑' n, if (2 : ℕ) ≤ n then (((-x) ^ n) /. ((n + 1))!) else 0)))
  (h5 : (x ≠ 0) → ((∑' n, if (0 : ℕ) ≤ n then (((((-(1 : ℤ)) ^ n) * (n ^ (3 : ℕ))) /. ((n + 1))!) * (x ^ n)) else 0) = ((((-(x /. 2)) + ((x ^ (2 : ℕ)) * (∑' n, if (2 : ℕ) ≤ n then (((-x) ^ (n - 2)) /. ((n - 2))!) else 0))) + (∑' n, if (2 : ℕ) ≤ n then (((-x) ^ n) /. (n)!) else 0)) + ((1 /. x) * (∑' n, if (2 : ℕ) ≤ n then (((-x) ^ (n + 1)) /. ((n + 1))!) else 0)))))
  (h6 : (x ≠ 0) → ((∑' n, if (0 : ℕ) ≤ n then (((((-(1 : ℤ)) ^ n) * (n ^ (3 : ℕ))) /. ((n + 1))!) * (x ^ n)) else 0) = ((((((-(x /. 2)) + ((x ^ (2 : ℕ)) * (Real.exp (-x)))) + (Real.exp (-x))) - 1) + x) + ((1 /. x) * ((((Real.exp (-x)) - 1) + x) - ((x ^ (2 : ℕ)) /. ((2 : ℕ))!))))))
  (h7 : (x ≠ 0) → ((∑' n, if (0 : ℕ) ≤ n then (((((-(1 : ℤ)) ^ n) * (n ^ (3 : ℕ))) /. ((n + 1))!) * (x ^ n)) else 0) = (((Real.exp (-x)) * (((x ^ (2 : ℕ)) + 1) + (1 /. x))) - (1 /. x))))
  (h8 : (x = 0) → ((∑' n, if (0 : ℕ) ≤ n then (((((-(1 : ℤ)) ^ n) * (n ^ (3 : ℕ))) /. ((n + 1))!) * (x ^ n)) else 0) = 0))
  : (∑' n, if (0 : ℕ) ≤ n then (((((-(1 : ℤ)) ^ n) * (n ^ (3 : ℕ))) /. ((n + 1))!) * (x ^ n)) else 0) = (if (x ≠ 0) then (((Real.exp (-x)) * (((x ^ (2 : ℕ)) + 1) + (1 /. x))) - (1 /. x)) else (if (x = 0) then 0 else 0)) := by
  sorry

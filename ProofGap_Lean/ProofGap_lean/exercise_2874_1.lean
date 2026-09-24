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

-- exercise: exercise_2874_1

theorem proof_gap_exercise_2874_1_1
  (f : (ℝ -> ℝ))
  (x : ℝ)
  (h : ℝ)
  (n : ℕ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : h ∈ (Set.univ : Set ℝ))
  (h3 : (n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1})))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((f x_1) = (Real.exp (x_1 ^ (2 : ℕ)))))))
  : ((f (x + h)) - (f x)) = ((Real.exp ((x + h) ^ (2 : ℕ))) - (Real.exp (x ^ (2 : ℕ)))) := by
  sorry

theorem proof_gap_exercise_2874_1_2
  (f : (ℝ -> ℝ))
  (x : ℝ)
  (h : ℝ)
  (n : ℕ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : h ∈ (Set.univ : Set ℝ))
  (h3 : (n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1})))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((f x_1) = (Real.exp (x_1 ^ (2 : ℕ)))))))
  (h5 : ((f (x + h)) - (f x)) = ((Real.exp ((x + h) ^ (2 : ℕ))) - (Real.exp (x ^ (2 : ℕ)))))
  : ((Real.exp ((x + h) ^ (2 : ℕ))) - (Real.exp (x ^ (2 : ℕ)))) = ((Real.exp (x ^ (2 : ℕ))) * ((Real.exp (((2 * x) * h) + (h ^ (2 : ℕ)))) - 1)) := by
  sorry

theorem proof_gap_exercise_2874_1_3
  (f : (ℝ -> ℝ))
  (x : ℝ)
  (h : ℝ)
  (n : ℕ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : h ∈ (Set.univ : Set ℝ))
  (h3 : (n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1})))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((f x_1) = (Real.exp (x_1 ^ (2 : ℕ)))))))
  (h5 : ((f (x + h)) - (f x)) = ((Real.exp ((x + h) ^ (2 : ℕ))) - (Real.exp (x ^ (2 : ℕ)))))
  (h6 : ((Real.exp ((x + h) ^ (2 : ℕ))) - (Real.exp (x ^ (2 : ℕ)))) = ((Real.exp (x ^ (2 : ℕ))) * ((Real.exp (((2 * x) * h) + (h ^ (2 : ℕ)))) - 1)))
  : ((f (x + h)) - (f x)) = ((Real.exp (x ^ (2 : ℕ))) * ((Real.exp (((2 * x) * h) + (h ^ (2 : ℕ)))) - 1)) := by
  sorry

theorem proof_gap_exercise_2874_1_4
  (f : (ℝ -> ℝ))
  (x : ℝ)
  (h : ℝ)
  (n : ℕ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : h ∈ (Set.univ : Set ℝ))
  (h3 : (n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1})))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((f x_1) = (Real.exp (x_1 ^ (2 : ℕ)))))))
  (h5 : ((f (x + h)) - (f x)) = ((Real.exp ((x + h) ^ (2 : ℕ))) - (Real.exp (x ^ (2 : ℕ)))))
  (h6 : ((Real.exp ((x + h) ^ (2 : ℕ))) - (Real.exp (x ^ (2 : ℕ)))) = ((Real.exp (x ^ (2 : ℕ))) * ((Real.exp (((2 * x) * h) + (h ^ (2 : ℕ)))) - 1)))
  (h7 : ((f (x + h)) - (f x)) = ((Real.exp (x ^ (2 : ℕ))) * ((Real.exp (((2 * x) * h) + (h ^ (2 : ℕ)))) - 1)))
  : ((Real.exp (((2 * x) * h) + (h ^ (2 : ℕ)))) - 1) = (∑' m, if (1 : ℕ) ≤ m then (((((2 * x) * h) + (h ^ (2 : ℕ))) ^ m) /. (m)!) else 0) := by
  sorry

theorem proof_gap_exercise_2874_1_5
  (f : (ℝ -> ℝ))
  (x : ℝ)
  (h : ℝ)
  (n : ℕ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : h ∈ (Set.univ : Set ℝ))
  (h3 : (n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1})))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((f x_1) = (Real.exp (x_1 ^ (2 : ℕ)))))))
  (h5 : ((f (x + h)) - (f x)) = ((Real.exp ((x + h) ^ (2 : ℕ))) - (Real.exp (x ^ (2 : ℕ)))))
  (h6 : ((Real.exp ((x + h) ^ (2 : ℕ))) - (Real.exp (x ^ (2 : ℕ)))) = ((Real.exp (x ^ (2 : ℕ))) * ((Real.exp (((2 * x) * h) + (h ^ (2 : ℕ)))) - 1)))
  (h7 : ((f (x + h)) - (f x)) = ((Real.exp (x ^ (2 : ℕ))) * ((Real.exp (((2 * x) * h) + (h ^ (2 : ℕ)))) - 1)))
  (h8 : ((Real.exp (((2 * x) * h) + (h ^ (2 : ℕ)))) - 1) = (∑' m, if (1 : ℕ) ≤ m then (((((2 * x) * h) + (h ^ (2 : ℕ))) ^ m) /. (m)!) else 0))
  : ((f (x + h)) - (f x)) = ((Real.exp (x ^ (2 : ℕ))) * (∑' m, if (1 : ℕ) ≤ m then (((((2 * x) * h) + (h ^ (2 : ℕ))) ^ m) /. (m)!) else 0)) := by
  sorry

theorem proof_gap_exercise_2874_1_6
  (f : (ℝ -> ℝ))
  (x : ℝ)
  (h : ℝ)
  (n : ℕ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : h ∈ (Set.univ : Set ℝ))
  (h3 : (n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1})))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((f x_1) = (Real.exp (x_1 ^ (2 : ℕ)))))))
  (h5 : ((f (x + h)) - (f x)) = ((Real.exp ((x + h) ^ (2 : ℕ))) - (Real.exp (x ^ (2 : ℕ)))))
  (h6 : ((Real.exp ((x + h) ^ (2 : ℕ))) - (Real.exp (x ^ (2 : ℕ)))) = ((Real.exp (x ^ (2 : ℕ))) * ((Real.exp (((2 * x) * h) + (h ^ (2 : ℕ)))) - 1)))
  (h7 : ((f (x + h)) - (f x)) = ((Real.exp (x ^ (2 : ℕ))) * ((Real.exp (((2 * x) * h) + (h ^ (2 : ℕ)))) - 1)))
  (h8 : ((Real.exp (((2 * x) * h) + (h ^ (2 : ℕ)))) - 1) = (∑' m, if (1 : ℕ) ≤ m then (((((2 * x) * h) + (h ^ (2 : ℕ))) ^ m) /. (m)!) else 0))
  (h9 : ((f (x + h)) - (f x)) = ((Real.exp (x ^ (2 : ℕ))) * (∑' m, if (1 : ℕ) ≤ m then (((((2 * x) * h) + (h ^ (2 : ℕ))) ^ m) /. (m)!) else 0)))
  : (∃ n_div : ℕ, (n_div : ℝ) = (⌊(n /. 2)⌋ : ℝ)) ∧ (((iteratedDeriv n (fun t => f t) x) /. (n)!) = ((Real.exp (x ^ (2 : ℕ))) * (∑ k ∈ Finset.Icc (0 : ℕ) ⌊(⌊(n /. 2)⌋ : ℝ)⌋₊, (((2 * x) ^ (n - (2 * k))) /. (((n - (2 * k)))! * (k)!))))) := by
  sorry

theorem proof_gap_exercise_2874_1_7
  (f : (ℝ -> ℝ))
  (x : ℝ)
  (h : ℝ)
  (n : ℕ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : h ∈ (Set.univ : Set ℝ))
  (h3 : (n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1})))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((f x_1) = (Real.exp (x_1 ^ (2 : ℕ)))))))
  (h5 : ((f (x + h)) - (f x)) = ((Real.exp ((x + h) ^ (2 : ℕ))) - (Real.exp (x ^ (2 : ℕ)))))
  (h6 : ((Real.exp ((x + h) ^ (2 : ℕ))) - (Real.exp (x ^ (2 : ℕ)))) = ((Real.exp (x ^ (2 : ℕ))) * ((Real.exp (((2 * x) * h) + (h ^ (2 : ℕ)))) - 1)))
  (h7 : ((f (x + h)) - (f x)) = ((Real.exp (x ^ (2 : ℕ))) * ((Real.exp (((2 * x) * h) + (h ^ (2 : ℕ)))) - 1)))
  (h8 : ((Real.exp (((2 * x) * h) + (h ^ (2 : ℕ)))) - 1) = (∑' m, if (1 : ℕ) ≤ m then (((((2 * x) * h) + (h ^ (2 : ℕ))) ^ m) /. (m)!) else 0))
  (h9 : ((f (x + h)) - (f x)) = ((Real.exp (x ^ (2 : ℕ))) * (∑' m, if (1 : ℕ) ≤ m then (((((2 * x) * h) + (h ^ (2 : ℕ))) ^ m) /. (m)!) else 0)))
  (h10 : ((iteratedDeriv n (fun t => f t) x) /. (n)!) = ((Real.exp (x ^ (2 : ℕ))) * (∑ k ∈ Finset.Icc (0 : ℕ) ⌊(⌊(n /. 2)⌋ : ℝ)⌋₊, (((2 * x) ^ (n - (2 * k))) /. (((n - (2 * k)))! * (k)!)))))
  : (∃ n_div : ℕ, (n_div : ℝ) = (⌊(n /. 2)⌋ : ℝ)) ∧ ((iteratedDeriv n (fun t => f t) x) = ((Real.exp (x ^ (2 : ℕ))) * (∑ k ∈ Finset.Icc (0 : ℕ) ⌊(⌊(n /. 2)⌋ : ℝ)⌋₊, (((n)! /. (((n - (2 * k)))! * (k)!)) * ((2 * x) ^ (n - (2 * k))))))) := by
  sorry

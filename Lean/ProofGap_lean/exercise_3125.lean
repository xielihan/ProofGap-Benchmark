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

-- exercise: exercise_3125

theorem proof_gap_exercise_3125_1
  (f : (ℝ -> ℝ))
  (P : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) ≤ x)) ∧ (x ≤ 1)) → ((f x) = |(x)|))))
  (h2 : (f (0 : ℝ)) = 0)
  (h3 : (f (1 /. 2)) = (1 /. 2))
  (h4 : (f (-(1 /. 2))) = (1 /. 2))
  (h5 : (f (1 : ℝ)) = 1)
  (h6 : (f (-(1 : ℝ))) = 1)
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((P x) = (((((((x * (x - (1 /. 2))) * ((x ^ (2 : ℕ)) - 1)) /. ((((-(1 /. 2)) * (-(1 : ℝ))) * (1 /. 2)) * (-(3 /. 2)))) * (1 /. 2)) + ((((x * (x + (1 /. 2))) * ((x ^ (2 : ℕ)) - 1)) /. ((((1 /. 2) * 1) * (3 /. 2)) * (-(1 /. 2)))) * (1 /. 2))) + ((((x * (x - 1)) * ((x ^ (2 : ℕ)) - (1 /. 4))) /. ((((-(1 : ℝ)) * (-(1 /. 2))) * (-(3 /. 2))) * (-(2 : ℝ)))) * 1)) + ((((x * (x + 1)) * ((x ^ (2 : ℕ)) - (1 /. 4))) /. (((1 * (3 /. 2)) * (1 /. 2)) * 2)) * 1))))) := by
  sorry

theorem proof_gap_exercise_3125_2
  (f : (ℝ -> ℝ))
  (P : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) ≤ x)) ∧ (x ≤ 1)) → ((f x) = |(x)|))))
  (h2 : (f (0 : ℝ)) = 0)
  (h3 : (f (1 /. 2)) = (1 /. 2))
  (h4 : (f (-(1 /. 2))) = (1 /. 2))
  (h5 : (f (1 : ℝ)) = 1)
  (h6 : (f (-(1 : ℝ))) = 1)
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((P x) = (((((((x * (x - (1 /. 2))) * ((x ^ (2 : ℕ)) - 1)) /. ((((-(1 /. 2)) * (-(1 : ℝ))) * (1 /. 2)) * (-(3 /. 2)))) * (1 /. 2)) + ((((x * (x + (1 /. 2))) * ((x ^ (2 : ℕ)) - 1)) /. ((((1 /. 2) * 1) * (3 /. 2)) * (-(1 /. 2)))) * (1 /. 2))) + ((((x * (x - 1)) * ((x ^ (2 : ℕ)) - (1 /. 4))) /. ((((-(1 : ℝ)) * (-(1 /. 2))) * (-(3 /. 2))) * (-(2 : ℝ)))) * 1)) + ((((x * (x + 1)) * ((x ^ (2 : ℕ)) - (1 /. 4))) /. (((1 * (3 /. 2)) * (1 /. 2)) * 2)) * 1))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| ≤ 1)) → ((P x) = (((x ^ (2 : ℕ)) /. 3) * (7 - (4 * (x ^ (2 : ℕ)))))))) := by
  sorry

theorem proof_gap_exercise_3125_3
  (f : (ℝ -> ℝ))
  (P : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) ≤ x)) ∧ (x ≤ 1)) → ((f x) = |(x)|))))
  (h2 : (f (0 : ℝ)) = 0)
  (h3 : (f (1 /. 2)) = (1 /. 2))
  (h4 : (f (-(1 /. 2))) = (1 /. 2))
  (h5 : (f (1 : ℝ)) = 1)
  (h6 : (f (-(1 : ℝ))) = 1)
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((P x) = (((((((x * (x - (1 /. 2))) * ((x ^ (2 : ℕ)) - 1)) /. ((((-(1 /. 2)) * (-(1 : ℝ))) * (1 /. 2)) * (-(3 /. 2)))) * (1 /. 2)) + ((((x * (x + (1 /. 2))) * ((x ^ (2 : ℕ)) - 1)) /. ((((1 /. 2) * 1) * (3 /. 2)) * (-(1 /. 2)))) * (1 /. 2))) + ((((x * (x - 1)) * ((x ^ (2 : ℕ)) - (1 /. 4))) /. ((((-(1 : ℝ)) * (-(1 /. 2))) * (-(3 /. 2))) * (-(2 : ℝ)))) * 1)) + ((((x * (x + 1)) * ((x ^ (2 : ℕ)) - (1 /. 4))) /. (((1 * (3 /. 2)) * (1 /. 2)) * 2)) * 1))))))
  (h8 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| ≤ 1)) → ((P x) = (((x ^ (2 : ℕ)) /. 3) * (7 - (4 * (x ^ (2 : ℕ)))))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| ≤ 1)) → (|((f x) - (P x))| ≤ |(((f x) - (P x)))|))) := by
  sorry

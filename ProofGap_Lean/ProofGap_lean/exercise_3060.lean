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

-- exercise: exercise_3060

theorem proof_gap_exercise_3060_1
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((Real.sin x) = (x * (∏' n, if (1 : ℕ) ≤ n then (1 - ((x ^ (2 : ℕ)) /. ((n ^ (2 : ℕ)) * (Real.pi ^ (2 : ℕ))))) else 1))))) := by
  sorry

theorem proof_gap_exercise_3060_2
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((Real.sin x) = (x * (∏' n, if (1 : ℕ) ≤ n then (1 - ((x ^ (2 : ℕ)) /. ((n ^ (2 : ℕ)) * (Real.pi ^ (2 : ℕ))))) else 1))))))
  : (Real.sin (Real.pi /. 3)) = ((Real.pi /. 3) * (∏' n, if (1 : ℕ) ≤ n then (1 - (1 /. ((3 * n) ^ (2 : ℕ)))) else 1)) := by
  sorry

theorem proof_gap_exercise_3060_3
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((Real.sin x) = (x * (∏' n, if (1 : ℕ) ≤ n then (1 - ((x ^ (2 : ℕ)) /. ((n ^ (2 : ℕ)) * (Real.pi ^ (2 : ℕ))))) else 1))))))
  (h2 : (Real.sin (Real.pi /. 3)) = ((Real.pi /. 3) * (∏' n, if (1 : ℕ) ≤ n then (1 - (1 /. ((3 * n) ^ (2 : ℕ)))) else 1)))
  : (Real.sin (Real.pi /. 3)) = ((Real.pi /. 3) * (∏' n, if (1 : ℕ) ≤ n then ((((3 * n) - 1) * ((3 * n) + 1)) /. ((3 * n) ^ (2 : ℕ))) else 1)) := by
  sorry

theorem proof_gap_exercise_3060_4
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((Real.sin x) = (x * (∏' n, if (1 : ℕ) ≤ n then (1 - ((x ^ (2 : ℕ)) /. ((n ^ (2 : ℕ)) * (Real.pi ^ (2 : ℕ))))) else 1))))))
  (h2 : (Real.sin (Real.pi /. 3)) = ((Real.pi /. 3) * (∏' n, if (1 : ℕ) ≤ n then (1 - (1 /. ((3 * n) ^ (2 : ℕ)))) else 1)))
  (h3 : (Real.sin (Real.pi /. 3)) = ((Real.pi /. 3) * (∏' n, if (1 : ℕ) ≤ n then ((((3 * n) - 1) * ((3 * n) + 1)) /. ((3 * n) ^ (2 : ℕ))) else 1)))
  : (∏' n, if (1 : ℕ) ≤ n then (((3 * n) /. ((3 * n) - 1)) * ((3 * n) /. ((3 * n) + 1))) else 1) = ((Real.pi /. 3) /. (Real.sin (Real.pi /. 3))) := by
  sorry

theorem proof_gap_exercise_3060_5
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((Real.sin x) = (x * (∏' n, if (1 : ℕ) ≤ n then (1 - ((x ^ (2 : ℕ)) /. ((n ^ (2 : ℕ)) * (Real.pi ^ (2 : ℕ))))) else 1))))))
  (h2 : (Real.sin (Real.pi /. 3)) = ((Real.pi /. 3) * (∏' n, if (1 : ℕ) ≤ n then (1 - (1 /. ((3 * n) ^ (2 : ℕ)))) else 1)))
  (h3 : (Real.sin (Real.pi /. 3)) = ((Real.pi /. 3) * (∏' n, if (1 : ℕ) ≤ n then ((((3 * n) - 1) * ((3 * n) + 1)) /. ((3 * n) ^ (2 : ℕ))) else 1)))
  (h4 : (∏' n, if (1 : ℕ) ≤ n then (((3 * n) /. ((3 * n) - 1)) * ((3 * n) /. ((3 * n) + 1))) else 1) = ((Real.pi /. 3) /. (Real.sin (Real.pi /. 3))))
  : ((Real.pi /. 3) /. (Real.sin (Real.pi /. 3))) = ((2 * Real.pi) /. (3 * (Real.rpow (3 : ℝ) (((2 : ℝ))⁻¹)))) := by
  sorry

theorem proof_gap_exercise_3060_6
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((Real.sin x) = (x * (∏' n, if (1 : ℕ) ≤ n then (1 - ((x ^ (2 : ℕ)) /. ((n ^ (2 : ℕ)) * (Real.pi ^ (2 : ℕ))))) else 1))))))
  (h2 : (Real.sin (Real.pi /. 3)) = ((Real.pi /. 3) * (∏' n, if (1 : ℕ) ≤ n then (1 - (1 /. ((3 * n) ^ (2 : ℕ)))) else 1)))
  (h3 : (Real.sin (Real.pi /. 3)) = ((Real.pi /. 3) * (∏' n, if (1 : ℕ) ≤ n then ((((3 * n) - 1) * ((3 * n) + 1)) /. ((3 * n) ^ (2 : ℕ))) else 1)))
  (h4 : (∏' n, if (1 : ℕ) ≤ n then (((3 * n) /. ((3 * n) - 1)) * ((3 * n) /. ((3 * n) + 1))) else 1) = ((Real.pi /. 3) /. (Real.sin (Real.pi /. 3))))
  (h5 : ((Real.pi /. 3) /. (Real.sin (Real.pi /. 3))) = ((2 * Real.pi) /. (3 * (Real.rpow (3 : ℝ) (((2 : ℝ))⁻¹)))))
  : (∏' n, if (1 : ℕ) ≤ n then (((3 * n) /. ((3 * n) - 1)) * ((3 * n) /. ((3 * n) + 1))) else 1) = ((2 * Real.pi) /. (3 * (Real.rpow (3 : ℝ) (((2 : ℝ))⁻¹)))) := by
  sorry

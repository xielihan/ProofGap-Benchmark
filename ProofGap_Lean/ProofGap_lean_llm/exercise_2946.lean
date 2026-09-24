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

-- exercise: exercise_2946

theorem proof_gap_exercise_2946_1
  (f : (ℝ -> ℝ))
  (A : (ℕ -> ℝ))
  (B : (ℕ -> ℝ))
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (∀ z : ℤ, (z : ℝ) ≠ a))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-Real.pi) < x)) ∧ (x < Real.pi)) → ((f x) = (Real.sin (a * x))))))
  : Function.Odd f := by
  sorry

theorem proof_gap_exercise_2946_2
  (f : (ℝ -> ℝ))
  (A : (ℕ -> ℝ))
  (B : (ℕ -> ℝ))
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (∀ z : ℤ, (z : ℝ) ≠ a))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-Real.pi) < x)) ∧ (x < Real.pi)) → ((f x) = (Real.sin (a * x))))))
  (h3 : Function.Odd f)
  : (A (0 : ℕ)) = 0 := by
  sorry

theorem proof_gap_exercise_2946_3
  (f : (ℝ -> ℝ))
  (A : (ℕ -> ℝ))
  (B : (ℕ -> ℝ))
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (∀ z : ℤ, (z : ℝ) ≠ a))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-Real.pi) < x)) ∧ (x < Real.pi)) → ((f x) = (Real.sin (a * x))))))
  (h3 : Function.Odd f)
  (h4 : (A (0 : ℕ)) = 0)
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((A n) = 0))) := by
  sorry

theorem proof_gap_exercise_2946_4
  (f : (ℝ -> ℝ))
  (A : (ℕ -> ℝ))
  (B : (ℕ -> ℝ))
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (∀ z : ℤ, (z : ℝ) ≠ a))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-Real.pi) < x)) ∧ (x < Real.pi)) → ((f x) = (Real.sin (a * x))))))
  (h3 : Function.Odd f)
  (h4 : (A (0 : ℕ)) = 0)
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((A n) = 0))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((((B n) = ((2 /. Real.pi) * (∫ x in (0 : ℝ)..Real.pi, (((Real.sin (a * x)) * (Real.sin (n * x))) * (1 : ℝ))))) ∧ (((2 /. Real.pi) * (∫ x in (0 : ℝ)..Real.pi, (((Real.sin (a * x)) * (Real.sin (n * x))) * (1 : ℝ)))) = ((1 /. Real.pi) * (∫ x in (0 : ℝ)..Real.pi, (((Real.cos (((n : ℝ) - a) * x)) - (Real.cos (((n : ℝ) + a) * x))) * (1 : ℝ)))))) ∧ (((1 /. Real.pi) * (∫ x in (0 : ℝ)..Real.pi, (((Real.cos (((n : ℝ) - a) * x)) - (Real.cos (((n : ℝ) + a) * x))) * (1 : ℝ)))) = (((2 * (Real.sin (a * Real.pi))) /. Real.pi) * ((((-1 : ℝ) ^ (n + 1)) * (n : ℝ)) /. (((n : ℝ) ^ (2 : ℕ)) - (a ^ (2 : ℕ))))))))) := by
  sorry

theorem proof_gap_exercise_2946_5
  (f : (ℝ -> ℝ))
  (A : (ℕ -> ℝ))
  (B : (ℕ -> ℝ))
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (∀ z : ℤ, (z : ℝ) ≠ a))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-Real.pi) < x)) ∧ (x < Real.pi)) → ((f x) = (Real.sin (a * x))))))
  (h3 : Function.Odd f)
  (h4 : (A (0 : ℕ)) = 0)
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((A n) = 0))))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((((B n) = ((2 /. Real.pi) * (∫ x in (0 : ℝ)..Real.pi, (((Real.sin (a * x)) * (Real.sin (n * x))) * (1 : ℝ))))) ∧ (((2 /. Real.pi) * (∫ x in (0 : ℝ)..Real.pi, (((Real.sin (a * x)) * (Real.sin (n * x))) * (1 : ℝ)))) = ((1 /. Real.pi) * (∫ x in (0 : ℝ)..Real.pi, (((Real.cos (((n : ℝ) - a) * x)) - (Real.cos (((n : ℝ) + a) * x))) * (1 : ℝ)))))) ∧ (((1 /. Real.pi) * (∫ x in (0 : ℝ)..Real.pi, (((Real.cos (((n : ℝ) - a) * x)) - (Real.cos (((n : ℝ) + a) * x))) * (1 : ℝ)))) = (((2 * (Real.sin (a * Real.pi))) /. Real.pi) * ((((-1 : ℝ) ^ (n + 1)) * (n : ℝ)) /. (((n : ℝ) ^ (2 : ℕ)) - (a ^ (2 : ℕ))))))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-Real.pi) < x)) ∧ (x < Real.pi)) → ((f x) = (((2 * (Real.sin (a * Real.pi))) /. Real.pi) * (∑' n, if (1 : ℕ) ≤ n then (((((-1 : ℝ) ^ (n + 1)) * (n : ℝ)) * (Real.sin (n * x))) /. (((n : ℝ) ^ (2 : ℕ)) - (a ^ (2 : ℕ)))) else 0))))) := by
  sorry

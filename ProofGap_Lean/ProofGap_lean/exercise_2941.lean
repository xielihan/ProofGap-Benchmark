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

-- exercise: exercise_2941

theorem proof_gap_exercise_2941_1
  (f : (ℝ -> ℝ))
  (a : (ℕ -> ℝ))
  (b : (ℕ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 (2 * Real.pi)))) → ((f x) = ((Real.pi - x) /. 2)))))
  : (a (0 : ℕ)) = ((1 /. Real.pi) * (∫ x in (0 : ℝ)..(2 * Real.pi), (((Real.pi - x) /. (2 : ℝ)) * (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_2941_2
  (f : (ℝ -> ℝ))
  (a : (ℕ -> ℝ))
  (b : (ℕ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 (2 * Real.pi)))) → ((f x) = ((Real.pi - x) /. 2)))))
  (h2 : (a (0 : ℕ)) = ((1 /. Real.pi) * (∫ x in (0 : ℝ)..(2 * Real.pi), (((Real.pi - x) /. (2 : ℝ)) * (1 : ℝ)))))
  : (a (0 : ℕ)) = 0 := by
  sorry

theorem proof_gap_exercise_2941_3
  (f : (ℝ -> ℝ))
  (a : (ℕ -> ℝ))
  (b : (ℕ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 (2 * Real.pi)))) → ((f x) = ((Real.pi - x) /. 2)))))
  (h2 : (a (0 : ℕ)) = ((1 /. Real.pi) * (∫ x in (0 : ℝ)..(2 * Real.pi), (((Real.pi - x) /. (2 : ℝ)) * (1 : ℝ)))))
  (h3 : (a (0 : ℕ)) = 0)
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((1 /. Real.pi) * (∫ x in (0 : ℝ)..(2 * Real.pi), ((((Real.pi - x) /. (2 : ℝ)) * (Real.cos (n * x))) * (1 : ℝ))))))) := by
  sorry

theorem proof_gap_exercise_2941_4
  (f : (ℝ -> ℝ))
  (a : (ℕ -> ℝ))
  (b : (ℕ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 (2 * Real.pi)))) → ((f x) = ((Real.pi - x) /. 2)))))
  (h2 : (a (0 : ℕ)) = ((1 /. Real.pi) * (∫ x in (0 : ℝ)..(2 * Real.pi), (((Real.pi - x) /. (2 : ℝ)) * (1 : ℝ)))))
  (h3 : (a (0 : ℕ)) = 0)
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((1 /. Real.pi) * (∫ x in (0 : ℝ)..(2 * Real.pi), ((((Real.pi - x) /. (2 : ℝ)) * (Real.cos (n * x))) * (1 : ℝ))))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = 0))) := by
  sorry

theorem proof_gap_exercise_2941_5
  (f : (ℝ -> ℝ))
  (a : (ℕ -> ℝ))
  (b : (ℕ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 (2 * Real.pi)))) → ((f x) = ((Real.pi - x) /. 2)))))
  (h2 : (a (0 : ℕ)) = ((1 /. Real.pi) * (∫ x in (0 : ℝ)..(2 * Real.pi), (((Real.pi - x) /. (2 : ℝ)) * (1 : ℝ)))))
  (h3 : (a (0 : ℕ)) = 0)
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((1 /. Real.pi) * (∫ x in (0 : ℝ)..(2 * Real.pi), ((((Real.pi - x) /. (2 : ℝ)) * (Real.cos (n * x))) * (1 : ℝ))))))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = 0))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) = ((1 /. Real.pi) * (∫ x in (0 : ℝ)..(2 * Real.pi), ((((Real.pi - x) /. (2 : ℝ)) * (Real.sin (n * x))) * (1 : ℝ))))))) := by
  sorry

theorem proof_gap_exercise_2941_6
  (f : (ℝ -> ℝ))
  (a : (ℕ -> ℝ))
  (b : (ℕ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 (2 * Real.pi)))) → ((f x) = ((Real.pi - x) /. 2)))))
  (h2 : (a (0 : ℕ)) = ((1 /. Real.pi) * (∫ x in (0 : ℝ)..(2 * Real.pi), (((Real.pi - x) /. (2 : ℝ)) * (1 : ℝ)))))
  (h3 : (a (0 : ℕ)) = 0)
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((1 /. Real.pi) * (∫ x in (0 : ℝ)..(2 * Real.pi), ((((Real.pi - x) /. (2 : ℝ)) * (Real.cos (n * x))) * (1 : ℝ))))))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = 0))))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) = ((1 /. Real.pi) * (∫ x in (0 : ℝ)..(2 * Real.pi), ((((Real.pi - x) /. (2 : ℝ)) * (Real.sin (n * x))) * (1 : ℝ))))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) = (1 /. n)))) := by
  sorry

theorem proof_gap_exercise_2941_7
  (f : (ℝ -> ℝ))
  (a : (ℕ -> ℝ))
  (b : (ℕ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 (2 * Real.pi)))) → ((f x) = ((Real.pi - x) /. 2)))))
  (h2 : (a (0 : ℕ)) = ((1 /. Real.pi) * (∫ x in (0 : ℝ)..(2 * Real.pi), (((Real.pi - x) /. (2 : ℝ)) * (1 : ℝ)))))
  (h3 : (a (0 : ℕ)) = 0)
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((1 /. Real.pi) * (∫ x in (0 : ℝ)..(2 * Real.pi), ((((Real.pi - x) /. (2 : ℝ)) * (Real.cos (n * x))) * (1 : ℝ))))))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = 0))))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) = ((1 /. Real.pi) * (∫ x in (0 : ℝ)..(2 * Real.pi), ((((Real.pi - x) /. (2 : ℝ)) * (Real.sin (n * x))) * (1 : ℝ))))))))
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) = (1 /. n)))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 (2 * Real.pi)))) → (((Real.pi - x) /. 2) = (∑' n, if (1 : ℕ) ≤ n then ((Real.sin (n * x)) /. n) else 0)))) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 (2 * Real.pi)))) → ((f x) = (((a (0 : ℕ)) /. 2) + (∑' n, if (1 : ℕ) ≤ n then (((a n) * (Real.cos (n * x))) + ((b n) * (Real.sin (n * x)))) else 0))))) := by
  sorry

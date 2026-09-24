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

-- exercise: exercise_1147

theorem proof_gap_exercise_1147_1
  (y : (ℝ -> ℝ))
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((y x) ^ (2 : ℕ)) = ((2 * p) * x)))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (p /. (y x))))) := by
  sorry

theorem proof_gap_exercise_1147_2
  (y : (ℝ -> ℝ))
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((y x) ^ (2 : ℕ)) = ((2 * p) * x)))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (p /. (y x))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => y t) x) = ((-(p /. ((y x) ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => y t) x))))) := by
  sorry

theorem proof_gap_exercise_1147_3
  (y : (ℝ -> ℝ))
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((y x) ^ (2 : ℕ)) = ((2 * p) * x)))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (p /. (y x))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => y t) x) = ((-(p /. ((y x) ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => y t) x))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((-(p /. ((y x) ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => y t) x)) = (-((p ^ (2 : ℕ)) /. ((y x) ^ (3 : ℕ))))))) := by
  sorry

theorem proof_gap_exercise_1147_4
  (y : (ℝ -> ℝ))
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((y x) ^ (2 : ℕ)) = ((2 * p) * x)))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (p /. (y x))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => y t) x) = ((-(p /. ((y x) ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => y t) x))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((-(p /. ((y x) ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => y t) x)) = (-((p ^ (2 : ℕ)) /. ((y x) ^ (3 : ℕ))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => y t) x) = (-((p ^ (2 : ℕ)) /. ((y x) ^ (3 : ℕ))))))) := by
  sorry

theorem proof_gap_exercise_1147_5
  (y : (ℝ -> ℝ))
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((y x) ^ (2 : ℕ)) = ((2 * p) * x)))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (p /. (y x))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => y t) x) = ((-(p /. ((y x) ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => y t) x))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((-(p /. ((y x) ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => y t) x)) = (-((p ^ (2 : ℕ)) /. ((y x) ^ (3 : ℕ))))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => y t) x) = (-((p ^ (2 : ℕ)) /. ((y x) ^ (3 : ℕ))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 3 (fun t => y t) x) = (((3 * (p ^ (2 : ℕ))) /. ((y x) ^ (4 : ℕ))) * (iteratedDeriv 1 (fun t => y t) x))))) := by
  sorry

theorem proof_gap_exercise_1147_6
  (y : (ℝ -> ℝ))
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((y x) ^ (2 : ℕ)) = ((2 * p) * x)))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (p /. (y x))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => y t) x) = ((-(p /. ((y x) ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => y t) x))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((-(p /. ((y x) ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => y t) x)) = (-((p ^ (2 : ℕ)) /. ((y x) ^ (3 : ℕ))))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => y t) x) = (-((p ^ (2 : ℕ)) /. ((y x) ^ (3 : ℕ))))))))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 3 (fun t => y t) x) = (((3 * (p ^ (2 : ℕ))) /. ((y x) ^ (4 : ℕ))) * (iteratedDeriv 1 (fun t => y t) x))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((3 * (p ^ (2 : ℕ))) /. ((y x) ^ (4 : ℕ))) * (iteratedDeriv 1 (fun t => y t) x)) = ((3 * (p ^ (3 : ℕ))) /. ((y x) ^ (5 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_1147_7
  (y : (ℝ -> ℝ))
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((y x) ^ (2 : ℕ)) = ((2 * p) * x)))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (p /. (y x))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => y t) x) = ((-(p /. ((y x) ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => y t) x))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((-(p /. ((y x) ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => y t) x)) = (-((p ^ (2 : ℕ)) /. ((y x) ^ (3 : ℕ))))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => y t) x) = (-((p ^ (2 : ℕ)) /. ((y x) ^ (3 : ℕ))))))))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 3 (fun t => y t) x) = (((3 * (p ^ (2 : ℕ))) /. ((y x) ^ (4 : ℕ))) * (iteratedDeriv 1 (fun t => y t) x))))))
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((3 * (p ^ (2 : ℕ))) /. ((y x) ^ (4 : ℕ))) * (iteratedDeriv 1 (fun t => y t) x)) = ((3 * (p ^ (3 : ℕ))) /. ((y x) ^ (5 : ℕ)))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 3 (fun t => y t) x) = ((3 * (p ^ (3 : ℕ))) /. ((y x) ^ (5 : ℕ)))))) := by
  sorry

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

-- exercise: exercise_2468

theorem proof_gap_exercise_2468_1
  (P : (ℝ -> ℝ))
  (a : ℝ)
  (V : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : V ∈ (Set.univ : Set ℝ))
  (h3 : (forall (z : ℝ), ((((z ∈ (Set.univ : Set ℝ)) ∧ (0 < z)) ∧ (z < a)) → (V = (∫ z_1 in (0 : ℝ)..a, ((P z_1) * (1 : ℝ)))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → (forall (z : ℝ), ((((z ∈ (Set.univ : Set ℝ)) ∧ (0 < z)) ∧ (z < a)) → ((((x ^ (2 : ℕ)) /. (a ^ (2 : ℕ))) + ((y ^ (2 : ℕ)) /. (z ^ (2 : ℕ)))) = 1))))))) := by
  sorry

theorem proof_gap_exercise_2468_2
  (P : (ℝ -> ℝ))
  (a : ℝ)
  (V : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : V ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → (forall (z : ℝ), ((((z ∈ (Set.univ : Set ℝ)) ∧ (0 < z)) ∧ (z < a)) → ((((x ^ (2 : ℕ)) /. (a ^ (2 : ℕ))) + ((y ^ (2 : ℕ)) /. (z ^ (2 : ℕ)))) = 1))))))))
  (h4 : (forall (z : ℝ), ((((z ∈ (Set.univ : Set ℝ)) ∧ (0 < z)) ∧ (z < a)) → (V = (∫ z_1 in (0 : ℝ)..a, ((P z_1) * (1 : ℝ)))))))
  : (forall (z : ℝ), ((((z ∈ (Set.univ : Set ℝ)) ∧ (0 < z)) ∧ (z < a)) → ((P z) = ((Real.pi * a) * z)))) := by
  sorry

theorem proof_gap_exercise_2468_3
  (P : (ℝ -> ℝ))
  (a : ℝ)
  (V : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : V ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → (forall (z : ℝ), ((((z ∈ (Set.univ : Set ℝ)) ∧ (0 < z)) ∧ (z < a)) → ((((x ^ (2 : ℕ)) /. (a ^ (2 : ℕ))) + ((y ^ (2 : ℕ)) /. (z ^ (2 : ℕ)))) = 1))))))))
  (h4 : (forall (z : ℝ), ((((z ∈ (Set.univ : Set ℝ)) ∧ (0 < z)) ∧ (z < a)) → ((P z) = ((Real.pi * a) * z)))))
  (h5 : (forall (z : ℝ), ((((z ∈ (Set.univ : Set ℝ)) ∧ (0 < z)) ∧ (z < a)) → (V = ((Real.pi * a) * (∫ z_1 in (0 : ℝ)..a, (z_1 * (1 : ℝ))))))))
  : (forall (z : ℝ), ((((z ∈ (Set.univ : Set ℝ)) ∧ (0 < z)) ∧ (z < a)) → (V = (∫ z_1 in (0 : ℝ)..a, ((P z_1) * (1 : ℝ)))))) := by
  sorry

theorem proof_gap_exercise_2468_4
  (P : (ℝ -> ℝ))
  (a : ℝ)
  (V : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : V ∈ (Set.univ : Set ℝ))
  (h3 : (exists (x : (ℝ -> ℝ)) (y : (ℝ -> ℝ)), (True ∧ (forall (z : ℝ), ((((z ∈ (Set.univ : Set ℝ)) ∧ (0 < z)) ∧ (z < a)) → (((((x z) ^ (2 : ℕ)) /. (a ^ (2 : ℕ))) + (((y z) ^ (2 : ℕ)) /. (z ^ (2 : ℕ)))) = 1))))))
  (h4 : (forall (z : ℝ), ((((z ∈ (Set.univ : Set ℝ)) ∧ (0 < z)) ∧ (z < a)) → ((P z) = ((Real.pi * a) * z)))))
  (h5 : (forall (z : ℝ), ((((z ∈ (Set.univ : Set ℝ)) ∧ (0 < z)) ∧ (z < a)) → (V = (∫ z_1 in (0 : ℝ)..a, ((P z_1) * (1 : ℝ)))))))
  : (forall (z : ℝ), ((((z ∈ (Set.univ : Set ℝ)) ∧ (0 < z)) ∧ (z < a)) → (V = ((Real.pi * a) * (∫ z_1 in (0 : ℝ)..a, (z_1 * (1 : ℝ))))))) := by
  sorry

theorem proof_gap_exercise_2468_5
  (P : (ℝ -> ℝ))
  (a : ℝ)
  (V : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : V ∈ (Set.univ : Set ℝ))
  (h3 : (exists (x : (ℝ -> ℝ)) (y : (ℝ -> ℝ)), (True ∧ (forall (z : ℝ), ((((z ∈ (Set.univ : Set ℝ)) ∧ (0 < z)) ∧ (z < a)) → (((((x z) ^ (2 : ℕ)) /. (a ^ (2 : ℕ))) + (((y z) ^ (2 : ℕ)) /. (z ^ (2 : ℕ)))) = 1))))))
  (h4 : (forall (z : ℝ), ((((z ∈ (Set.univ : Set ℝ)) ∧ (0 < z)) ∧ (z < a)) → ((P z) = ((Real.pi * a) * z)))))
  (h5 : (forall (z : ℝ), ((((z ∈ (Set.univ : Set ℝ)) ∧ (0 < z)) ∧ (z < a)) → (V = (∫ z_1 in (0 : ℝ)..a, ((P z_1) * (1 : ℝ)))))))
  (h6 : (forall (z : ℝ), ((((z ∈ (Set.univ : Set ℝ)) ∧ (0 < z)) ∧ (z < a)) → (V = ((Real.pi * a) * (∫ z_1 in (0 : ℝ)..a, (z_1 * (1 : ℝ))))))))
  : V = ((Real.pi * (a ^ (3 : ℕ))) /. 2) := by
  sorry

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

-- exercise: exercise_2978

theorem proof_gap_exercise_2978_1
  (f : (ℝ -> ℝ))
  (a : (ℕ -> ℝ))
  (b : (ℕ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (x + Real.pi)) = (-(f x))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((a n) = ((1 /. Real.pi) * (∫ x_1 in (-Real.pi)..Real.pi, (((f x_1) * (Real.cos (n * x_1))) * (1 : ℝ))))))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) = ((1 /. Real.pi) * (∫ x_1 in (-Real.pi)..Real.pi, (((f x_1) * (Real.sin (n * x_1))) * (1 : ℝ))))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((a n) = ((1 /. Real.pi) * ((-(∫ x_1 in (-Real.pi)..(0 : ℝ), (((f (Real.pi + x_1)) * (Real.cos (n * x_1))) * (1 : ℝ)))) + (∫ x_1 in (0 : ℝ)..Real.pi, (((f x_1) * (Real.cos (n * x_1))) * (1 : ℝ)))))))))) := by
  sorry

theorem proof_gap_exercise_2978_2
  (f : (ℝ -> ℝ))
  (a : (ℕ -> ℝ))
  (b : (ℕ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (x + Real.pi)) = (-(f x))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((a n) = ((1 /. Real.pi) * (∫ x_1 in (-Real.pi)..Real.pi, (((f x_1) * (Real.cos (n * x_1))) * (1 : ℝ))))))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) = ((1 /. Real.pi) * (∫ x_1 in (-Real.pi)..Real.pi, (((f x_1) * (Real.sin (n * x_1))) * (1 : ℝ))))))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((a n) = ((1 /. Real.pi) * ((-(∫ x_1 in (-Real.pi)..(0 : ℝ), (((f (Real.pi + x_1)) * (Real.cos (n * x_1))) * (1 : ℝ)))) + (∫ x_1 in (0 : ℝ)..Real.pi, (((f x_1) * (Real.cos (n * x_1))) * (1 : ℝ)))))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((a n) = ((1 /. Real.pi) * (∫ x_1 in (0 : ℝ)..Real.pi, ((((((-(1 : ℝ)) ^ (n + 1)) + (1 : ℝ)) * (f x_1)) * (Real.cos (n * x_1))) * (1 : ℝ))))))))) := by
  sorry

theorem proof_gap_exercise_2978_3
  (f : (ℝ -> ℝ))
  (a : (ℕ -> ℝ))
  (b : (ℕ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (x + Real.pi)) = (-(f x))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((a n) = ((1 /. Real.pi) * (∫ x_1 in (-Real.pi)..Real.pi, (((f x_1) * (Real.cos (n * x_1))) * (1 : ℝ))))))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) = ((1 /. Real.pi) * (∫ x_1 in (-Real.pi)..Real.pi, (((f x_1) * (Real.sin (n * x_1))) * (1 : ℝ))))))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((a n) = ((1 /. Real.pi) * ((-(∫ x_1 in (-Real.pi)..(0 : ℝ), (((f (Real.pi + x_1)) * (Real.cos (n * x_1))) * (1 : ℝ)))) + (∫ x_1 in (0 : ℝ)..Real.pi, (((f x_1) * (Real.cos (n * x_1))) * (1 : ℝ)))))))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((a n) = ((1 /. Real.pi) * (∫ x_1 in (0 : ℝ)..Real.pi, ((((((-(1 : ℝ)) ^ (n + 1)) + (1 : ℝ)) * (f x_1)) * (Real.cos (n * x_1))) * (1 : ℝ))))))))))
  : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((a (2 * n)) = 0))) := by
  sorry

theorem proof_gap_exercise_2978_4
  (f : (ℝ -> ℝ))
  (a : (ℕ -> ℝ))
  (b : (ℕ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (x + Real.pi)) = (-(f x))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((a n) = ((1 /. Real.pi) * (∫ x_1 in (-Real.pi)..Real.pi, (((f x_1) * (Real.cos (n * x_1))) * (1 : ℝ))))))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) = ((1 /. Real.pi) * (∫ x_1 in (-Real.pi)..Real.pi, (((f x_1) * (Real.sin (n * x_1))) * (1 : ℝ))))))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((a n) = ((1 /. Real.pi) * ((-(∫ x_1 in (-Real.pi)..(0 : ℝ), (((f (Real.pi + x_1)) * (Real.cos (n * x_1))) * (1 : ℝ)))) + (∫ x_1 in (0 : ℝ)..Real.pi, (((f x_1) * (Real.cos (n * x_1))) * (1 : ℝ)))))))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((a n) = ((1 /. Real.pi) * (∫ x_1 in (0 : ℝ)..Real.pi, ((((((-(1 : ℝ)) ^ (n + 1)) + (1 : ℝ)) * (f x_1)) * (Real.cos (n * x_1))) * (1 : ℝ))))))))))
  (h6 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((a (2 * n)) = 0))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b (2 * n)) = 0))) := by
  sorry

theorem proof_gap_exercise_2978_5
  (f : (ℝ -> ℝ))
  (a : (ℕ -> ℝ))
  (b : (ℕ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (x + Real.pi)) = (-(f x))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((a n) = ((1 /. Real.pi) * (∫ x_1 in (-Real.pi)..Real.pi, (((f x_1) * (Real.cos (n * x_1))) * (1 : ℝ))))))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) = ((1 /. Real.pi) * (∫ x_1 in (-Real.pi)..Real.pi, (((f x_1) * (Real.sin (n * x_1))) * (1 : ℝ))))))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((a n) = ((1 /. Real.pi) * ((-(∫ x_1 in (-Real.pi)..(0 : ℝ), (((f (Real.pi + x_1)) * (Real.cos (n * x_1))) * (1 : ℝ)))) + (∫ x_1 in (0 : ℝ)..Real.pi, (((f x_1) * (Real.cos (n * x_1))) * (1 : ℝ)))))))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((a n) = ((1 /. Real.pi) * (∫ x_1 in (0 : ℝ)..Real.pi, ((((((-(1 : ℝ)) ^ (n + 1)) + (1 : ℝ)) * (f x_1)) * (Real.cos (n * x_1))) * (1 : ℝ))))))))))
  (h6 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((a (2 * n)) = 0))))
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b (2 * n)) = 0))))
  : ((forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((a (2 * n)) = 0))) ∧ (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b (2 * n)) = 0)))) → ((forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((a (2 * n)) = 0))) ∧ (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b (2 * n)) = 0)))) := by
  sorry

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

-- exercise: exercise_3617

theorem proof_gap_exercise_3617_1
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (Not (exists (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) ∧ (x = (k * Real.pi)))))) → ((y x) = (Real.arctan (1 /. (Real.sin x)))))))
  : (forall (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) → (Not (ContinuousAt y (k * Real.pi))))) := by
  sorry

theorem proof_gap_exercise_3617_2
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (Not (exists (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) ∧ (x = (k * Real.pi)))))) → ((y x) = (Real.arctan (1 /. (Real.sin x)))))))
  (h3 : (forall (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) → (Not (ContinuousAt y (k * Real.pi))))))
  : (forall (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) → (Tendsto (fun x : ℝ => (y x)) (𝓝[<] (k * Real.pi)) (𝓝 (((-(1 : ℝ)) ^ k) * (Real.pi /. 2)))))) := by
  sorry

theorem proof_gap_exercise_3617_3
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (Not (exists (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) ∧ (x = (k * Real.pi)))))) → ((y x) = (Real.arctan (1 /. (Real.sin x)))))))
  (h3 : (forall (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) → (Not (ContinuousAt y (k * Real.pi))))))
  (h4 : (forall (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) → (Tendsto (fun x : ℝ => (y x)) (𝓝[<] (k * Real.pi)) (𝓝 (((-(1 : ℝ)) ^ k) * (Real.pi /. 2)))))))
  : (forall (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) → (Tendsto (fun x : ℝ => (y x)) (𝓝[>] (k * Real.pi)) (𝓝 (((-(1 : ℝ)) ^ (k + 1)) * (Real.pi /. 2)))))) := by
  sorry

theorem proof_gap_exercise_3617_4
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (Not (exists (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) ∧ (x = (k * Real.pi)))))) → ((y x) = (Real.arctan (1 /. (Real.sin x)))))))
  (h3 : (forall (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) → (Not (ContinuousAt y (k * Real.pi))))))
  (h4 : (forall (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) → (Tendsto (fun x : ℝ => (y x)) (𝓝[<] (k * Real.pi)) (𝓝 (((-(1 : ℝ)) ^ k) * (Real.pi /. 2)))))))
  (h5 : (forall (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) → (Tendsto (fun x : ℝ => (y x)) (𝓝[>] (k * Real.pi)) (𝓝 (((-(1 : ℝ)) ^ (k + 1)) * (Real.pi /. 2)))))))
  : (a ∈ ({Mult_k_uCF_u80 | (k ∈ (Set.univ : Set ℤ))})) ↔ (Not (ContinuousAt y a)) := by
  sorry

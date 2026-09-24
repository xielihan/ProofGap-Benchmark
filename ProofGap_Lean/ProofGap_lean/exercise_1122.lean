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

-- exercise: exercise_1122

theorem proof_gap_exercise_1122_1
  (y : (ℝ -> ℝ))
  (u : (ℝ -> ℝ))
  (v : (ℝ -> ℝ))
  (I : (Set ℝ))
  (h1 : I ⊆ (Set.univ : Set ℝ))
  (h2 : ContDiffOn ℝ (2 : ℕ∞) u I)
  (h3 : ContDiffOn ℝ (2 : ℕ∞) v I)
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → (((v x) ≠ 0) ∧ (((u x) /. (v x)) > 0)))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → ((y x) = (Real.log ((u x) /. (v x)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → ((iteratedDeriv 1 (fun t => y t) x) = (((iteratedDeriv 1 (fun t => u t) x) /. (u x)) - ((iteratedDeriv 1 (fun t => v t) x) /. (v x)))))) := by
  sorry

theorem proof_gap_exercise_1122_2
  (y : (ℝ -> ℝ))
  (u : (ℝ -> ℝ))
  (v : (ℝ -> ℝ))
  (I : (Set ℝ))
  (h1 : I ⊆ (Set.univ : Set ℝ))
  (h2 : ContDiffOn ℝ (2 : ℕ∞) u I)
  (h3 : ContDiffOn ℝ (2 : ℕ∞) v I)
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → (((v x) ≠ 0) ∧ (((u x) /. (v x)) > 0)))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → ((y x) = (Real.log ((u x) /. (v x)))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → ((iteratedDeriv 1 (fun t => y t) x) = (((iteratedDeriv 1 (fun t => u t) x) /. (u x)) - ((iteratedDeriv 1 (fun t => v t) x) /. (v x)))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) ∧ (((u x) * (v x)) > 0)) → ((iteratedDeriv 2 (fun t => y t) x) = (((((u x) * (iteratedDeriv 2 (fun t => u t) x)) - ((iteratedDeriv 1 (fun t => u t) x) ^ (2 : ℕ))) /. ((u x) ^ (2 : ℕ))) - ((((v x) * (iteratedDeriv 2 (fun t => v t) x)) - ((iteratedDeriv 1 (fun t => v t) x) ^ (2 : ℕ))) /. ((v x) ^ (2 : ℕ))))))) := by
  sorry

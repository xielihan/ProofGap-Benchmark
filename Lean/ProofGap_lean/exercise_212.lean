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

-- exercise: exercise_212

theorem proof_gap_exercise_212_1
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| ≥ 2)) → ((f (x + (1 /. x))) = ((x ^ (2 : ℕ)) + (1 /. (x ^ (2 : ℕ))))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| ≥ 2)) → ((f (x + (1 /. x))) = (((x + (1 /. x)) ^ (2 : ℕ)) - 2)))) := by
  sorry

theorem proof_gap_exercise_212_2
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| ≥ 2)) → ((f (x + (1 /. x))) = ((x ^ (2 : ℕ)) + (1 /. (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| ≥ 2)) → ((f (x + (1 /. x))) = (((x + (1 /. x)) ^ (2 : ℕ)) - 2)))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x + (1 /. x)))) → ((t ^ (2 : ℕ)) = (((x ^ (2 : ℕ)) + 2) + (1 /. (x ^ (2 : ℕ))))))))) := by
  sorry

theorem proof_gap_exercise_212_3
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| ≥ 2)) → ((f (x + (1 /. x))) = ((x ^ (2 : ℕ)) + (1 /. (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| ≥ 2)) → ((f (x + (1 /. x))) = (((x + (1 /. x)) ^ (2 : ℕ)) - 2)))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x + (1 /. x)))) → ((t ^ (2 : ℕ)) = (((x ^ (2 : ℕ)) + 2) + (1 /. (x ^ (2 : ℕ))))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x + (1 /. x)))) ∧ (|(x)| ≥ 2)) → (|(t)| ≥ (5 /. 2)))))) := by
  sorry

theorem proof_gap_exercise_212_4
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| ≥ 2)) → ((f (x + (1 /. x))) = ((x ^ (2 : ℕ)) + (1 /. (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| ≥ 2)) → ((f (x + (1 /. x))) = (((x + (1 /. x)) ^ (2 : ℕ)) - 2)))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x + (1 /. x)))) → ((t ^ (2 : ℕ)) = (((x ^ (2 : ℕ)) + 2) + (1 /. (x ^ (2 : ℕ))))))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x + (1 /. x)))) ∧ (|(x)| ≥ 2)) → (|(t)| ≥ (5 /. 2)))))))
  : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (|(t)| ≥ (5 /. 2))) → ((f t) = ((t ^ (2 : ℕ)) - 2)))) := by
  sorry

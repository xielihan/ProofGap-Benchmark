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

-- exercise: exercise_196

theorem proof_gap_exercise_196_1
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((a * (x ^ (2 : ℕ))) + (b * x)) + c)))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((((f (x + 3)) - (3 * (f (x + 2)))) + (3 * (f (x + 1)))) - (f x)) = ((((((a * ((x + 3) ^ (2 : ℕ))) + (b * (x + 3))) + c) - (3 * (((a * ((x + 2) ^ (2 : ℕ))) + (b * (x + 2))) + c))) + (3 * (((a * ((x + 1) ^ (2 : ℕ))) + (b * (x + 1))) + c))) - (((a * (x ^ (2 : ℕ))) + (b * x)) + c))))) := by
  sorry

theorem proof_gap_exercise_196_2
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((a * (x ^ (2 : ℕ))) + (b * x)) + c)))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((((f (x + 3)) - (3 * (f (x + 2)))) + (3 * (f (x + 1)))) - (f x)) = ((((((a * ((x + 3) ^ (2 : ℕ))) + (b * (x + 3))) + c) - (3 * (((a * ((x + 2) ^ (2 : ℕ))) + (b * (x + 2))) + c))) + (3 * (((a * ((x + 1) ^ (2 : ℕ))) + (b * (x + 1))) + c))) - (((a * (x ^ (2 : ℕ))) + (b * x)) + c))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((((f (x + 3)) - (3 * (f (x + 2)))) + (3 * (f (x + 1)))) - (f x)) = ((((((((((((((((((((a * (x ^ (2 : ℕ))) + ((6 * a) * x)) + (9 * a)) + (b * x)) + (3 * b)) + c) - ((3 * a) * (x ^ (2 : ℕ)))) - ((12 * a) * x)) - (12 * a)) - ((3 * b) * x)) - (6 * b)) - (3 * c)) + ((3 * a) * (x ^ (2 : ℕ)))) + ((6 * a) * x)) + (3 * a)) + ((3 * b) * x)) + (3 * c)) - (a * (x ^ (2 : ℕ)))) - (b * x)) - c)))) := by
  sorry

theorem proof_gap_exercise_196_3
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((a * (x ^ (2 : ℕ))) + (b * x)) + c)))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((((f (x + 3)) - (3 * (f (x + 2)))) + (3 * (f (x + 1)))) - (f x)) = ((((((a * ((x + 3) ^ (2 : ℕ))) + (b * (x + 3))) + c) - (3 * (((a * ((x + 2) ^ (2 : ℕ))) + (b * (x + 2))) + c))) + (3 * (((a * ((x + 1) ^ (2 : ℕ))) + (b * (x + 1))) + c))) - (((a * (x ^ (2 : ℕ))) + (b * x)) + c))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((((f (x + 3)) - (3 * (f (x + 2)))) + (3 * (f (x + 1)))) - (f x)) = ((((((((((((((((((((a * (x ^ (2 : ℕ))) + ((6 * a) * x)) + (9 * a)) + (b * x)) + (3 * b)) + c) - ((3 * a) * (x ^ (2 : ℕ)))) - ((12 * a) * x)) - (12 * a)) - ((3 * b) * x)) - (6 * b)) - (3 * c)) + ((3 * a) * (x ^ (2 : ℕ)))) + ((6 * a) * x)) + (3 * a)) + ((3 * b) * x)) + (3 * c)) - (a * (x ^ (2 : ℕ)))) - (b * x)) - c)))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((((f (x + 3)) - (3 * (f (x + 2)))) + (3 * (f (x + 1)))) - (f x)) = 0))) := by
  sorry

theorem proof_gap_exercise_196_4
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((a * (x ^ (2 : ℕ))) + (b * x)) + c)))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((((f (x + 3)) - (3 * (f (x + 2)))) + (3 * (f (x + 1)))) - (f x)) = ((((((a * ((x + 3) ^ (2 : ℕ))) + (b * (x + 3))) + c) - (3 * (((a * ((x + 2) ^ (2 : ℕ))) + (b * (x + 2))) + c))) + (3 * (((a * ((x + 1) ^ (2 : ℕ))) + (b * (x + 1))) + c))) - (((a * (x ^ (2 : ℕ))) + (b * x)) + c))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((((f (x + 3)) - (3 * (f (x + 2)))) + (3 * (f (x + 1)))) - (f x)) = ((((((((((((((((((((a * (x ^ (2 : ℕ))) + ((6 * a) * x)) + (9 * a)) + (b * x)) + (3 * b)) + c) - ((3 * a) * (x ^ (2 : ℕ)))) - ((12 * a) * x)) - (12 * a)) - ((3 * b) * x)) - (6 * b)) - (3 * c)) + ((3 * a) * (x ^ (2 : ℕ)))) + ((6 * a) * x)) + (3 * a)) + ((3 * b) * x)) + (3 * c)) - (a * (x ^ (2 : ℕ)))) - (b * x)) - c)))))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((((f (x + 3)) - (3 * (f (x + 2)))) + (3 * (f (x + 1)))) - (f x)) = 0))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((((f (x + 3)) - (3 * (f (x + 2)))) + (3 * (f (x + 1)))) - (f x)) = 0))) := by
  sorry

theorem proof_gap_exercise_196_5
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((a * (x ^ (2 : ℕ))) + (b * x)) + c)))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((((f (x + 3)) - (3 * (f (x + 2)))) + (3 * (f (x + 1)))) - (f x)) = ((((((a * ((x + 3) ^ (2 : ℕ))) + (b * (x + 3))) + c) - (3 * (((a * ((x + 2) ^ (2 : ℕ))) + (b * (x + 2))) + c))) + (3 * (((a * ((x + 1) ^ (2 : ℕ))) + (b * (x + 1))) + c))) - (((a * (x ^ (2 : ℕ))) + (b * x)) + c))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((((f (x + 3)) - (3 * (f (x + 2)))) + (3 * (f (x + 1)))) - (f x)) = ((((((((((((((((((((a * (x ^ (2 : ℕ))) + ((6 * a) * x)) + (9 * a)) + (b * x)) + (3 * b)) + c) - ((3 * a) * (x ^ (2 : ℕ)))) - ((12 * a) * x)) - (12 * a)) - ((3 * b) * x)) - (6 * b)) - (3 * c)) + ((3 * a) * (x ^ (2 : ℕ)))) + ((6 * a) * x)) + (3 * a)) + ((3 * b) * x)) + (3 * c)) - (a * (x ^ (2 : ℕ)))) - (b * x)) - c)))))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((((f (x + 3)) - (3 * (f (x + 2)))) + (3 * (f (x + 1)))) - (f x)) = 0))))
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((((f (x + 3)) - (3 * (f (x + 2)))) + (3 * (f (x + 1)))) - (f x)) = 0))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((((f (x + 3)) - (3 * (f (x + 2)))) + (3 * (f (x + 1)))) - (f x)) = 0))) := by
  sorry

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

-- exercise: exercise_197

theorem proof_gap_exercise_197_1
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((a * x) + b)))))
  (h4 : (f (0 : ℝ)) = (-(2 : ℝ)))
  (h5 : (f (3 : ℝ)) = 5)
  : (f (0 : ℝ)) = b := by
  sorry

theorem proof_gap_exercise_197_2
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((a * x) + b)))))
  (h4 : (f (0 : ℝ)) = (-(2 : ℝ)))
  (h5 : (f (3 : ℝ)) = 5)
  (h6 : (f (0 : ℝ)) = b)
  : b = (-(2 : ℝ)) := by
  sorry

theorem proof_gap_exercise_197_3
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((a * x) + b)))))
  (h4 : (f (0 : ℝ)) = (-(2 : ℝ)))
  (h5 : (f (3 : ℝ)) = 5)
  (h6 : (f (0 : ℝ)) = b)
  (h7 : b = (-(2 : ℝ)))
  : (f (0 : ℝ)) = (-(2 : ℝ)) := by
  sorry

theorem proof_gap_exercise_197_4
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((a * x) + b)))))
  (h4 : (f (0 : ℝ)) = (-(2 : ℝ)))
  (h5 : (f (3 : ℝ)) = 5)
  (h6 : (f (0 : ℝ)) = b)
  (h7 : b = (-(2 : ℝ)))
  (h8 : (f (0 : ℝ)) = (-(2 : ℝ)))
  : (f (3 : ℝ)) = ((3 * a) + b) := by
  sorry

theorem proof_gap_exercise_197_5
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((a * x) + b)))))
  (h4 : (f (0 : ℝ)) = (-(2 : ℝ)))
  (h5 : (f (3 : ℝ)) = 5)
  (h6 : (f (0 : ℝ)) = b)
  (h7 : b = (-(2 : ℝ)))
  (h8 : (f (0 : ℝ)) = (-(2 : ℝ)))
  (h9 : (f (3 : ℝ)) = ((3 * a) + b))
  : ((3 * a) + b) = 5 := by
  sorry

theorem proof_gap_exercise_197_6
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((a * x) + b)))))
  (h4 : (f (0 : ℝ)) = (-(2 : ℝ)))
  (h5 : (f (3 : ℝ)) = 5)
  (h6 : (f (0 : ℝ)) = b)
  (h7 : b = (-(2 : ℝ)))
  (h8 : (f (0 : ℝ)) = (-(2 : ℝ)))
  (h9 : (f (3 : ℝ)) = ((3 * a) + b))
  (h10 : ((3 * a) + b) = 5)
  : (f (3 : ℝ)) = 5 := by
  sorry

theorem proof_gap_exercise_197_7
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((a * x) + b)))))
  (h4 : (f (0 : ℝ)) = (-(2 : ℝ)))
  (h5 : (f (3 : ℝ)) = 5)
  (h6 : (f (0 : ℝ)) = b)
  (h7 : b = (-(2 : ℝ)))
  (h8 : (f (0 : ℝ)) = (-(2 : ℝ)))
  (h9 : (f (3 : ℝ)) = ((3 * a) + b))
  (h10 : ((3 * a) + b) = 5)
  (h11 : (f (3 : ℝ)) = 5)
  : a = (7 /. 3) := by
  sorry

theorem proof_gap_exercise_197_8
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((a * x) + b)))))
  (h4 : (f (0 : ℝ)) = (-(2 : ℝ)))
  (h5 : (f (3 : ℝ)) = 5)
  (h6 : (f (0 : ℝ)) = b)
  (h7 : b = (-(2 : ℝ)))
  (h8 : (f (0 : ℝ)) = (-(2 : ℝ)))
  (h9 : (f (3 : ℝ)) = ((3 * a) + b))
  (h10 : ((3 * a) + b) = 5)
  (h11 : (f (3 : ℝ)) = 5)
  (h12 : a = (7 /. 3))
  : b = (-(2 : ℝ)) := by
  sorry

theorem proof_gap_exercise_197_9
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((a * x) + b)))))
  (h4 : (f (0 : ℝ)) = (-(2 : ℝ)))
  (h5 : (f (3 : ℝ)) = 5)
  (h6 : (f (0 : ℝ)) = b)
  (h7 : b = (-(2 : ℝ)))
  (h8 : (f (0 : ℝ)) = (-(2 : ℝ)))
  (h9 : (f (3 : ℝ)) = ((3 * a) + b))
  (h10 : ((3 * a) + b) = 5)
  (h11 : (f (3 : ℝ)) = 5)
  (h12 : a = (7 /. 3))
  (h13 : b = (-(2 : ℝ)))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((7 /. 3) * x) - 2)))) := by
  sorry

theorem proof_gap_exercise_197_10
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((a * x) + b)))))
  (h4 : (f (0 : ℝ)) = (-(2 : ℝ)))
  (h5 : (f (3 : ℝ)) = 5)
  (h6 : (f (0 : ℝ)) = b)
  (h7 : b = (-(2 : ℝ)))
  (h8 : (f (0 : ℝ)) = (-(2 : ℝ)))
  (h9 : (f (3 : ℝ)) = ((3 * a) + b))
  (h10 : ((3 * a) + b) = 5)
  (h11 : (f (3 : ℝ)) = 5)
  (h12 : a = (7 /. 3))
  (h13 : b = (-(2 : ℝ)))
  (h14 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((7 /. 3) * x) - 2)))))
  : (f (1 : ℝ)) = (1 /. 3) := by
  sorry

theorem proof_gap_exercise_197_11
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((a * x) + b)))))
  (h4 : (f (0 : ℝ)) = (-(2 : ℝ)))
  (h5 : (f (3 : ℝ)) = 5)
  (h6 : (f (0 : ℝ)) = b)
  (h7 : b = (-(2 : ℝ)))
  (h8 : (f (0 : ℝ)) = (-(2 : ℝ)))
  (h9 : (f (3 : ℝ)) = ((3 * a) + b))
  (h10 : ((3 * a) + b) = 5)
  (h11 : (f (3 : ℝ)) = 5)
  (h12 : a = (7 /. 3))
  (h13 : b = (-(2 : ℝ)))
  (h14 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((7 /. 3) * x) - 2)))))
  (h15 : (f (1 : ℝ)) = (1 /. 3))
  : (f (2 : ℝ)) = (8 /. 3) := by
  sorry

theorem proof_gap_exercise_197_12
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((a * x) + b)))))
  (h4 : (f (0 : ℝ)) = (-(2 : ℝ)))
  (h5 : (f (3 : ℝ)) = 5)
  (h6 : (f (0 : ℝ)) = b)
  (h7 : b = (-(2 : ℝ)))
  (h8 : (f (0 : ℝ)) = (-(2 : ℝ)))
  (h9 : (f (3 : ℝ)) = ((3 * a) + b))
  (h10 : ((3 * a) + b) = 5)
  (h11 : (f (3 : ℝ)) = 5)
  (h12 : a = (7 /. 3))
  (h13 : b = (-(2 : ℝ)))
  (h14 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((7 /. 3) * x) - 2)))))
  (h15 : (f (1 : ℝ)) = (1 /. 3))
  (h16 : (f (2 : ℝ)) = (8 /. 3))
  : ((((a = (7 /. 3)) ∧ (b = (-(2 : ℝ)))) ∧ ((f (1 : ℝ)) = (1 /. 3))) ∧ ((f (2 : ℝ)) = (8 /. 3))) → (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((a * x) + b)))) := by
  sorry

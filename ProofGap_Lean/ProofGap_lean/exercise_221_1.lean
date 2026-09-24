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

-- exercise: exercise_221_1

theorem proof_gap_exercise_221_1_1
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((a * x) + b)))))
  : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_1 < x_2)) → (((f x_2) - (f x_1)) = (a * (x_2 - x_1))))))) := by
  sorry

theorem proof_gap_exercise_221_1_2
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((a * x) + b)))))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_1 < x_2)) → (((f x_2) - (f x_1)) = (a * (x_2 - x_1))))))))
  : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_1 < x_2)) ∧ (a > 0)) → (((f x_2) - (f x_1)) > 0))))) := by
  sorry

theorem proof_gap_exercise_221_1_3
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((a * x) + b)))))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_1 < x_2)) → (((f x_2) - (f x_1)) = (a * (x_2 - x_1))))))))
  (h5 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_1 < x_2)) ∧ (a > 0)) → (((f x_2) - (f x_1)) > 0))))))
  : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_1 < x_2)) ∧ (a > 0)) → (Monotone f))))) := by
  sorry

theorem proof_gap_exercise_221_1_4
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((a * x) + b)))))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_1 < x_2)) → (((f x_2) - (f x_1)) = (a * (x_2 - x_1))))))))
  (h5 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_1 < x_2)) ∧ (a > 0)) → (((f x_2) - (f x_1)) > 0))))))
  (h6 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_1 < x_2)) ∧ (a > 0)) → (Monotone f))))))
  : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_1 < x_2)) ∧ (a < 0)) → (((f x_2) - (f x_1)) < 0))))) := by
  sorry

theorem proof_gap_exercise_221_1_5
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((a * x) + b)))))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_1 < x_2)) → (((f x_2) - (f x_1)) = (a * (x_2 - x_1))))))))
  (h5 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_1 < x_2)) ∧ (a > 0)) → (((f x_2) - (f x_1)) > 0))))))
  (h6 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_1 < x_2)) ∧ (a > 0)) → (Monotone f))))))
  (h7 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_1 < x_2)) ∧ (a < 0)) → (((f x_2) - (f x_1)) < 0))))))
  : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_1 < x_2)) ∧ (a < 0)) → (Antitone f))))) := by
  sorry

theorem proof_gap_exercise_221_1_6
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((a * x) + b)))))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_1 < x_2)) → (((f x_2) - (f x_1)) = (a * (x_2 - x_1))))))))
  (h5 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_1 < x_2)) ∧ (a > 0)) → (((f x_2) - (f x_1)) > 0))))))
  (h6 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_1 < x_2)) ∧ (a > 0)) → (Monotone f))))))
  (h7 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_1 < x_2)) ∧ (a < 0)) → (((f x_2) - (f x_1)) < 0))))))
  (h8 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_1 < x_2)) ∧ (a < 0)) → (Antitone f))))))
  : (((a > 0) → (Monotone f)) ∧ ((a < 0) → (Antitone f))) → ((Monotone f) ∨ (Antitone f)) := by
  sorry

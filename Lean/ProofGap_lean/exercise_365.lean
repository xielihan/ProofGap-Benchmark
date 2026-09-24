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

-- exercise: exercise_365

theorem proof_gap_exercise_365_1
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (y_0 : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : y_0 ∈ (Set.univ : Set ℝ))
  (h4 : b ≠ a)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((f (a + x)) - y_0) = (y_0 - (f (a - x)))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (b + x)) = (f (b - x))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (b + x)) = ((2 * y_0) - (f (((2 * a) - b) - x)))))) := by
  sorry

theorem proof_gap_exercise_365_2
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (y_0 : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : y_0 ∈ (Set.univ : Set ℝ))
  (h4 : b ≠ a)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((f (a + x)) - y_0) = (y_0 - (f (a - x)))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (b + x)) = (f (b - x))))))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (b + x)) = ((2 * y_0) - (f (((2 * a) - b) - x)))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (b - x)) = ((2 * y_0) - (f (((2 * a) - b) - x)))))) := by
  sorry

theorem proof_gap_exercise_365_3
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (y_0 : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : y_0 ∈ (Set.univ : Set ℝ))
  (h4 : b ≠ a)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((f (a + x)) - y_0) = (y_0 - (f (a - x)))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (b + x)) = (f (b - x))))))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (b + x)) = ((2 * y_0) - (f (((2 * a) - b) - x)))))))
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (b - x)) = ((2 * y_0) - (f (((2 * a) - b) - x)))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((2 * y_0) - (f (((2 * a) - (2 * b)) + x)))))) := by
  sorry

theorem proof_gap_exercise_365_4
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (y_0 : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : y_0 ∈ (Set.univ : Set ℝ))
  (h4 : b ≠ a)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((f (a + x)) - y_0) = (y_0 - (f (a - x)))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (b + x)) = (f (b - x))))))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (b + x)) = ((2 * y_0) - (f (((2 * a) - b) - x)))))))
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (b - x)) = ((2 * y_0) - (f (((2 * a) - b) - x)))))))
  (h9 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((2 * y_0) - (f (((2 * a) - (2 * b)) + x)))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (((2 * b) - (2 * a)) + x)) = ((2 * y_0) - (f x))))) := by
  sorry

theorem proof_gap_exercise_365_5
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (y_0 : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : y_0 ∈ (Set.univ : Set ℝ))
  (h4 : b ≠ a)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((f (a + x)) - y_0) = (y_0 - (f (a - x)))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (b + x)) = (f (b - x))))))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (b + x)) = ((2 * y_0) - (f (((2 * a) - b) - x)))))))
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (b - x)) = ((2 * y_0) - (f (((2 * a) - b) - x)))))))
  (h9 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((2 * y_0) - (f (((2 * a) - (2 * b)) + x)))))))
  (h10 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (((2 * b) - (2 * a)) + x)) = ((2 * y_0) - (f x))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (((2 * a) - (2 * b)) + x)) = (f (((2 * b) - (2 * a)) + x))))) := by
  sorry

theorem proof_gap_exercise_365_6
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (y_0 : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : y_0 ∈ (Set.univ : Set ℝ))
  (h4 : b ≠ a)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((f (a + x)) - y_0) = (y_0 - (f (a - x)))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (b + x)) = (f (b - x))))))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (b + x)) = ((2 * y_0) - (f (((2 * a) - b) - x)))))))
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (b - x)) = ((2 * y_0) - (f (((2 * a) - b) - x)))))))
  (h9 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((2 * y_0) - (f (((2 * a) - (2 * b)) + x)))))))
  (h10 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (((2 * b) - (2 * a)) + x)) = ((2 * y_0) - (f x))))))
  (h11 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (((2 * a) - (2 * b)) + x)) = (f (((2 * b) - (2 * a)) + x))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (f ((4 * (b - a)) + x))))) := by
  sorry

theorem proof_gap_exercise_365_7
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (y_0 : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : y_0 ∈ (Set.univ : Set ℝ))
  (h4 : b ≠ a)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((f (a + x)) - y_0) = (y_0 - (f (a - x)))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (b + x)) = (f (b - x))))))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (b + x)) = ((2 * y_0) - (f (((2 * a) - b) - x)))))))
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (b - x)) = ((2 * y_0) - (f (((2 * a) - b) - x)))))))
  (h9 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((2 * y_0) - (f (((2 * a) - (2 * b)) + x)))))))
  (h10 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (((2 * b) - (2 * a)) + x)) = ((2 * y_0) - (f x))))))
  (h11 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (((2 * a) - (2 * b)) + x)) = (f (((2 * b) - (2 * a)) + x))))))
  (h12 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (f ((4 * (b - a)) + x))))))
  : Function.Periodic f (4 * (b - a)) := by
  sorry

theorem proof_gap_exercise_365_8
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (y_0 : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : y_0 ∈ (Set.univ : Set ℝ))
  (h4 : b ≠ a)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((f (a + x)) - y_0) = (y_0 - (f (a - x)))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (b + x)) = (f (b - x))))))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (b + x)) = ((2 * y_0) - (f (((2 * a) - b) - x)))))))
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (b - x)) = ((2 * y_0) - (f (((2 * a) - b) - x)))))))
  (h9 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((2 * y_0) - (f (((2 * a) - (2 * b)) + x)))))))
  (h10 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (((2 * b) - (2 * a)) + x)) = ((2 * y_0) - (f x))))))
  (h11 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (((2 * a) - (2 * b)) + x)) = (f (((2 * b) - (2 * a)) + x))))))
  (h12 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (f ((4 * (b - a)) + x))))))
  (h13 : Function.Periodic f (4 * (b - a)))
  : Function.Periodic f (4 * (b - a)) := by
  sorry

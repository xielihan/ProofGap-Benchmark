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

-- exercise: exercise_361_3

theorem proof_gap_exercise_361_3_1
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (d : ℝ)
  (x_0 : ℝ)
  (y_0 : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : d ∈ (Set.univ : Set ℝ))
  (h5 : x_0 ∈ (Set.univ : Set ℝ))
  (h6 : y_0 ∈ (Set.univ : Set ℝ))
  (h7 : a ≠ 0)
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((((a * (x ^ (3 : ℕ))) + (b * (x ^ (2 : ℕ)))) + (c * x)) + d)))))
  : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (((y (x_0 + t)) + (y (x_0 - t))) = ((((((((a * ((x_0 + t) ^ (3 : ℕ))) + (b * ((x_0 + t) ^ (2 : ℕ)))) + (c * (x_0 + t))) + d) + (a * ((x_0 - t) ^ (3 : ℕ)))) + (b * ((x_0 - t) ^ (2 : ℕ)))) + (c * (x_0 - t))) + d)))) := by
  sorry

theorem proof_gap_exercise_361_3_2
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (d : ℝ)
  (x_0 : ℝ)
  (y_0 : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : d ∈ (Set.univ : Set ℝ))
  (h5 : x_0 ∈ (Set.univ : Set ℝ))
  (h6 : y_0 ∈ (Set.univ : Set ℝ))
  (h7 : a ≠ 0)
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((((a * (x ^ (3 : ℕ))) + (b * (x ^ (2 : ℕ)))) + (c * x)) + d)))))
  (h9 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (((y (x_0 + t)) + (y (x_0 - t))) = ((((((((a * ((x_0 + t) ^ (3 : ℕ))) + (b * ((x_0 + t) ^ (2 : ℕ)))) + (c * (x_0 + t))) + d) + (a * ((x_0 - t) ^ (3 : ℕ)))) + (b * ((x_0 - t) ^ (2 : ℕ)))) + (c * (x_0 - t))) + d)))))
  : (x_0 = (-(b /. (3 * a)))) → (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (((y (x_0 + t)) + (y (x_0 - t))) = (2 * y_0)))) := by
  sorry

theorem proof_gap_exercise_361_3_3
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (d : ℝ)
  (x_0 : ℝ)
  (y_0 : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : d ∈ (Set.univ : Set ℝ))
  (h5 : x_0 ∈ (Set.univ : Set ℝ))
  (h6 : y_0 ∈ (Set.univ : Set ℝ))
  (h7 : a ≠ 0)
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((((a * (x ^ (3 : ℕ))) + (b * (x ^ (2 : ℕ)))) + (c * x)) + d)))))
  (h9 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (((y (x_0 + t)) + (y (x_0 - t))) = ((((((((a * ((x_0 + t) ^ (3 : ℕ))) + (b * ((x_0 + t) ^ (2 : ℕ)))) + (c * (x_0 + t))) + d) + (a * ((x_0 - t) ^ (3 : ℕ)))) + (b * ((x_0 - t) ^ (2 : ℕ)))) + (c * (x_0 - t))) + d)))))
  (h10 : (x_0 = (-(b /. (3 * a)))) → (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (((y (x_0 + t)) + (y (x_0 - t))) = (2 * y_0)))))
  : (y_0 = ((((a * (x_0 ^ (3 : ℕ))) + (b * (x_0 ^ (2 : ℕ)))) + (c * x_0)) + d)) → (x_0 = (-(b /. (3 * a)))) := by
  sorry

theorem proof_gap_exercise_361_3_4
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (d : ℝ)
  (x_0 : ℝ)
  (y_0 : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : d ∈ (Set.univ : Set ℝ))
  (h5 : x_0 ∈ (Set.univ : Set ℝ))
  (h6 : y_0 ∈ (Set.univ : Set ℝ))
  (h7 : a ≠ 0)
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((((a * (x ^ (3 : ℕ))) + (b * (x ^ (2 : ℕ)))) + (c * x)) + d)))))
  (h9 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (((y (x_0 + t)) + (y (x_0 - t))) = ((((((((a * ((x_0 + t) ^ (3 : ℕ))) + (b * ((x_0 + t) ^ (2 : ℕ)))) + (c * (x_0 + t))) + d) + (a * ((x_0 - t) ^ (3 : ℕ)))) + (b * ((x_0 - t) ^ (2 : ℕ)))) + (c * (x_0 - t))) + d)))))
  (h10 : (x_0 = (-(b /. (3 * a)))) → (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (((y (x_0 + t)) + (y (x_0 - t))) = (2 * y_0)))))
  (h11 : (y_0 = ((((a * (x_0 ^ (3 : ℕ))) + (b * (x_0 ^ (2 : ℕ)))) + (c * x_0)) + d)) → (x_0 = (-(b /. (3 * a)))))
  : (y_0 = ((((a * (x_0 ^ (3 : ℕ))) + (b * (x_0 ^ (2 : ℕ)))) + (c * x_0)) + d)) → (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (((y (x_0 + t)) + (y (x_0 - t))) = (2 * y_0)))) := by
  sorry

theorem proof_gap_exercise_361_3_5
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (d : ℝ)
  (x_0 : ℝ)
  (y_0 : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : d ∈ (Set.univ : Set ℝ))
  (h5 : x_0 ∈ (Set.univ : Set ℝ))
  (h6 : y_0 ∈ (Set.univ : Set ℝ))
  (h7 : a ≠ 0)
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((((a * (x ^ (3 : ℕ))) + (b * (x ^ (2 : ℕ)))) + (c * x)) + d)))))
  (h9 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (((y (x_0 + t)) + (y (x_0 - t))) = ((((((((a * ((x_0 + t) ^ (3 : ℕ))) + (b * ((x_0 + t) ^ (2 : ℕ)))) + (c * (x_0 + t))) + d) + (a * ((x_0 - t) ^ (3 : ℕ)))) + (b * ((x_0 - t) ^ (2 : ℕ)))) + (c * (x_0 - t))) + d)))))
  : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (((y ((-(b /. (3 * a))) + t)) + (y ((-(b /. (3 * a))) - t))) = (2 * (y (-(b /. (3 * a)))))))) := by
  sorry

theorem proof_gap_exercise_361_3_6
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (d : ℝ)
  (x_0 : ℝ)
  (y_0 : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : d ∈ (Set.univ : Set ℝ))
  (h5 : x_0 ∈ (Set.univ : Set ℝ))
  (h6 : y_0 ∈ (Set.univ : Set ℝ))
  (h7 : a ≠ 0)
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((((a * (x ^ (3 : ℕ))) + (b * (x ^ (2 : ℕ)))) + (c * x)) + d)))))
  (h9 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (((y (x_0 + t)) + (y (x_0 - t))) = ((((((((a * ((x_0 + t) ^ (3 : ℕ))) + (b * ((x_0 + t) ^ (2 : ℕ)))) + (c * (x_0 + t))) + d) + (a * ((x_0 - t) ^ (3 : ℕ)))) + (b * ((x_0 - t) ^ (2 : ℕ)))) + (c * (x_0 - t))) + d)))))
  (h10 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (((y (x_0 + t)) + (y (x_0 - t))) = (2 * y_0)))) → (y_0 = (y x_0)))
  (h11 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (((y (x_0 + t)) + (y (x_0 - t))) = (2 * y_0)))) → (x_0 = (-(b /. (3 * a)))))
  (h12 : (x_0 = (-(b /. (3 * a)))) → ((y_0 = (y x_0)) → (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (((y (x_0 + t)) + (y (x_0 - t))) = (2 * y_0))))))
  (h13 : ((x_0, y_0) = ((-(b /. (3 * a))), ((((a * ((-(b /. (3 * a))) ^ (3 : ℕ))) + (b * ((-(b /. (3 * a))) ^ (2 : ℕ)))) + (c * (-(b /. (3 * a))))) + d))) ↔ ((x_0 = (-(b /. (3 * a)))) ∧ (y_0 = (y (-(b /. (3 * a)))))))
  : ((x_0, y_0) = ((-(b /. (3 * a))), ((((a * ((-(b /. (3 * a))) ^ (3 : ℕ))) + (b * ((-(b /. (3 * a))) ^ (2 : ℕ)))) + (c * (-(b /. (3 * a))))) + d))) ↔ (((x_0 ∈ (Set.univ : Set ℝ)) ∧ (y_0 ∈ (Set.univ : Set ℝ))) ∧ (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (((y (x_0 + t)) + (y (x_0 - t))) = (2 * y_0))))) := by
  sorry

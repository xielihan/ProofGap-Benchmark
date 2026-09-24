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

-- exercise: exercise_361_2

theorem proof_gap_exercise_361_2_1
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
  (h7 : c ≠ 0)
  (h8 : ((a * d) - (b * c)) ≠ 0)
  (h9 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((y x) = (((a * x) + b) /. ((c * x) + d))))))
  : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (((c * (x_0 + t)) + d) ≠ 0)) ∧ (((c * (x_0 - t)) + d) ≠ 0)) → (((y (x_0 + t)) + (y (x_0 - t))) = ((((a * (x_0 + t)) + b) /. ((c * (x_0 + t)) + d)) + (((a * (x_0 - t)) + b) /. ((c * (x_0 - t)) + d)))))) := by
  sorry

theorem proof_gap_exercise_361_2_2
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
  (h7 : c ≠ 0)
  (h8 : ((a * d) - (b * c)) ≠ 0)
  (h9 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((y x) = (((a * x) + b) /. ((c * x) + d))))))
  (h10 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (((c * (x_0 + t)) + d) ≠ 0)) ∧ (((c * (x_0 - t)) + d) ≠ 0)) → (((y (x_0 + t)) + (y (x_0 - t))) = ((((a * (x_0 + t)) + b) /. ((c * (x_0 + t)) + d)) + (((a * (x_0 - t)) + b) /. ((c * (x_0 - t)) + d)))))))
  : (x_0 = (-(d /. c))) → (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (((y (x_0 + t)) + (y (x_0 - t))) = (2 * y_0)))) := by
  sorry

theorem proof_gap_exercise_361_2_3
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
  (h7 : c ≠ 0)
  (h8 : ((a * d) - (b * c)) ≠ 0)
  (h9 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((y x) = (((a * x) + b) /. ((c * x) + d))))))
  (h10 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (((c * (x_0 + t)) + d) ≠ 0)) ∧ (((c * (x_0 - t)) + d) ≠ 0)) → (((y (x_0 + t)) + (y (x_0 - t))) = ((((a * (x_0 + t)) + b) /. ((c * (x_0 + t)) + d)) + (((a * (x_0 - t)) + b) /. ((c * (x_0 - t)) + d)))))))
  (h11 : (x_0 = (-(d /. c))) → (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (((y (x_0 + t)) + (y (x_0 - t))) = (2 * y_0)))))
  : (y_0 = (a /. c)) → (x_0 = (-(d /. c))) := by
  sorry

theorem proof_gap_exercise_361_2_4
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
  (h7 : c ≠ 0)
  (h8 : ((a * d) - (b * c)) ≠ 0)
  (h9 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((y x) = (((a * x) + b) /. ((c * x) + d))))))
  (h10 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (((c * (x_0 + t)) + d) ≠ 0)) ∧ (((c * (x_0 - t)) + d) ≠ 0)) → (((y (x_0 + t)) + (y (x_0 - t))) = ((((a * (x_0 + t)) + b) /. ((c * (x_0 + t)) + d)) + (((a * (x_0 - t)) + b) /. ((c * (x_0 - t)) + d)))))))
  (h11 : (x_0 = (-(d /. c))) → (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (((y (x_0 + t)) + (y (x_0 - t))) = (2 * y_0)))))
  (h12 : (y_0 = (a /. c)) → (x_0 = (-(d /. c))))
  : (y_0 = (a /. c)) → (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (((y (x_0 + t)) + (y (x_0 - t))) = (2 * y_0)))) := by
  sorry

theorem proof_gap_exercise_361_2_5
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
  (h7 : c ≠ 0)
  (h8 : ((a * d) - (b * c)) ≠ 0)
  (h9 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((y x) = (((a * x) + b) /. ((c * x) + d))))))
  (h10 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (((c * (x_0 + t)) + d) ≠ 0)) ∧ (((c * (x_0 - t)) + d) ≠ 0)) → (((y (x_0 + t)) + (y (x_0 - t))) = ((((a * (x_0 + t)) + b) /. ((c * (x_0 + t)) + d)) + (((a * (x_0 - t)) + b) /. ((c * (x_0 - t)) + d)))))))
  (h11 : (x_0 = (-(d /. c))) → (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (((y (x_0 + t)) + (y (x_0 - t))) = (2 * y_0)))))
  (h12 : (y_0 = (a /. c)) → (x_0 = (-(d /. c))))
  (h13 : (y_0 = (a /. c)) → (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (((y (x_0 + t)) + (y (x_0 - t))) = (2 * y_0)))))
  : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (((c * ((-(d /. c)) + t)) + d) ≠ 0)) ∧ (((c * ((-(d /. c)) - t)) + d) ≠ 0)) → (((y ((-(d /. c)) + t)) + (y ((-(d /. c)) - t))) = (2 * (a /. c))))) := by
  sorry

theorem proof_gap_exercise_361_2_6
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
  (h7 : c ≠ 0)
  (h8 : ((a * d) - (b * c)) ≠ 0)
  (h9 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((y x) = (((a * x) + b) /. ((c * x) + d))))))
  (h10 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (((c * (x_0 + t)) + d) ≠ 0)) ∧ (((c * (x_0 - t)) + d) ≠ 0)) → (((y (x_0 + t)) + (y (x_0 - t))) = ((((a * (x_0 + t)) + b) /. ((c * (x_0 + t)) + d)) + (((a * (x_0 - t)) + b) /. ((c * (x_0 - t)) + d)))))))
  (h11 : (x_0 = (-(d /. c))) → (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (((y (x_0 + t)) + (y (x_0 - t))) = (2 * y_0)))))
  (h12 : (y_0 = (a /. c)) → (x_0 = (-(d /. c))))
  (h13 : (y_0 = (a /. c)) → (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (((y (x_0 + t)) + (y (x_0 - t))) = (2 * y_0)))))
  (h14 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (((c * ((-(d /. c)) + t)) + d) ≠ 0)) ∧ (((c * ((-(d /. c)) - t)) + d) ≠ 0)) → (((y ((-(d /. c)) + t)) + (y ((-(d /. c)) - t))) = (2 * (a /. c))))))
  : ((x_0, y_0) = ((-(d /. c)), (a /. c))) ↔ (((x_0 ∈ (Set.univ : Set ℝ)) ∧ (y_0 ∈ (Set.univ : Set ℝ))) ∧ (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (((c * (x_0 + t)) + d) ≠ 0)) ∧ (((c * (x_0 - t)) + d) ≠ 0)) → (((y (x_0 + t)) + (y (x_0 - t))) = (2 * y_0))))) := by
  sorry

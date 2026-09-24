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

-- exercise: exercise_221_2

theorem proof_gap_exercise_221_2_1
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : a ≠ 0)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((a * (x ^ (2 : ℕ))) + (b * x)) + c)))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((a * ((x + (b /. (2 * a))) ^ (2 : ℕ))) + ((((4 * a) * c) - (b ^ (2 : ℕ))) /. (4 * a)))))) := by
  sorry

theorem proof_gap_exercise_221_2_2
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : a ≠ 0)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((a * (x ^ (2 : ℕ))) + (b * x)) + c)))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((a * ((x + (b /. (2 * a))) ^ (2 : ℕ))) + ((((4 * a) * c) - (b ^ (2 : ℕ))) /. (4 * a)))))))
  : (a > 0) → ((lpMinimumPoints f) = ({x | x = (-(b /. (2 * a)))})) := by
  sorry

theorem proof_gap_exercise_221_2_3
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : a ≠ 0)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((a * (x ^ (2 : ℕ))) + (b * x)) + c)))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((a * ((x + (b /. (2 * a))) ^ (2 : ℕ))) + ((((4 * a) * c) - (b ^ (2 : ℕ))) /. (4 * a)))))))
  (h7 : (a > 0) → ((lpMinimumPoints f) = ({x | x = (-(b /. (2 * a)))})))
  : (a > 0) → (AntitoneOn f (Set.Iio (-(b /. (2 * a))))) := by
  sorry

theorem proof_gap_exercise_221_2_4
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : a ≠ 0)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((a * (x ^ (2 : ℕ))) + (b * x)) + c)))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((a * ((x + (b /. (2 * a))) ^ (2 : ℕ))) + ((((4 * a) * c) - (b ^ (2 : ℕ))) /. (4 * a)))))))
  (h7 : (a > 0) → ((lpMinimumPoints f) = ({x | x = (-(b /. (2 * a)))})))
  (h8 : (a > 0) → (AntitoneOn f (Set.Iio (-(b /. (2 * a))))))
  : (a > 0) → (MonotoneOn f (Set.Ioi (-(b /. (2 * a))))) := by
  sorry

theorem proof_gap_exercise_221_2_5
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : a ≠ 0)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((a * (x ^ (2 : ℕ))) + (b * x)) + c)))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((a * ((x + (b /. (2 * a))) ^ (2 : ℕ))) + ((((4 * a) * c) - (b ^ (2 : ℕ))) /. (4 * a)))))))
  (h7 : (a > 0) → ((lpMinimumPoints f) = ({x | x = (-(b /. (2 * a)))})))
  (h8 : (a > 0) → (AntitoneOn f (Set.Iio (-(b /. (2 * a))))))
  (h9 : (a > 0) → (MonotoneOn f (Set.Ioi (-(b /. (2 * a))))))
  : (a < 0) → ((lpMaximumPoints f) = ({x | x = (-(b /. (2 * a)))})) := by
  sorry

theorem proof_gap_exercise_221_2_6
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : a ≠ 0)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((a * (x ^ (2 : ℕ))) + (b * x)) + c)))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((a * ((x + (b /. (2 * a))) ^ (2 : ℕ))) + ((((4 * a) * c) - (b ^ (2 : ℕ))) /. (4 * a)))))))
  (h7 : (a > 0) → ((lpMinimumPoints f) = ({x | x = (-(b /. (2 * a)))})))
  (h8 : (a > 0) → (AntitoneOn f (Set.Iio (-(b /. (2 * a))))))
  (h9 : (a > 0) → (MonotoneOn f (Set.Ioi (-(b /. (2 * a))))))
  (h10 : (a < 0) → ((lpMaximumPoints f) = ({x | x = (-(b /. (2 * a)))})))
  : (a < 0) → (MonotoneOn f (Set.Iio (-(b /. (2 * a))))) := by
  sorry

theorem proof_gap_exercise_221_2_7
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : a ≠ 0)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((a * (x ^ (2 : ℕ))) + (b * x)) + c)))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((a * ((x + (b /. (2 * a))) ^ (2 : ℕ))) + ((((4 * a) * c) - (b ^ (2 : ℕ))) /. (4 * a)))))))
  (h7 : (a > 0) → ((lpMinimumPoints f) = ({x | x = (-(b /. (2 * a)))})))
  (h8 : (a > 0) → (AntitoneOn f (Set.Iio (-(b /. (2 * a))))))
  (h9 : (a > 0) → (MonotoneOn f (Set.Ioi (-(b /. (2 * a))))))
  (h10 : (a < 0) → ((lpMaximumPoints f) = ({x | x = (-(b /. (2 * a)))})))
  (h11 : (a < 0) → (MonotoneOn f (Set.Iio (-(b /. (2 * a))))))
  : (a < 0) → (AntitoneOn f (Set.Ioi (-(b /. (2 * a))))) := by
  sorry

theorem proof_gap_exercise_221_2_8
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : a ≠ 0)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((a * (x ^ (2 : ℕ))) + (b * x)) + c)))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((a * ((x + (b /. (2 * a))) ^ (2 : ℕ))) + ((((4 * a) * c) - (b ^ (2 : ℕ))) /. (4 * a)))))))
  (h7 : (a > 0) → ((lpMinimumPoints f) = ({x | x = (-(b /. (2 * a)))})))
  (h8 : (a > 0) → (AntitoneOn f (Set.Iio (-(b /. (2 * a))))))
  (h9 : (a > 0) → (MonotoneOn f (Set.Ioi (-(b /. (2 * a))))))
  (h10 : (a < 0) → ((lpMaximumPoints f) = ({x | x = (-(b /. (2 * a)))})))
  (h11 : (a < 0) → (MonotoneOn f (Set.Iio (-(b /. (2 * a))))))
  (h12 : (a < 0) → (AntitoneOn f (Set.Ioi (-(b /. (2 * a))))))
  : (((a > 0) → ((AntitoneOn f (Set.Iio (-(b /. (2 * a))))) ∧ (MonotoneOn f (Set.Ioi (-(b /. (2 * a))))))) ∧ ((a < 0) → ((MonotoneOn f (Set.Iio (-(b /. (2 * a))))) ∧ (AntitoneOn f (Set.Ioi (-(b /. (2 * a)))))))) → ((((MonotoneOn f (Set.Iio (-(b /. (2 * a))))) ∨ (AntitoneOn f (Set.Iio (-(b /. (2 * a)))))) ∨ (MonotoneOn f (Set.Ioi (-(b /. (2 * a)))))) ∨ (AntitoneOn f (Set.Ioi (-(b /. (2 * a)))))) := by
  sorry

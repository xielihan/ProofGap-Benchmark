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

-- exercise: exercise_3435

theorem proof_gap_exercise_3435_1
  (t : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((t x) = (Real.log |(x)|)))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 3 (fun t_1 => y t_1) x) = ((6 * (y x)) /. (x ^ (3 : ℕ)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t_1 => t_1) x) = (1 /. x)))) := by
  sorry

theorem proof_gap_exercise_3435_2
  (t : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((t x) = (Real.log |(x)|)))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 3 (fun t_1 => y t_1) x) = ((6 * (y x)) /. (x ^ (3 : ℕ)))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t_1 => t_1) x) = (1 /. x)))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t_1 => y t_1) x) = ((1 /. x) * (iteratedDeriv 1 (fun t_1 => y t_1) (t x)))))) := by
  sorry

theorem proof_gap_exercise_3435_3
  (t : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((t x) = (Real.log |(x)|)))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 3 (fun t_1 => y t_1) x) = ((6 * (y x)) /. (x ^ (3 : ℕ)))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t_1 => t_1) x) = (1 /. x)))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t_1 => y t_1) x) = ((1 /. x) * (iteratedDeriv 1 (fun t_1 => y t_1) (t x)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 2 (fun t_1 => y t_1) x) = (((iteratedDeriv 2 (fun t_1 => y t_1) (t x)) - (iteratedDeriv 1 (fun t_1 => y t_1) (t x))) /. (x ^ (2 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_3435_4
  (t : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((t x) = (Real.log |(x)|)))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 3 (fun t_1 => y t_1) x) = ((6 * (y x)) /. (x ^ (3 : ℕ)))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t_1 => t_1) x) = (1 /. x)))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t_1 => y t_1) x) = ((1 /. x) * (iteratedDeriv 1 (fun t_1 => y t_1) (t x)))))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 2 (fun t_1 => y t_1) x) = (((iteratedDeriv 2 (fun t_1 => y t_1) (t x)) - (iteratedDeriv 1 (fun t_1 => y t_1) (t x))) /. (x ^ (2 : ℕ)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 3 (fun t_1 => y t_1) x) = ((((iteratedDeriv 3 (fun t_1 => y t_1) (t x)) - (3 * (iteratedDeriv 2 (fun t_1 => y t_1) (t x)))) + (2 * (iteratedDeriv 1 (fun t_1 => y t_1) (t x)))) /. (x ^ (3 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_3435_5
  (t : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((t x) = (Real.log |(x)|)))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 3 (fun t_1 => y t_1) x) = ((6 * (y x)) /. (x ^ (3 : ℕ)))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t_1 => t_1) x) = (1 /. x)))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t_1 => y t_1) x) = ((1 /. x) * (iteratedDeriv 1 (fun t_1 => y t_1) (t x)))))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 2 (fun t_1 => y t_1) x) = (((iteratedDeriv 2 (fun t_1 => y t_1) (t x)) - (iteratedDeriv 1 (fun t_1 => y t_1) (t x))) /. (x ^ (2 : ℕ)))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 3 (fun t_1 => y t_1) x) = ((((iteratedDeriv 3 (fun t_1 => y t_1) (t x)) - (3 * (iteratedDeriv 2 (fun t_1 => y t_1) (t x)))) + (2 * (iteratedDeriv 1 (fun t_1 => y t_1) (t x)))) /. (x ^ (3 : ℕ)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → (((((iteratedDeriv 3 (fun t_1 => y t_1) (t x)) - (3 * (iteratedDeriv 2 (fun t_1 => y t_1) (t x)))) + (2 * (iteratedDeriv 1 (fun t_1 => y t_1) (t x)))) /. (x ^ (3 : ℕ))) = ((6 * (y (t x))) /. (x ^ (3 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_3435_6
  (t : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((t x) = (Real.log |(x)|)))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 3 (fun t_1 => y t_1) x) = ((6 * (y x)) /. (x ^ (3 : ℕ)))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t_1 => t_1) x) = (1 /. x)))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t_1 => y t_1) x) = ((1 /. x) * (iteratedDeriv 1 (fun t_1 => y t_1) (t x)))))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 2 (fun t_1 => y t_1) x) = (((iteratedDeriv 2 (fun t_1 => y t_1) (t x)) - (iteratedDeriv 1 (fun t_1 => y t_1) (t x))) /. (x ^ (2 : ℕ)))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 3 (fun t_1 => y t_1) x) = ((((iteratedDeriv 3 (fun t_1 => y t_1) (t x)) - (3 * (iteratedDeriv 2 (fun t_1 => y t_1) (t x)))) + (2 * (iteratedDeriv 1 (fun t_1 => y t_1) (t x)))) /. (x ^ (3 : ℕ)))))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → (((((iteratedDeriv 3 (fun t_1 => y t_1) (t x)) - (3 * (iteratedDeriv 2 (fun t_1 => y t_1) (t x)))) + (2 * (iteratedDeriv 1 (fun t_1 => y t_1) (t x)))) /. (x ^ (3 : ℕ))) = ((6 * (y (t x))) /. (x ^ (3 : ℕ)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → (((((iteratedDeriv 3 (fun t_1 => y t_1) (t x)) - (3 * (iteratedDeriv 2 (fun t_1 => y t_1) (t x)))) + (2 * (iteratedDeriv 1 (fun t_1 => y t_1) (t x)))) - (6 * (y (t x)))) = 0))) := by
  sorry

theorem proof_gap_exercise_3435_7
  (t : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((t x) = (Real.log |(x)|)))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 3 (fun t_1 => y t_1) x) = ((6 * (y x)) /. (x ^ (3 : ℕ)))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t_1 => t_1) x) = (1 /. x)))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t_1 => y t_1) x) = ((1 /. x) * (iteratedDeriv 1 (fun t_1 => y t_1) (t x)))))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 2 (fun t_1 => y t_1) x) = (((iteratedDeriv 2 (fun t_1 => y t_1) (t x)) - (iteratedDeriv 1 (fun t_1 => y t_1) (t x))) /. (x ^ (2 : ℕ)))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 3 (fun t_1 => y t_1) x) = ((((iteratedDeriv 3 (fun t_1 => y t_1) (t x)) - (3 * (iteratedDeriv 2 (fun t_1 => y t_1) (t x)))) + (2 * (iteratedDeriv 1 (fun t_1 => y t_1) (t x)))) /. (x ^ (3 : ℕ)))))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → (((((iteratedDeriv 3 (fun t_1 => y t_1) (t x)) - (3 * (iteratedDeriv 2 (fun t_1 => y t_1) (t x)))) + (2 * (iteratedDeriv 1 (fun t_1 => y t_1) (t x)))) /. (x ^ (3 : ℕ))) = ((6 * (y (t x))) /. (x ^ (3 : ℕ)))))))
  (h8 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → (((((iteratedDeriv 3 (fun t_1 => y t_1) (t x)) - (3 * (iteratedDeriv 2 (fun t_1 => y t_1) (t x)))) + (2 * (iteratedDeriv 1 (fun t_1 => y t_1) (t x)))) - (6 * (y (t x)))) = 0))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → (((((iteratedDeriv 3 (fun t_1 => y t_1) (t x)) - (3 * (iteratedDeriv 2 (fun t_1 => y t_1) (t x)))) + (2 * (iteratedDeriv 1 (fun t_1 => y t_1) (t x)))) - (6 * (y (t x)))) = 0))) := by
  sorry

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

-- exercise: exercise_2182_3

theorem proof_gap_exercise_2182_3_1
  (f : (ℝ -> ℝ))
  (S_lower : (ℕ -> ℝ))
  (S_upper : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 10))) → ((f x) = (Real.rpow (2 : ℝ) x)))))
  (h3 : h = (10 /. n))
  : (exists (m : (ℕ -> ℝ)), (exists (M : (ℕ -> ℝ)), (forall (i : ℕ), (((i ∈ (Set.univ : Set ℕ)) ∧ (i ≤ (n - 1))) → (((m i) = (Real.rpow (2 : ℝ) (i * h))) ∧ ((M i) = (Real.rpow (2 : ℝ) ((i + 1) * h)))))))) := by
  sorry

theorem proof_gap_exercise_2182_3_2
  (f : (ℝ -> ℝ))
  (S_lower : (ℕ -> ℝ))
  (S_upper : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 10))) → ((f x) = (Real.rpow (2 : ℝ) x)))))
  (h3 : h = (10 /. n))
  (h4 : (exists (m : (ℕ -> ℝ)), (exists (M : (ℕ -> ℝ)), (forall (i : ℕ), (((i ∈ (Set.univ : Set ℕ)) ∧ (i ≤ (n - 1))) → (((m i) = (Real.rpow (2 : ℝ) (i * h))) ∧ ((M i) = (Real.rpow (2 : ℝ) ((i + 1) * h)))))))))
  : (S_lower n) = (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (h * (Real.rpow (2 : ℝ) (i * h)))) := by
  sorry

theorem proof_gap_exercise_2182_3_3
  (f : (ℝ -> ℝ))
  (S_lower : (ℕ -> ℝ))
  (S_upper : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 10))) → ((f x) = (Real.rpow (2 : ℝ) x)))))
  (h3 : h = (10 /. n))
  (h4 : (exists (m : (ℕ -> ℝ)), (exists (M : (ℕ -> ℝ)), (forall (i : ℕ), (((i ∈ (Set.univ : Set ℕ)) ∧ (i ≤ (n - 1))) → (((m i) = (Real.rpow (2 : ℝ) (i * h))) ∧ ((M i) = (Real.rpow (2 : ℝ) ((i + 1) * h)))))))))
  (h5 : (S_lower n) = (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (h * (Real.rpow (2 : ℝ) (i * h)))))
  : (S_lower n) = ((h * ((Real.rpow (2 : ℝ) (n * h)) - 1)) /. ((Real.rpow (2 : ℝ) h) - 1)) := by
  sorry

theorem proof_gap_exercise_2182_3_4
  (f : (ℝ -> ℝ))
  (S_lower : (ℕ -> ℝ))
  (S_upper : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 10))) → ((f x) = (Real.rpow (2 : ℝ) x)))))
  (h3 : h = (10 /. n))
  (h4 : (exists (m : (ℕ -> ℝ)), (exists (M : (ℕ -> ℝ)), (forall (i : ℕ), (((i ∈ (Set.univ : Set ℕ)) ∧ (i ≤ (n - 1))) → (((m i) = (Real.rpow (2 : ℝ) (i * h))) ∧ ((M i) = (Real.rpow (2 : ℝ) ((i + 1) * h)))))))))
  (h5 : (S_lower n) = (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (h * (Real.rpow (2 : ℝ) (i * h)))))
  (h6 : (S_lower n) = ((h * ((Real.rpow (2 : ℝ) (n * h)) - 1)) /. ((Real.rpow (2 : ℝ) h) - 1)))
  : (S_lower n) = (10230 /. (n * ((Real.rpow (2 : ℝ) (10 /. n)) - 1))) := by
  sorry

theorem proof_gap_exercise_2182_3_5
  (f : (ℝ -> ℝ))
  (S_lower : (ℕ -> ℝ))
  (S_upper : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 10))) → ((f x) = (Real.rpow (2 : ℝ) x)))))
  (h3 : h = (10 /. n))
  (h4 : (exists (m : (ℕ -> ℝ)), (exists (M : (ℕ -> ℝ)), (forall (i : ℕ), (((i ∈ (Set.univ : Set ℕ)) ∧ (i ≤ (n - 1))) → (((m i) = (Real.rpow (2 : ℝ) (i * h))) ∧ ((M i) = (Real.rpow (2 : ℝ) ((i + 1) * h)))))))))
  (h5 : (S_lower n) = (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (h * (Real.rpow (2 : ℝ) (i * h)))))
  (h6 : (S_lower n) = ((h * ((Real.rpow (2 : ℝ) (n * h)) - 1)) /. ((Real.rpow (2 : ℝ) h) - 1)))
  (h7 : (S_lower n) = (10230 /. (n * ((Real.rpow (2 : ℝ) (10 /. n)) - 1))))
  : (S_upper n) = (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (h * (Real.rpow (2 : ℝ) ((i + 1) * h)))) := by
  sorry

theorem proof_gap_exercise_2182_3_6
  (f : (ℝ -> ℝ))
  (S_lower : (ℕ -> ℝ))
  (S_upper : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 10))) → ((f x) = (Real.rpow (2 : ℝ) x)))))
  (h3 : h = (10 /. n))
  (h4 : (exists (m : (ℕ -> ℝ)), (exists (M : (ℕ -> ℝ)), (forall (i : ℕ), (((i ∈ (Set.univ : Set ℕ)) ∧ (i ≤ (n - 1))) → (((m i) = (Real.rpow (2 : ℝ) (i * h))) ∧ ((M i) = (Real.rpow (2 : ℝ) ((i + 1) * h)))))))))
  (h5 : (S_lower n) = (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (h * (Real.rpow (2 : ℝ) (i * h)))))
  (h6 : (S_lower n) = ((h * ((Real.rpow (2 : ℝ) (n * h)) - 1)) /. ((Real.rpow (2 : ℝ) h) - 1)))
  (h7 : (S_lower n) = (10230 /. (n * ((Real.rpow (2 : ℝ) (10 /. n)) - 1))))
  (h8 : (S_upper n) = (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (h * (Real.rpow (2 : ℝ) ((i + 1) * h)))))
  : (S_upper n) = (((h * (Real.rpow (2 : ℝ) h)) * ((Real.rpow (2 : ℝ) (n * h)) - 1)) /. ((Real.rpow (2 : ℝ) h) - 1)) := by
  sorry

theorem proof_gap_exercise_2182_3_7
  (f : (ℝ -> ℝ))
  (S_lower : (ℕ -> ℝ))
  (S_upper : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 10))) → ((f x) = (Real.rpow (2 : ℝ) x)))))
  (h3 : h = (10 /. n))
  (h4 : (exists (m : (ℕ -> ℝ)), (exists (M : (ℕ -> ℝ)), (forall (i : ℕ), (((i ∈ (Set.univ : Set ℕ)) ∧ (i ≤ (n - 1))) → (((m i) = (Real.rpow (2 : ℝ) (i * h))) ∧ ((M i) = (Real.rpow (2 : ℝ) ((i + 1) * h)))))))))
  (h5 : (S_lower n) = (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (h * (Real.rpow (2 : ℝ) (i * h)))))
  (h6 : (S_lower n) = ((h * ((Real.rpow (2 : ℝ) (n * h)) - 1)) /. ((Real.rpow (2 : ℝ) h) - 1)))
  (h7 : (S_lower n) = (10230 /. (n * ((Real.rpow (2 : ℝ) (10 /. n)) - 1))))
  (h8 : (S_upper n) = (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (h * (Real.rpow (2 : ℝ) ((i + 1) * h)))))
  (h9 : (S_upper n) = (((h * (Real.rpow (2 : ℝ) h)) * ((Real.rpow (2 : ℝ) (n * h)) - 1)) /. ((Real.rpow (2 : ℝ) h) - 1)))
  : (S_upper n) = ((10230 * (Real.rpow (2 : ℝ) (10 /. n))) /. (n * ((Real.rpow (2 : ℝ) (10 /. n)) - 1))) := by
  sorry

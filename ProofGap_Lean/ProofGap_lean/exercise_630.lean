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

-- exercise: exercise_630

theorem proof_gap_exercise_630_1
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((Real.sin x) = ((((2 : ℕ) ^ n) * (∏ k ∈ Finset.Icc (1 : ℕ) n, (Real.cos (x /. ((2 : ℕ) ^ k))))) * (Real.sin (x /. ((2 : ℕ) ^ n))))))) := by
  sorry

theorem proof_gap_exercise_630_2
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((Real.sin x) = ((((2 : ℕ) ^ n) * (∏ k ∈ Finset.Icc (1 : ℕ) n, (Real.cos (x /. ((2 : ℕ) ^ k))))) * (Real.sin (x /. ((2 : ℕ) ^ n))))))))
  : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (x ≠ 0)) → ((∏ k ∈ Finset.Icc (1 : ℕ) n, (Real.cos (x /. ((2 : ℕ) ^ k)))) = (((Real.sin x) /. x) * ((x /. ((2 : ℕ) ^ n)) /. (Real.sin (x /. ((2 : ℕ) ^ n)))))))) := by
  sorry

theorem proof_gap_exercise_630_3
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((Real.sin x) = ((((2 : ℕ) ^ n) * (∏ k ∈ Finset.Icc (1 : ℕ) n, (Real.cos (x /. ((2 : ℕ) ^ k))))) * (Real.sin (x /. ((2 : ℕ) ^ n))))))))
  (h3 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (x ≠ 0)) → ((∏ k ∈ Finset.Icc (1 : ℕ) n, (Real.cos (x /. ((2 : ℕ) ^ k)))) = (((Real.sin x) /. x) * ((x /. ((2 : ℕ) ^ n)) /. (Real.sin (x /. ((2 : ℕ) ^ n)))))))))
  : (x ≠ 0) → (Tendsto (fun n : ℕ => ((x /. (Real.rpow (2 : ℝ) n)) /. (Real.sin (x /. (Real.rpow (2 : ℝ) n))))) atTop (𝓝 1)) := by
  sorry

theorem proof_gap_exercise_630_4
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((Real.sin x) = ((((2 : ℕ) ^ n) * (∏ k ∈ Finset.Icc (1 : ℕ) n, (Real.cos (x /. ((2 : ℕ) ^ k))))) * (Real.sin (x /. ((2 : ℕ) ^ n))))))))
  (h3 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (x ≠ 0)) → ((∏ k ∈ Finset.Icc (1 : ℕ) n, (Real.cos (x /. ((2 : ℕ) ^ k)))) = (((Real.sin x) /. x) * ((x /. ((2 : ℕ) ^ n)) /. (Real.sin (x /. ((2 : ℕ) ^ n)))))))))
  (h4 : (x ≠ 0) → (Tendsto (fun n : ℕ => ((x /. (Real.rpow (2 : ℝ) n)) /. (Real.sin (x /. (Real.rpow (2 : ℝ) n))))) atTop (𝓝 1)))
  : (x ≠ 0) → (Tendsto (fun n : ℕ => (∏ k ∈ Finset.Icc (1 : ℕ) n, (Real.cos (x /. ((2 : ℕ) ^ k))))) atTop (𝓝 ((Real.sin x) /. x))) := by
  sorry

theorem proof_gap_exercise_630_5
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((Real.sin x) = ((((2 : ℕ) ^ n) * (∏ k ∈ Finset.Icc (1 : ℕ) n, (Real.cos (x /. ((2 : ℕ) ^ k))))) * (Real.sin (x /. ((2 : ℕ) ^ n))))))))
  (h3 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (x ≠ 0)) → ((∏ k ∈ Finset.Icc (1 : ℕ) n, (Real.cos (x /. ((2 : ℕ) ^ k)))) = (((Real.sin x) /. x) * ((x /. ((2 : ℕ) ^ n)) /. (Real.sin (x /. ((2 : ℕ) ^ n)))))))))
  (h4 : (x ≠ 0) → (Tendsto (fun n : ℕ => ((x /. (Real.rpow (2 : ℝ) n)) /. (Real.sin (x /. (Real.rpow (2 : ℝ) n))))) atTop (𝓝 1)))
  (h5 : (x ≠ 0) → (Tendsto (fun n : ℕ => (∏ k ∈ Finset.Icc (1 : ℕ) n, (Real.cos (x /. ((2 : ℕ) ^ k))))) atTop (𝓝 ((Real.sin x) /. x))))
  : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (x = 0)) → ((∏ k ∈ Finset.Icc (1 : ℕ) n, (Real.cos (x /. ((2 : ℕ) ^ k)))) = 1))) := by
  sorry

theorem proof_gap_exercise_630_6
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((Real.sin x) = ((((2 : ℕ) ^ n) * (∏ k ∈ Finset.Icc (1 : ℕ) n, (Real.cos (x /. ((2 : ℕ) ^ k))))) * (Real.sin (x /. ((2 : ℕ) ^ n))))))))
  (h3 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (x ≠ 0)) → ((∏ k ∈ Finset.Icc (1 : ℕ) n, (Real.cos (x /. ((2 : ℕ) ^ k)))) = (((Real.sin x) /. x) * ((x /. ((2 : ℕ) ^ n)) /. (Real.sin (x /. ((2 : ℕ) ^ n)))))))))
  (h4 : (x ≠ 0) → (Tendsto (fun n : ℕ => ((x /. (Real.rpow (2 : ℝ) n)) /. (Real.sin (x /. (Real.rpow (2 : ℝ) n))))) atTop (𝓝 1)))
  (h5 : (x ≠ 0) → (Tendsto (fun n : ℕ => (∏ k ∈ Finset.Icc (1 : ℕ) n, (Real.cos (x /. ((2 : ℕ) ^ k))))) atTop (𝓝 ((Real.sin x) /. x))))
  (h6 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (x = 0)) → ((∏ k ∈ Finset.Icc (1 : ℕ) n, (Real.cos (x /. ((2 : ℕ) ^ k)))) = 1))))
  : (x = 0) → (Tendsto (fun n : ℕ => (∏ k ∈ Finset.Icc (1 : ℕ) n, (Real.cos (x /. ((2 : ℕ) ^ k))))) atTop (𝓝 1)) := by
  sorry

theorem proof_gap_exercise_630_7
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((Real.sin x) = ((((2 : ℕ) ^ n) * (∏ k ∈ Finset.Icc (1 : ℕ) n, (Real.cos (x /. ((2 : ℕ) ^ k))))) * (Real.sin (x /. ((2 : ℕ) ^ n))))))))
  (h3 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (x ≠ 0)) → ((∏ k ∈ Finset.Icc (1 : ℕ) n, (Real.cos (x /. ((2 : ℕ) ^ k)))) = (((Real.sin x) /. x) * ((x /. ((2 : ℕ) ^ n)) /. (Real.sin (x /. ((2 : ℕ) ^ n)))))))))
  (h4 : (x ≠ 0) → (Tendsto (fun n : ℕ => ((x /. (Real.rpow (2 : ℝ) n)) /. (Real.sin (x /. (Real.rpow (2 : ℝ) n))))) atTop (𝓝 1)))
  (h5 : (x ≠ 0) → (Tendsto (fun n : ℕ => (∏ k ∈ Finset.Icc (1 : ℕ) n, (Real.cos (x /. ((2 : ℕ) ^ k))))) atTop (𝓝 ((Real.sin x) /. x))))
  (h6 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (x = 0)) → ((∏ k ∈ Finset.Icc (1 : ℕ) n, (Real.cos (x /. ((2 : ℕ) ^ k)))) = 1))))
  (h7 : (x = 0) → (Tendsto (fun n : ℕ => (∏ k ∈ Finset.Icc (1 : ℕ) n, (Real.cos (x /. ((2 : ℕ) ^ k))))) atTop (𝓝 1)))
  : Tendsto (fun n : ℕ => (∏ k ∈ Finset.Icc (1 : ℕ) n, (Real.cos (x /. ((2 : ℕ) ^ k))))) atTop (𝓝 (if (x ≠ 0) then ((Real.sin x) /. x) else (if (x = 0) then 1 else 1))) := by
  sorry

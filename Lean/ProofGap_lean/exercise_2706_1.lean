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

-- exercise: exercise_2706_1

theorem proof_gap_exercise_2706_1_1
  (a : (ℕ -> ℝ))
  (b : (ℕ -> ℝ))
  (c : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) ∈ (Set.univ : Set ℝ)))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) ∈ (Set.univ : Set ℝ)))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((c n) = ((a n) + (b n))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (a n_1) else 0)))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (¬ Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (b n_1) else 0)))))
  : (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (c n) else 0)) → ((∑' n, if (1 : ℕ) ≤ n then (b n) else 0) = ((∑' n, if (1 : ℕ) ≤ n then (c n) else 0) - (∑' n, if (1 : ℕ) ≤ n then (a n) else 0))) := by
  sorry

theorem proof_gap_exercise_2706_1_2
  (a : (ℕ -> ℝ))
  (b : (ℕ -> ℝ))
  (c : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) ∈ (Set.univ : Set ℝ)))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) ∈ (Set.univ : Set ℝ)))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((c n) = ((a n) + (b n))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (a n_1) else 0)))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (¬ Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (b n_1) else 0)))))
  (h6 : (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (c n) else 0)) → ((∑' n, if (1 : ℕ) ≤ n then (b n) else 0) = ((∑' n, if (1 : ℕ) ≤ n then (c n) else 0) - (∑' n, if (1 : ℕ) ≤ n then (a n) else 0))))
  : (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (c n) else 0)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (b n) else 0)) := by
  sorry

theorem proof_gap_exercise_2706_1_3
  (a : (ℕ -> ℝ))
  (b : (ℕ -> ℝ))
  (c : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) ∈ (Set.univ : Set ℝ)))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) ∈ (Set.univ : Set ℝ)))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((c n) = ((a n) + (b n))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (a n_1) else 0)))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (¬ Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (b n_1) else 0)))))
  (h6 : (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (c n) else 0)) → ((∑' n, if (1 : ℕ) ≤ n then (b n) else 0) = ((∑' n, if (1 : ℕ) ≤ n then (c n) else 0) - (∑' n, if (1 : ℕ) ≤ n then (a n) else 0))))
  (h7 : (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (c n) else 0)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (b n) else 0)))
  : (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (c n) else 0)) → False := by
  sorry

theorem proof_gap_exercise_2706_1_4
  (a : (ℕ -> ℝ))
  (b : (ℕ -> ℝ))
  (c : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) ∈ (Set.univ : Set ℝ)))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) ∈ (Set.univ : Set ℝ)))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((c n) = ((a n) + (b n))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (a n_1) else 0)))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (¬ Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (b n_1) else 0)))))
  (h6 : (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (c n) else 0)) → ((∑' n, if (1 : ℕ) ≤ n then (b n) else 0) = ((∑' n, if (1 : ℕ) ≤ n then (c n) else 0) - (∑' n, if (1 : ℕ) ≤ n then (a n) else 0))))
  (h7 : (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (c n) else 0)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (b n) else 0)))
  (h8 : (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (c n) else 0)) → False)
  : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (c n) else 0) := by
  sorry

theorem proof_gap_exercise_2706_1_5
  (a : (ℕ -> ℝ))
  (b : (ℕ -> ℝ))
  (c : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) ∈ (Set.univ : Set ℝ)))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) ∈ (Set.univ : Set ℝ)))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((c n) = ((a n) + (b n))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (a n_1) else 0)))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (¬ Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (b n_1) else 0)))))
  (h6 : (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (c n) else 0)) → ((∑' n, if (1 : ℕ) ≤ n then (b n) else 0) = ((∑' n, if (1 : ℕ) ≤ n then (c n) else 0) - (∑' n, if (1 : ℕ) ≤ n then (a n) else 0))))
  (h7 : (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (c n) else 0)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (b n) else 0)))
  (h8 : (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (c n) else 0)) → False)
  (h9 : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (c n) else 0))
  : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (c n) else 0) := by
  sorry

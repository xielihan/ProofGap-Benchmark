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

-- exercise: exercise_2796_1

theorem proof_gap_exercise_2796_1_1
  (r : (ℕ -> ℝ))
  (f : (ℝ -> ℝ))
  (S : (ℕ -> ℝ -> ℝ))
  (k : ℕ)
  (h1 : k ∈ (Set.univ : Set ℕ))
  (h2 : (forall (k_1 : ℕ), (((k_1 ∈ (Set.univ : Set ℕ)) ∧ (k_1 ∈ ({n : ℕ | 0 < n}))) → (((r k_1) ∈ ({x_1 : ℝ | ∃ q : ℚ, (q : ℝ) = x_1})) ∧ ((r k_1) ∈ (Set.Icc 0 1))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 1))) → ((f x) = (∑' k_1, if (1 : ℕ) ≤ k_1 then (|((x - (r k_1)))| /. ((3 : ℕ) ^ k_1)) else 0)))))
  (h4 : S = (fun (N : ℕ) => (fun (x : ℝ) => (∑ k_1 ∈ Finset.Icc (1 : ℕ) N, (|((x - (r k_1)))| /. ((3 : ℕ) ^ k_1))))))
  : (forall (k_1 : ℕ) (x : ℝ), (((((k_1 ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (k_1 ∈ ({n : ℕ | 0 < n}))) ∧ (x ∈ (Set.Icc 0 1))) → (|(((x - (r k_1)) /. ((3 : ℕ) ^ k_1)))| ≤ (1 /. ((3 : ℕ) ^ k_1))))) := by
  sorry

theorem proof_gap_exercise_2796_1_2
  (r : (ℕ -> ℝ))
  (f : (ℝ -> ℝ))
  (S : (ℕ -> ℝ -> ℝ))
  (k : ℕ)
  (h1 : k ∈ (Set.univ : Set ℕ))
  (h2 : (forall (k_1 : ℕ), (((k_1 ∈ (Set.univ : Set ℕ)) ∧ (k_1 ∈ ({n : ℕ | 0 < n}))) → (((r k_1) ∈ ({x_1 : ℝ | ∃ q : ℚ, (q : ℝ) = x_1})) ∧ ((r k_1) ∈ (Set.Icc 0 1))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 1))) → ((f x) = (∑' k_1, if (1 : ℕ) ≤ k_1 then (|((x - (r k_1)))| /. ((3 : ℕ) ^ k_1)) else 0)))))
  (h4 : S = (fun (N : ℕ) => (fun (x : ℝ) => (∑ k_1 ∈ Finset.Icc (1 : ℕ) N, (|((x - (r k_1)))| /. ((3 : ℕ) ^ k_1))))))
  (h5 : (forall (k_1 : ℕ) (x : ℝ), (((((k_1 ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (k_1 ∈ ({n : ℕ | 0 < n}))) ∧ (x ∈ (Set.Icc 0 1))) → (|(((x - (r k_1)) /. ((3 : ℕ) ^ k_1)))| ≤ (1 /. ((3 : ℕ) ^ k_1))))))
  : Summable (fun (k_1 : ℕ) => if (1 : ℕ) ≤ k_1 then (1 /. ((3 : ℕ) ^ k_1)) else 0) := by
  sorry

theorem proof_gap_exercise_2796_1_3
  (r : (ℕ -> ℝ))
  (f : (ℝ -> ℝ))
  (S : (ℕ -> ℝ -> ℝ))
  (k : ℕ)
  (h1 : k ∈ (Set.univ : Set ℕ))
  (h2 : (forall (k_1 : ℕ), (((k_1 ∈ (Set.univ : Set ℕ)) ∧ (k_1 ∈ ({n : ℕ | 0 < n}))) → (((r k_1) ∈ ({x_1 : ℝ | ∃ q : ℚ, (q : ℝ) = x_1})) ∧ ((r k_1) ∈ (Set.Icc 0 1))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 1))) → ((f x) = (∑' k_1, if (1 : ℕ) ≤ k_1 then (|((x - (r k_1)))| /. ((3 : ℕ) ^ k_1)) else 0)))))
  (h4 : S = (fun (N : ℕ) => (fun (x : ℝ) => (∑ k_1 ∈ Finset.Icc (1 : ℕ) N, (|((x - (r k_1)))| /. ((3 : ℕ) ^ k_1))))))
  (h5 : (forall (k_1 : ℕ) (x : ℝ), (((((k_1 ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (k_1 ∈ ({n : ℕ | 0 < n}))) ∧ (x ∈ (Set.Icc 0 1))) → (|(((x - (r k_1)) /. ((3 : ℕ) ^ k_1)))| ≤ (1 /. ((3 : ℕ) ^ k_1))))))
  (h6 : Summable (fun (k_1 : ℕ) => if (1 : ℕ) ≤ k_1 then (1 /. ((3 : ℕ) ^ k_1)) else 0))
  : TendstoUniformlyOn S f Filter.atTop (Set.Icc 0 1) := by
  sorry

theorem proof_gap_exercise_2796_1_4
  (r : (ℕ -> ℝ))
  (f : (ℝ -> ℝ))
  (S : (ℕ -> ℝ -> ℝ))
  (k : ℕ)
  (h1 : k ∈ (Set.univ : Set ℕ))
  (h2 : (forall (k_1 : ℕ), (((k_1 ∈ (Set.univ : Set ℕ)) ∧ (k_1 ∈ ({n : ℕ | 0 < n}))) → (((r k_1) ∈ ({x_1 : ℝ | ∃ q : ℚ, (q : ℝ) = x_1})) ∧ ((r k_1) ∈ (Set.Icc 0 1))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 1))) → ((f x) = (∑' k_1, if (1 : ℕ) ≤ k_1 then (|((x - (r k_1)))| /. ((3 : ℕ) ^ k_1)) else 0)))))
  (h4 : S = (fun (N : ℕ) => (fun (x : ℝ) => (∑ k_1 ∈ Finset.Icc (1 : ℕ) N, (|((x - (r k_1)))| /. ((3 : ℕ) ^ k_1))))))
  (h5 : (forall (k_1 : ℕ) (x : ℝ), (((((k_1 ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (k_1 ∈ ({n : ℕ | 0 < n}))) ∧ (x ∈ (Set.Icc 0 1))) → (|(((x - (r k_1)) /. ((3 : ℕ) ^ k_1)))| ≤ (1 /. ((3 : ℕ) ^ k_1))))))
  (h6 : Summable (fun (k_1 : ℕ) => if (1 : ℕ) ≤ k_1 then (1 /. ((3 : ℕ) ^ k_1)) else 0))
  (h7 : TendstoUniformlyOn S f Filter.atTop (Set.Icc 0 1))
  : (forall (k_1 : ℕ), (((k_1 ∈ (Set.univ : Set ℕ)) ∧ (k_1 ∈ ({n : ℕ | 0 < n}))) → (ContinuousOn (fun (x : ℝ) => (|((x - (r k_1)))| /. ((3 : ℕ) ^ k_1))) (Set.Icc 0 1)))) := by
  sorry

theorem proof_gap_exercise_2796_1_5
  (r : (ℕ -> ℝ))
  (f : (ℝ -> ℝ))
  (S : (ℕ -> ℝ -> ℝ))
  (k : ℕ)
  (h1 : k ∈ (Set.univ : Set ℕ))
  (h2 : (forall (k_1 : ℕ), (((k_1 ∈ (Set.univ : Set ℕ)) ∧ (k_1 ∈ ({n : ℕ | 0 < n}))) → (((r k_1) ∈ ({x_1 : ℝ | ∃ q : ℚ, (q : ℝ) = x_1})) ∧ ((r k_1) ∈ (Set.Icc 0 1))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 1))) → ((f x) = (∑' k_1, if (1 : ℕ) ≤ k_1 then (|((x - (r k_1)))| /. ((3 : ℕ) ^ k_1)) else 0)))))
  (h4 : S = (fun (N : ℕ) => (fun (x : ℝ) => (∑ k_1 ∈ Finset.Icc (1 : ℕ) N, (|((x - (r k_1)))| /. ((3 : ℕ) ^ k_1))))))
  (h5 : (forall (k_1 : ℕ) (x : ℝ), (((((k_1 ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (k_1 ∈ ({n : ℕ | 0 < n}))) ∧ (x ∈ (Set.Icc 0 1))) → (|(((x - (r k_1)) /. ((3 : ℕ) ^ k_1)))| ≤ (1 /. ((3 : ℕ) ^ k_1))))))
  (h6 : Summable (fun (k_1 : ℕ) => if (1 : ℕ) ≤ k_1 then (1 /. ((3 : ℕ) ^ k_1)) else 0))
  (h7 : TendstoUniformlyOn S f Filter.atTop (Set.Icc 0 1))
  (h8 : (forall (k_1 : ℕ), (((k_1 ∈ (Set.univ : Set ℕ)) ∧ (k_1 ∈ ({n : ℕ | 0 < n}))) → (ContinuousOn (fun (x : ℝ) => (|((x - (r k_1)))| /. ((3 : ℕ) ^ k_1))) (Set.Icc 0 1)))))
  : ContinuousOn f (Set.Icc 0 1) := by
  sorry

theorem proof_gap_exercise_2796_1_6
  (r : (ℕ -> ℝ))
  (f : (ℝ -> ℝ))
  (S : (ℕ -> ℝ -> ℝ))
  (k : ℕ)
  (h1 : k ∈ (Set.univ : Set ℕ))
  (h2 : (forall (k_1 : ℕ), (((k_1 ∈ (Set.univ : Set ℕ)) ∧ (k_1 ∈ ({n : ℕ | 0 < n}))) → (((r k_1) ∈ ({x_1 : ℝ | ∃ q : ℚ, (q : ℝ) = x_1})) ∧ ((r k_1) ∈ (Set.Icc 0 1))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 1))) → ((f x) = (∑' k_1, if (1 : ℕ) ≤ k_1 then (|((x - (r k_1)))| /. ((3 : ℕ) ^ k_1)) else 0)))))
  (h4 : S = (fun (N : ℕ) => (fun (x : ℝ) => (∑ k_1 ∈ Finset.Icc (1 : ℕ) N, (|((x - (r k_1)))| /. ((3 : ℕ) ^ k_1))))))
  (h5 : (forall (k_1 : ℕ) (x : ℝ), (((((k_1 ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (k_1 ∈ ({n : ℕ | 0 < n}))) ∧ (x ∈ (Set.Icc 0 1))) → (|(((x - (r k_1)) /. ((3 : ℕ) ^ k_1)))| ≤ (1 /. ((3 : ℕ) ^ k_1))))))
  (h6 : Summable (fun (k_1 : ℕ) => if (1 : ℕ) ≤ k_1 then (1 /. ((3 : ℕ) ^ k_1)) else 0))
  (h7 : TendstoUniformlyOn S f Filter.atTop (Set.Icc 0 1))
  (h8 : (forall (k_1 : ℕ), (((k_1 ∈ (Set.univ : Set ℕ)) ∧ (k_1 ∈ ({n : ℕ | 0 < n}))) → (ContinuousOn (fun (x : ℝ) => (|((x - (r k_1)))| /. ((3 : ℕ) ^ k_1))) (Set.Icc 0 1)))))
  (h9 : ContinuousOn f (Set.Icc 0 1))
  : ContinuousOn f (Set.Icc 0 1) := by
  sorry

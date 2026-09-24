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

-- exercise: exercise_2636

theorem proof_gap_exercise_2636_1
  (u : (ℕ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((Real.cos (a /. n)) ^ (n ^ (3 : ℕ)))))))
  : (a = 0) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = 1))) := by
  sorry

theorem proof_gap_exercise_2636_2
  (u : (ℕ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((Real.cos (a /. n)) ^ (n ^ (3 : ℕ)))))))
  (h3 : (a = 0) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = 1))))
  : (a = 0) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (u n) else 0)) := by
  sorry

theorem proof_gap_exercise_2636_3
  (u : (ℕ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((Real.cos (a /. n)) ^ (n ^ (3 : ℕ)))))))
  (h3 : (a = 0) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = 1))))
  (h4 : (a = 0) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (u n) else 0)))
  : (a ≠ 0) → (exists (n_0 : ℕ), (((n_0 ∈ (Set.univ : Set ℕ)) ∧ (n_0 ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ n_0)) → ((Real.cos (a /. n)) > 0))))) := by
  sorry

theorem proof_gap_exercise_2636_4
  (u : (ℕ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((Real.cos (a /. n)) ^ (n ^ (3 : ℕ)))))))
  (h3 : (a = 0) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = 1))))
  (h4 : (a = 0) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (u n) else 0)))
  (h5 : (a ≠ 0) → (exists (n_0 : ℕ), (((n_0 ∈ (Set.univ : Set ℕ)) ∧ (n_0 ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ n_0)) → ((Real.cos (a /. n)) > 0))))))
  : (a ≠ 0) → (exists (n_0 : ℕ), (((n_0 ∈ (Set.univ : Set ℕ)) ∧ (n_0 ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ n_0)) → ((Real.rpow (u n) (1 /. n)) = ((Real.cos (a /. n)) ^ (n ^ (2 : ℕ)))))))) := by
  sorry

theorem proof_gap_exercise_2636_5
  (u : (ℕ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((Real.cos (a /. n)) ^ (n ^ (3 : ℕ)))))))
  (h3 : (a = 0) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = 1))))
  (h4 : (a = 0) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (u n) else 0)))
  (h5 : (a ≠ 0) → (exists (n_0 : ℕ), (((n_0 ∈ (Set.univ : Set ℕ)) ∧ (n_0 ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ n_0)) → ((Real.cos (a /. n)) > 0))))))
  (h6 : (a ≠ 0) → (exists (n_0 : ℕ), (((n_0 ∈ (Set.univ : Set ℕ)) ∧ (n_0 ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ n_0)) → ((Real.rpow (u n) (1 /. n)) = ((Real.cos (a /. n)) ^ (n ^ (2 : ℕ)))))))))
  : (a ≠ 0) → (Tendsto (fun n : ℕ => (Real.rpow (Real.cos (a /. n)) (n ^ (2 : ℕ)))) atTop (𝓝 (Real.exp (-((a ^ (2 : ℕ)) /. 2))))) := by
  sorry

theorem proof_gap_exercise_2636_6
  (u : (ℕ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((Real.cos (a /. n)) ^ (n ^ (3 : ℕ)))))))
  (h3 : (a = 0) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = 1))))
  (h4 : (a = 0) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (u n) else 0)))
  (h5 : (a ≠ 0) → (exists (n_0 : ℕ), (((n_0 ∈ (Set.univ : Set ℕ)) ∧ (n_0 ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ n_0)) → ((Real.cos (a /. n)) > 0))))))
  (h6 : (a ≠ 0) → (exists (n_0 : ℕ), (((n_0 ∈ (Set.univ : Set ℕ)) ∧ (n_0 ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ n_0)) → ((Real.rpow (u n) (1 /. n)) = ((Real.cos (a /. n)) ^ (n ^ (2 : ℕ)))))))))
  (h7 : (a ≠ 0) → (Tendsto (fun n : ℕ => (Real.rpow (Real.cos (a /. n)) (n ^ (2 : ℕ)))) atTop (𝓝 (Real.exp (-((a ^ (2 : ℕ)) /. 2))))))
  : (a ≠ 0) → ((Real.exp (-((a ^ (2 : ℕ)) /. 2))) < 1) := by
  sorry

theorem proof_gap_exercise_2636_7
  (u : (ℕ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((Real.cos (a /. n)) ^ (n ^ (3 : ℕ)))))))
  (h3 : (a = 0) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = 1))))
  (h4 : (a = 0) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (u n) else 0)))
  (h5 : (a ≠ 0) → (exists (n_0 : ℕ), (((n_0 ∈ (Set.univ : Set ℕ)) ∧ (n_0 ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ n_0)) → ((Real.cos (a /. n)) > 0))))))
  (h6 : (a ≠ 0) → (exists (n_0 : ℕ), (((n_0 ∈ (Set.univ : Set ℕ)) ∧ (n_0 ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ n_0)) → ((Real.rpow (u n) (1 /. n)) = ((Real.cos (a /. n)) ^ (n ^ (2 : ℕ)))))))))
  (h7 : (a ≠ 0) → (Tendsto (fun n : ℕ => (Real.rpow (Real.cos (a /. n)) (n ^ (2 : ℕ)))) atTop (𝓝 (Real.exp (-((a ^ (2 : ℕ)) /. 2))))))
  (h8 : (a ≠ 0) → ((Real.exp (-((a ^ (2 : ℕ)) /. 2))) < 1))
  : (a ≠ 0) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (u n) else 0)) := by
  sorry

theorem proof_gap_exercise_2636_8
  (u : (ℕ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((Real.cos (a /. n)) ^ (n ^ (3 : ℕ)))))))
  (h3 : (a = 0) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = 1))))
  (h4 : (a = 0) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (u n) else 0)))
  (h5 : (a ≠ 0) → (exists (n_0 : ℕ), (((n_0 ∈ (Set.univ : Set ℕ)) ∧ (n_0 ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ n_0)) → ((Real.cos (a /. n)) > 0))))))
  (h6 : (a ≠ 0) → (exists (n_0 : ℕ), (((n_0 ∈ (Set.univ : Set ℕ)) ∧ (n_0 ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ n_0)) → ((Real.rpow (u n) (1 /. n)) = ((Real.cos (a /. n)) ^ (n ^ (2 : ℕ)))))))))
  (h7 : (a ≠ 0) → (Tendsto (fun n : ℕ => (Real.rpow (Real.cos (a /. n)) (n ^ (2 : ℕ)))) atTop (𝓝 (Real.exp (-((a ^ (2 : ℕ)) /. 2))))))
  (h8 : (a ≠ 0) → ((Real.exp (-((a ^ (2 : ℕ)) /. 2))) < 1))
  (h9 : (a ≠ 0) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (u n) else 0)))
  : (a ∈ ({a_1 | (a_1 ∈ (Set.univ : Set ℝ)) ∧ (a_1 ≠ 0)})) ↔ (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((Real.cos (a /. n)) ^ (n ^ (3 : ℕ))) else 0)) := by
  sorry

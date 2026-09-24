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

-- exercise: exercise_3033_1

theorem proof_gap_exercise_3033_1_1
  (s : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |(x)| < 1)
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((s n) = ((x ^ (n + 1)) /. ((1 - (x ^ n)) * (1 - (x ^ (n + 1)))))))))
  : (x ≠ 0) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((1 /. (1 - (x ^ n))) - (1 /. (1 - (x ^ (n + 1))))) = (((1 - x) /. x) * (s n))))) := by
  sorry

theorem proof_gap_exercise_3033_1_2
  (s : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |(x)| < 1)
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((s n) = ((x ^ (n + 1)) /. ((1 - (x ^ n)) * (1 - (x ^ (n + 1)))))))))
  (h4 : (x ≠ 0) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((1 /. (1 - (x ^ n))) - (1 /. (1 - (x ^ (n + 1))))) = (((1 - x) /. x) * (s n))))))
  : (x ≠ 0) → (forall (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k ∈ Finset.Icc (1 : ℕ) N, (((1 - x) /. x) * (s k))) = ((1 /. (1 - x)) - (1 /. (1 - (x ^ (N + 1)))))))) := by
  sorry

theorem proof_gap_exercise_3033_1_3
  (s : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |(x)| < 1)
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((s n) = ((x ^ (n + 1)) /. ((1 - (x ^ n)) * (1 - (x ^ (n + 1)))))))))
  (h4 : (x ≠ 0) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((1 /. (1 - (x ^ n))) - (1 /. (1 - (x ^ (n + 1))))) = (((1 - x) /. x) * (s n))))))
  (h5 : (x ≠ 0) → (forall (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k ∈ Finset.Icc (1 : ℕ) N, (((1 - x) /. x) * (s k))) = ((1 /. (1 - x)) - (1 /. (1 - (x ^ (N + 1)))))))))
  : (x ≠ 0) → (forall (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k ∈ Finset.Icc (1 : ℕ) N, (s k)) = ((x /. ((1 - x) ^ (2 : ℕ))) - ((x /. (1 - x)) * (1 /. (1 - (x ^ (N + 1))))))))) := by
  sorry

theorem proof_gap_exercise_3033_1_4
  (s : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |(x)| < 1)
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((s n) = ((x ^ (n + 1)) /. ((1 - (x ^ n)) * (1 - (x ^ (n + 1)))))))))
  (h4 : (x ≠ 0) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((1 /. (1 - (x ^ n))) - (1 /. (1 - (x ^ (n + 1))))) = (((1 - x) /. x) * (s n))))))
  (h5 : (x ≠ 0) → (forall (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k ∈ Finset.Icc (1 : ℕ) N, (((1 - x) /. x) * (s k))) = ((1 /. (1 - x)) - (1 /. (1 - (x ^ (N + 1)))))))))
  (h6 : (x ≠ 0) → (forall (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k ∈ Finset.Icc (1 : ℕ) N, (s k)) = ((x /. ((1 - x) ^ (2 : ℕ))) - ((x /. (1 - x)) * (1 /. (1 - (x ^ (N + 1))))))))))
  : (x ≠ 0) → (forall (N : ℕ), ((N ∈ (Set.univ : Set ℕ)) → (Tendsto (fun N_1 : ℕ => (1 /. (1 - (Real.rpow x (N_1 + 1))))) atTop (𝓝 1)))) := by
  sorry

theorem proof_gap_exercise_3033_1_5
  (s : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |(x)| < 1)
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((s n) = ((x ^ (n + 1)) /. ((1 - (x ^ n)) * (1 - (x ^ (n + 1)))))))))
  (h4 : (x ≠ 0) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((1 /. (1 - (x ^ n))) - (1 /. (1 - (x ^ (n + 1))))) = (((1 - x) /. x) * (s n))))))
  (h5 : (x ≠ 0) → (forall (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k ∈ Finset.Icc (1 : ℕ) N, (((1 - x) /. x) * (s k))) = ((1 /. (1 - x)) - (1 /. (1 - (x ^ (N + 1)))))))))
  (h6 : (x ≠ 0) → (forall (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k ∈ Finset.Icc (1 : ℕ) N, (s k)) = ((x /. ((1 - x) ^ (2 : ℕ))) - ((x /. (1 - x)) * (1 /. (1 - (x ^ (N + 1))))))))))
  (h7 : (x ≠ 0) → (forall (N : ℕ), ((N ∈ (Set.univ : Set ℕ)) → (Tendsto (fun N_1 : ℕ => (1 /. (1 - (Real.rpow x (N_1 + 1))))) atTop (𝓝 1)))))
  : (x ≠ 0) → (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (HasSum (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (s n_1) else 0) ((x ^ (2 : ℕ)) /. ((1 - x) ^ (2 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_3033_1_6
  (s : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |(x)| < 1)
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((s n) = ((x ^ (n + 1)) /. ((1 - (x ^ n)) * (1 - (x ^ (n + 1)))))))))
  (h4 : (x ≠ 0) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((1 /. (1 - (x ^ n))) - (1 /. (1 - (x ^ (n + 1))))) = (((1 - x) /. x) * (s n))))))
  (h5 : (x ≠ 0) → (forall (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k ∈ Finset.Icc (1 : ℕ) N, (((1 - x) /. x) * (s k))) = ((1 /. (1 - x)) - (1 /. (1 - (x ^ (N + 1)))))))))
  (h6 : (x ≠ 0) → (forall (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k ∈ Finset.Icc (1 : ℕ) N, (s k)) = ((x /. ((1 - x) ^ (2 : ℕ))) - ((x /. (1 - x)) * (1 /. (1 - (x ^ (N + 1))))))))))
  (h7 : (x ≠ 0) → (forall (N : ℕ), ((N ∈ (Set.univ : Set ℕ)) → (Tendsto (fun N_1 : ℕ => (1 /. (1 - (Real.rpow x (N_1 + 1))))) atTop (𝓝 1)))))
  (h8 : (x ≠ 0) → (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (HasSum (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (s n_1) else 0) ((x ^ (2 : ℕ)) /. ((1 - x) ^ (2 : ℕ)))))))
  : (x = 0) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((s n) = 0))) := by
  sorry

theorem proof_gap_exercise_3033_1_7
  (s : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |(x)| < 1)
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((s n) = ((x ^ (n + 1)) /. ((1 - (x ^ n)) * (1 - (x ^ (n + 1)))))))))
  (h4 : (x ≠ 0) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((1 /. (1 - (x ^ n))) - (1 /. (1 - (x ^ (n + 1))))) = (((1 - x) /. x) * (s n))))))
  (h5 : (x ≠ 0) → (forall (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k ∈ Finset.Icc (1 : ℕ) N, (((1 - x) /. x) * (s k))) = ((1 /. (1 - x)) - (1 /. (1 - (x ^ (N + 1)))))))))
  (h6 : (x ≠ 0) → (forall (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k ∈ Finset.Icc (1 : ℕ) N, (s k)) = ((x /. ((1 - x) ^ (2 : ℕ))) - ((x /. (1 - x)) * (1 /. (1 - (x ^ (N + 1))))))))))
  (h7 : (x ≠ 0) → (forall (N : ℕ), ((N ∈ (Set.univ : Set ℕ)) → (Tendsto (fun N_1 : ℕ => (1 /. (1 - (Real.rpow x (N_1 + 1))))) atTop (𝓝 1)))))
  (h8 : (x ≠ 0) → (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (HasSum (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (s n_1) else 0) ((x ^ (2 : ℕ)) /. ((1 - x) ^ (2 : ℕ)))))))
  (h9 : (x = 0) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((s n) = 0))))
  : (x = 0) → (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (HasSum (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (s n_1) else 0) 0))) := by
  sorry

theorem proof_gap_exercise_3033_1_8
  (s : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |(x)| < 1)
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((s n) = ((x ^ (n + 1)) /. ((1 - (x ^ n)) * (1 - (x ^ (n + 1)))))))))
  (h4 : (x ≠ 0) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((1 /. (1 - (x ^ n))) - (1 /. (1 - (x ^ (n + 1))))) = (((1 - x) /. x) * (s n))))))
  (h5 : (x ≠ 0) → (forall (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k ∈ Finset.Icc (1 : ℕ) N, (((1 - x) /. x) * (s k))) = ((1 /. (1 - x)) - (1 /. (1 - (x ^ (N + 1)))))))))
  (h6 : (x ≠ 0) → (forall (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k ∈ Finset.Icc (1 : ℕ) N, (s k)) = ((x /. ((1 - x) ^ (2 : ℕ))) - ((x /. (1 - x)) * (1 /. (1 - (x ^ (N + 1))))))))))
  (h7 : (x ≠ 0) → (forall (N : ℕ), ((N ∈ (Set.univ : Set ℕ)) → (Tendsto (fun N_1 : ℕ => (1 /. (1 - (Real.rpow x (N_1 + 1))))) atTop (𝓝 1)))))
  (h8 : (x ≠ 0) → (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (HasSum (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (s n_1) else 0) ((x ^ (2 : ℕ)) /. ((1 - x) ^ (2 : ℕ)))))))
  (h9 : (x = 0) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((s n) = 0))))
  (h10 : (x = 0) → (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (HasSum (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (s n_1) else 0) 0))))
  : (x = 0) → (((x ^ (2 : ℕ)) /. ((1 - x) ^ (2 : ℕ))) = 0) := by
  sorry

theorem proof_gap_exercise_3033_1_9
  (s : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |(x)| < 1)
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((s n) = ((x ^ (n + 1)) /. ((1 - (x ^ n)) * (1 - (x ^ (n + 1)))))))))
  (h4 : (x ≠ 0) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((1 /. (1 - (x ^ n))) - (1 /. (1 - (x ^ (n + 1))))) = (((1 - x) /. x) * (s n))))))
  (h5 : (x ≠ 0) → (forall (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k ∈ Finset.Icc (1 : ℕ) N, (((1 - x) /. x) * (s k))) = ((1 /. (1 - x)) - (1 /. (1 - (x ^ (N + 1)))))))))
  (h6 : (x ≠ 0) → (forall (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k ∈ Finset.Icc (1 : ℕ) N, (s k)) = ((x /. ((1 - x) ^ (2 : ℕ))) - ((x /. (1 - x)) * (1 /. (1 - (x ^ (N + 1))))))))))
  (h7 : (x ≠ 0) → (forall (N : ℕ), ((N ∈ (Set.univ : Set ℕ)) → (Tendsto (fun N_1 : ℕ => (1 /. (1 - (Real.rpow x (N_1 + 1))))) atTop (𝓝 1)))))
  (h8 : (x ≠ 0) → (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (HasSum (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (s n_1) else 0) ((x ^ (2 : ℕ)) /. ((1 - x) ^ (2 : ℕ)))))))
  (h9 : (x = 0) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((s n) = 0))))
  (h10 : (x = 0) → (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (HasSum (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (s n_1) else 0) 0))))
  (h11 : (x = 0) → (((x ^ (2 : ℕ)) /. ((1 - x) ^ (2 : ℕ))) = 0))
  : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((∑' n_1, if (1 : ℕ) ≤ n_1 then (s n_1) else 0) = ((x ^ (2 : ℕ)) /. ((1 - x) ^ (2 : ℕ)))))) := by
  sorry

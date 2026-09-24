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

-- exercise: exercise_2660

theorem proof_gap_exercise_2660_1
  (a : (ℕ -> ℝ))
  (S : ℝ)
  (h1 : S ∈ (Set.univ : Set ℝ))
  (h2 : (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → ((((a ((3 * k) + 1)) = (1 /. ((2 : ℕ) ^ (3 * k)))) ∧ ((a ((3 * k) + 2)) = (1 /. ((2 : ℕ) ^ ((3 * k) + 1))))) ∧ ((a ((3 * k) + 3)) = (-(1 /. ((2 : ℕ) ^ ((3 * k) + 2)))))))))
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (S = (∑' n_1, if (1 : ℕ) ≤ n_1 then (a n_1) else 0)))))
  : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0) := by
  sorry

theorem proof_gap_exercise_2660_2
  (a : (ℕ -> ℝ))
  (S : ℝ)
  (h1 : S ∈ (Set.univ : Set ℝ))
  (h2 : (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → ((((a ((3 * k) + 1)) = (1 /. ((2 : ℕ) ^ (3 * k)))) ∧ ((a ((3 * k) + 2)) = (1 /. ((2 : ℕ) ^ ((3 * k) + 1))))) ∧ ((a ((3 * k) + 3)) = (-(1 /. ((2 : ℕ) ^ ((3 * k) + 2)))))))))
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (S = (∑' n_1, if (1 : ℕ) ≤ n_1 then (a n_1) else 0)))))
  (h4 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0))
  : HasSum (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0) S := by
  sorry

theorem proof_gap_exercise_2660_3
  (a : (ℕ -> ℝ))
  (S : ℝ)
  (h1 : S ∈ (Set.univ : Set ℝ))
  (h2 : (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → ((((a ((3 * k) + 1)) = (1 /. ((2 : ℕ) ^ (3 * k)))) ∧ ((a ((3 * k) + 2)) = (1 /. ((2 : ℕ) ^ ((3 * k) + 1))))) ∧ ((a ((3 * k) + 3)) = (-(1 /. ((2 : ℕ) ^ ((3 * k) + 2)))))))))
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (S = (∑' n_1, if (1 : ℕ) ≤ n_1 then (a n_1) else 0)))))
  (h4 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0))
  (h5 : HasSum (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0) S)
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k ∈ Finset.Icc (0 : ℕ) (n - 1), (((a ((3 * k) + 1)) + (a ((3 * k) + 2))) + (a ((3 * k) + 3)))) = (((1 + (1 /. 2)) - (1 /. ((2 : ℕ) ^ (2 : ℕ)))) * ((1 - (1 /. ((2 : ℕ) ^ (3 * n)))) /. (1 - (1 /. ((2 : ℕ) ^ (3 : ℕ))))))))) := by
  sorry

theorem proof_gap_exercise_2660_4
  (a : (ℕ -> ℝ))
  (S : ℝ)
  (h1 : S ∈ (Set.univ : Set ℝ))
  (h2 : (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → ((((a ((3 * k) + 1)) = (1 /. ((2 : ℕ) ^ (3 * k)))) ∧ ((a ((3 * k) + 2)) = (1 /. ((2 : ℕ) ^ ((3 * k) + 1))))) ∧ ((a ((3 * k) + 3)) = (-(1 /. ((2 : ℕ) ^ ((3 * k) + 2)))))))))
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (S = (∑' n_1, if (1 : ℕ) ≤ n_1 then (a n_1) else 0)))))
  (h4 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0))
  (h5 : HasSum (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0) S)
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k ∈ Finset.Icc (0 : ℕ) (n - 1), (((a ((3 * k) + 1)) + (a ((3 * k) + 2))) + (a ((3 * k) + 3)))) = (((1 + (1 /. 2)) - (1 /. ((2 : ℕ) ^ (2 : ℕ)))) * ((1 - (1 /. ((2 : ℕ) ^ (3 * n)))) /. (1 - (1 /. ((2 : ℕ) ^ (3 : ℕ))))))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k ∈ Finset.Icc (0 : ℕ) (n - 1), (((a ((3 * k) + 1)) + (a ((3 * k) + 2))) + (a ((3 * k) + 3)))) = ((5 /. 4) * ((1 - (1 /. ((2 : ℕ) ^ (3 * n)))) /. (1 - (1 /. ((2 : ℕ) ^ (3 : ℕ))))))))) := by
  sorry

theorem proof_gap_exercise_2660_5
  (a : (ℕ -> ℝ))
  (S : ℝ)
  (h1 : S ∈ (Set.univ : Set ℝ))
  (h2 : (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → ((((a ((3 * k) + 1)) = (1 /. ((2 : ℕ) ^ (3 * k)))) ∧ ((a ((3 * k) + 2)) = (1 /. ((2 : ℕ) ^ ((3 * k) + 1))))) ∧ ((a ((3 * k) + 3)) = (-(1 /. ((2 : ℕ) ^ ((3 * k) + 2)))))))))
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (S = (∑' n_1, if (1 : ℕ) ≤ n_1 then (a n_1) else 0)))))
  (h4 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0))
  (h5 : HasSum (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0) S)
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k ∈ Finset.Icc (0 : ℕ) (n - 1), (((a ((3 * k) + 1)) + (a ((3 * k) + 2))) + (a ((3 * k) + 3)))) = (((1 + (1 /. 2)) - (1 /. ((2 : ℕ) ^ (2 : ℕ)))) * ((1 - (1 /. ((2 : ℕ) ^ (3 * n)))) /. (1 - (1 /. ((2 : ℕ) ^ (3 : ℕ))))))))))
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k ∈ Finset.Icc (0 : ℕ) (n - 1), (((a ((3 * k) + 1)) + (a ((3 * k) + 2))) + (a ((3 * k) + 3)))) = ((5 /. 4) * ((1 - (1 /. ((2 : ℕ) ^ (3 * n)))) /. (1 - (1 /. ((2 : ℕ) ^ (3 : ℕ))))))))))
  : Tendsto (fun n : ℕ => ((5 /. 4) * ((1 - (1 /. (Real.rpow (2 : ℝ) (3 * n)))) /. (1 - (1 /. ((2 : ℕ) ^ (3 : ℕ))))))) atTop (𝓝 S) := by
  sorry

theorem proof_gap_exercise_2660_6
  (a : (ℕ -> ℝ))
  (S : ℝ)
  (h1 : S ∈ (Set.univ : Set ℝ))
  (h2 : (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → ((((a ((3 * k) + 1)) = (1 /. ((2 : ℕ) ^ (3 * k)))) ∧ ((a ((3 * k) + 2)) = (1 /. ((2 : ℕ) ^ ((3 * k) + 1))))) ∧ ((a ((3 * k) + 3)) = (-(1 /. ((2 : ℕ) ^ ((3 * k) + 2)))))))))
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (S = (∑' n_1, if (1 : ℕ) ≤ n_1 then (a n_1) else 0)))))
  (h4 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0))
  (h5 : HasSum (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0) S)
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k ∈ Finset.Icc (0 : ℕ) (n - 1), (((a ((3 * k) + 1)) + (a ((3 * k) + 2))) + (a ((3 * k) + 3)))) = (((1 + (1 /. 2)) - (1 /. ((2 : ℕ) ^ (2 : ℕ)))) * ((1 - (1 /. ((2 : ℕ) ^ (3 * n)))) /. (1 - (1 /. ((2 : ℕ) ^ (3 : ℕ))))))))))
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k ∈ Finset.Icc (0 : ℕ) (n - 1), (((a ((3 * k) + 1)) + (a ((3 * k) + 2))) + (a ((3 * k) + 3)))) = ((5 /. 4) * ((1 - (1 /. ((2 : ℕ) ^ (3 * n)))) /. (1 - (1 /. ((2 : ℕ) ^ (3 : ℕ))))))))))
  (h8 : Tendsto (fun n : ℕ => ((5 /. 4) * ((1 - (1 /. (Real.rpow (2 : ℝ) (3 * n)))) /. (1 - (1 /. ((2 : ℕ) ^ (3 : ℕ))))))) atTop (𝓝 S))
  : S = ((5 /. 4) * (1 /. (1 - (1 /. ((2 : ℕ) ^ (3 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_2660_7
  (a : (ℕ -> ℝ))
  (S : ℝ)
  (h1 : S ∈ (Set.univ : Set ℝ))
  (h2 : (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → ((((a ((3 * k) + 1)) = (1 /. ((2 : ℕ) ^ (3 * k)))) ∧ ((a ((3 * k) + 2)) = (1 /. ((2 : ℕ) ^ ((3 * k) + 1))))) ∧ ((a ((3 * k) + 3)) = (-(1 /. ((2 : ℕ) ^ ((3 * k) + 2)))))))))
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (S = (∑' n_1, if (1 : ℕ) ≤ n_1 then (a n_1) else 0)))))
  (h4 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0))
  (h5 : HasSum (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0) S)
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k ∈ Finset.Icc (0 : ℕ) (n - 1), (((a ((3 * k) + 1)) + (a ((3 * k) + 2))) + (a ((3 * k) + 3)))) = (((1 + (1 /. 2)) - (1 /. ((2 : ℕ) ^ (2 : ℕ)))) * ((1 - (1 /. ((2 : ℕ) ^ (3 * n)))) /. (1 - (1 /. ((2 : ℕ) ^ (3 : ℕ))))))))))
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k ∈ Finset.Icc (0 : ℕ) (n - 1), (((a ((3 * k) + 1)) + (a ((3 * k) + 2))) + (a ((3 * k) + 3)))) = ((5 /. 4) * ((1 - (1 /. ((2 : ℕ) ^ (3 * n)))) /. (1 - (1 /. ((2 : ℕ) ^ (3 : ℕ))))))))))
  (h8 : Tendsto (fun n : ℕ => ((5 /. 4) * ((1 - (1 /. (Real.rpow (2 : ℝ) (3 * n)))) /. (1 - (1 /. ((2 : ℕ) ^ (3 : ℕ))))))) atTop (𝓝 S))
  (h9 : S = ((5 /. 4) * (1 /. (1 - (1 /. ((2 : ℕ) ^ (3 : ℕ)))))))
  : S = (10 /. 7) := by
  sorry

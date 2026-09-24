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

-- exercise: exercise_3091

theorem proof_gap_exercise_3091_1
  (P : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (N : ℕ), ((((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (N ≥ 2)) → ((P N) = (∏ n_1 ∈ Finset.Icc (2 : ℕ) N, (1 + (((-(1 : ℤ)) ^ n_1) /. (Real.log (n_1 : ℝ)))))))))))
  : Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) /. (Real.log (n : ℝ))) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then ‖((((-(1 : ℤ)) ^ n) /. (Real.log (n : ℝ))))‖ else 0) := by
  sorry

theorem proof_gap_exercise_3091_2
  (P : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (N : ℕ), ((((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (N ≥ 2)) → ((P N) = (∏ n_1 ∈ Finset.Icc (2 : ℕ) N, (1 + (((-(1 : ℤ)) ^ n_1) /. (Real.log (n_1 : ℝ)))))))))))
  (h2 : Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) /. (Real.log (n : ℝ))) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then ‖((((-(1 : ℤ)) ^ n) /. (Real.log (n : ℝ))))‖ else 0))
  : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → (((((-(1 : ℤ)) ^ n) /. (Real.log (n : ℝ))) ^ (2 : ℕ)) = (1 /. ((Real.log (n : ℝ)) ^ (2 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_3091_3
  (P : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (N : ℕ), ((((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (N ≥ 2)) → ((P N) = (∏ n_1 ∈ Finset.Icc (2 : ℕ) N, (1 + (((-(1 : ℤ)) ^ n_1) /. (Real.log (n_1 : ℝ)))))))))))
  (h2 : Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) /. (Real.log (n : ℝ))) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then ‖((((-(1 : ℤ)) ^ n) /. (Real.log (n : ℝ))))‖ else 0))
  (h3 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → (((((-(1 : ℤ)) ^ n) /. (Real.log (n : ℝ))) ^ (2 : ℕ)) = (1 /. ((Real.log (n : ℝ)) ^ (2 : ℕ)))))))
  : (exists (N_0 : ℕ), (((N_0 ∈ (Set.univ : Set ℕ)) ∧ (N_0 ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n > N_0)) → (n > ((Real.log (n : ℝ)) ^ (2 : ℕ))))))) := by
  sorry

theorem proof_gap_exercise_3091_4
  (P : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (N : ℕ), ((((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (N ≥ 2)) → ((P N) = (∏ n_1 ∈ Finset.Icc (2 : ℕ) N, (1 + (((-(1 : ℤ)) ^ n_1) /. (Real.log (n_1 : ℝ)))))))))))
  (h2 : Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) /. (Real.log (n : ℝ))) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then ‖((((-(1 : ℤ)) ^ n) /. (Real.log (n : ℝ))))‖ else 0))
  (h3 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → (((((-(1 : ℤ)) ^ n) /. (Real.log (n : ℝ))) ^ (2 : ℕ)) = (1 /. ((Real.log (n : ℝ)) ^ (2 : ℕ)))))))
  (h4 : (exists (N_0 : ℕ), (((N_0 ∈ (Set.univ : Set ℕ)) ∧ (N_0 ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n > N_0)) → (n > ((Real.log (n : ℝ)) ^ (2 : ℕ))))))))
  : (exists (N_0 : ℕ), (((N_0 ∈ (Set.univ : Set ℕ)) ∧ (N_0 ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n > N_0)) → ((1 /. ((Real.log (n : ℝ)) ^ (2 : ℕ))) > (1 /. n)))))) := by
  sorry

theorem proof_gap_exercise_3091_5
  (P : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (N : ℕ), ((((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (N ≥ 2)) → ((P N) = (∏ n_1 ∈ Finset.Icc (2 : ℕ) N, (1 + (((-(1 : ℤ)) ^ n_1) /. (Real.log (n_1 : ℝ)))))))))))
  (h2 : Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) /. (Real.log (n : ℝ))) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then ‖((((-(1 : ℤ)) ^ n) /. (Real.log (n : ℝ))))‖ else 0))
  (h3 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → (((((-(1 : ℤ)) ^ n) /. (Real.log (n : ℝ))) ^ (2 : ℕ)) = (1 /. ((Real.log (n : ℝ)) ^ (2 : ℕ)))))))
  (h4 : (exists (N_0 : ℕ), (((N_0 ∈ (Set.univ : Set ℕ)) ∧ (N_0 ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n > N_0)) → (n > ((Real.log (n : ℝ)) ^ (2 : ℕ))))))))
  (h5 : (exists (N_0 : ℕ), (((N_0 ∈ (Set.univ : Set ℕ)) ∧ (N_0 ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n > N_0)) → ((1 /. ((Real.log (n : ℝ)) ^ (2 : ℕ))) > (1 /. n)))))))
  : ¬ Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then (1 /. n) else 0) := by
  sorry

theorem proof_gap_exercise_3091_6
  (P : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (N : ℕ), ((((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (N ≥ 2)) → ((P N) = (∏ n_1 ∈ Finset.Icc (2 : ℕ) N, (1 + (((-(1 : ℤ)) ^ n_1) /. (Real.log (n_1 : ℝ)))))))))))
  (h2 : Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) /. (Real.log (n : ℝ))) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then ‖((((-(1 : ℤ)) ^ n) /. (Real.log (n : ℝ))))‖ else 0))
  (h3 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → (((((-(1 : ℤ)) ^ n) /. (Real.log (n : ℝ))) ^ (2 : ℕ)) = (1 /. ((Real.log (n : ℝ)) ^ (2 : ℕ)))))))
  (h4 : (exists (N_0 : ℕ), (((N_0 ∈ (Set.univ : Set ℕ)) ∧ (N_0 ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n > N_0)) → (n > ((Real.log (n : ℝ)) ^ (2 : ℕ))))))))
  (h5 : (exists (N_0 : ℕ), (((N_0 ∈ (Set.univ : Set ℕ)) ∧ (N_0 ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n > N_0)) → ((1 /. ((Real.log (n : ℝ)) ^ (2 : ℕ))) > (1 /. n)))))))
  (h6 : ¬ Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then (1 /. n) else 0))
  : ¬ Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then (1 /. ((Real.log (n : ℝ)) ^ (2 : ℕ))) else 0) := by
  sorry

theorem proof_gap_exercise_3091_7
  (P : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (N : ℕ), ((((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (N ≥ 2)) → ((P N) = (∏ n_1 ∈ Finset.Icc (2 : ℕ) N, (1 + (((-(1 : ℤ)) ^ n_1) /. (Real.log (n_1 : ℝ)))))))))))
  (h2 : Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) /. (Real.log (n : ℝ))) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then ‖((((-(1 : ℤ)) ^ n) /. (Real.log (n : ℝ))))‖ else 0))
  (h3 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → (((((-(1 : ℤ)) ^ n) /. (Real.log (n : ℝ))) ^ (2 : ℕ)) = (1 /. ((Real.log (n : ℝ)) ^ (2 : ℕ)))))))
  (h4 : (exists (N_0 : ℕ), (((N_0 ∈ (Set.univ : Set ℕ)) ∧ (N_0 ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n > N_0)) → (n > ((Real.log (n : ℝ)) ^ (2 : ℕ))))))))
  (h5 : (exists (N_0 : ℕ), (((N_0 ∈ (Set.univ : Set ℕ)) ∧ (N_0 ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n > N_0)) → ((1 /. ((Real.log (n : ℝ)) ^ (2 : ℕ))) > (1 /. n)))))))
  (h6 : ¬ Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then (1 /. n) else 0))
  (h7 : ¬ Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then (1 /. ((Real.log (n : ℝ)) ^ (2 : ℕ))) else 0))
  : ¬ Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then ((((-(1 : ℤ)) ^ n) /. (Real.log (n : ℝ))) ^ (2 : ℕ)) else 0) := by
  sorry

theorem proof_gap_exercise_3091_8
  (P : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (N : ℕ), ((((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (N ≥ 2)) → ((P N) = (∏ n_1 ∈ Finset.Icc (2 : ℕ) N, (1 + (((-(1 : ℤ)) ^ n_1) /. (Real.log (n_1 : ℝ)))))))))))
  (h2 : Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) /. (Real.log (n : ℝ))) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then ‖((((-(1 : ℤ)) ^ n) /. (Real.log (n : ℝ))))‖ else 0))
  (h3 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → (((((-(1 : ℤ)) ^ n) /. (Real.log (n : ℝ))) ^ (2 : ℕ)) = (1 /. ((Real.log (n : ℝ)) ^ (2 : ℕ)))))))
  (h4 : (exists (N_0 : ℕ), (((N_0 ∈ (Set.univ : Set ℕ)) ∧ (N_0 ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n > N_0)) → (n > ((Real.log (n : ℝ)) ^ (2 : ℕ))))))))
  (h5 : (exists (N_0 : ℕ), (((N_0 ∈ (Set.univ : Set ℕ)) ∧ (N_0 ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n > N_0)) → ((1 /. ((Real.log (n : ℝ)) ^ (2 : ℕ))) > (1 /. n)))))))
  (h6 : ¬ Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then (1 /. n) else 0))
  (h7 : ¬ Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then (1 /. ((Real.log (n : ℝ)) ^ (2 : ℕ))) else 0))
  (h8 : ¬ Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then ((((-(1 : ℤ)) ^ n) /. (Real.log (n : ℝ))) ^ (2 : ℕ)) else 0))
  : (¬ ∃ l, Filter.Tendsto P Filter.atTop (𝓝 l)) := by
  sorry

theorem proof_gap_exercise_3091_9
  (P : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (N : ℕ), ((((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (N ≥ 2)) → ((P N) = (∏ n_1 ∈ Finset.Icc (2 : ℕ) N, (1 + (((-(1 : ℤ)) ^ n_1) /. (Real.log (n_1 : ℝ)))))))))))
  (h2 : Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) /. (Real.log (n : ℝ))) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then ‖((((-(1 : ℤ)) ^ n) /. (Real.log (n : ℝ))))‖ else 0))
  (h3 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → (((((-(1 : ℤ)) ^ n) /. (Real.log (n : ℝ))) ^ (2 : ℕ)) = (1 /. ((Real.log (n : ℝ)) ^ (2 : ℕ)))))))
  (h4 : (exists (N_0 : ℕ), (((N_0 ∈ (Set.univ : Set ℕ)) ∧ (N_0 ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n > N_0)) → (n > ((Real.log (n : ℝ)) ^ (2 : ℕ))))))))
  (h5 : (exists (N_0 : ℕ), (((N_0 ∈ (Set.univ : Set ℕ)) ∧ (N_0 ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n > N_0)) → ((1 /. ((Real.log (n : ℝ)) ^ (2 : ℕ))) > (1 /. n)))))))
  (h6 : ¬ Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then (1 /. n) else 0))
  (h7 : ¬ Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then (1 /. ((Real.log (n : ℝ)) ^ (2 : ℕ))) else 0))
  (h8 : ¬ Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then ((((-(1 : ℤ)) ^ n) /. (Real.log (n : ℝ))) ^ (2 : ℕ)) else 0))
  (h9 : (¬ ∃ l, Filter.Tendsto P Filter.atTop (𝓝 l)))
  : (¬ ∃ l, Filter.Tendsto P Filter.atTop (𝓝 l)) := by
  sorry

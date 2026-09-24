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

-- exercise: exercise_3094

theorem proof_gap_exercise_3094_1
  (P : (ℕ -> ℝ))
  (p : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) = (Real.rpow ((n : ℝ) ^ ((-(1 : ℤ)) ^ n)) (((n : ℝ))⁻¹))))))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) → ((P N) = (∏ n_1 ∈ Finset.Icc (1 : ℕ) N, (p n_1))))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) > 0))) := by
  sorry

theorem proof_gap_exercise_3094_2
  (P : (ℕ -> ℝ))
  (p : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) = (Real.rpow ((n : ℝ) ^ ((-(1 : ℤ)) ^ n)) (((n : ℝ))⁻¹))))))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) → ((P N) = (∏ n_1 ∈ Finset.Icc (1 : ℕ) N, (p n_1))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) > 0))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((Real.log (p n)) = ((1 /. n) * (Real.log ((n : ℝ) ^ ((-(1 : ℤ)) ^ n))))))) := by
  sorry

theorem proof_gap_exercise_3094_3
  (P : (ℕ -> ℝ))
  (p : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) = (Real.rpow ((n : ℝ) ^ ((-(1 : ℤ)) ^ n)) (((n : ℝ))⁻¹))))))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) → ((P N) = (∏ n_1 ∈ Finset.Icc (1 : ℕ) N, (p n_1))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) > 0))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((Real.log (p n)) = ((1 /. n) * (Real.log ((n : ℝ) ^ ((-(1 : ℤ)) ^ n))))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((Real.log (p n)) = ((((-(1 : ℤ)) ^ n) /. n) * (Real.log (n : ℝ)))))) := by
  sorry

theorem proof_gap_exercise_3094_4
  (P : (ℕ -> ℝ))
  (p : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) = (Real.rpow ((n : ℝ) ^ ((-(1 : ℤ)) ^ n)) (((n : ℝ))⁻¹))))))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) → ((P N) = (∏ n_1 ∈ Finset.Icc (1 : ℕ) N, (p n_1))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) > 0))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((Real.log (p n)) = ((1 /. n) * (Real.log ((n : ℝ) ^ ((-(1 : ℤ)) ^ n))))))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((Real.log (p n)) = ((((-(1 : ℤ)) ^ n) /. n) * (Real.log (n : ℝ)))))))
  : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) * ((Real.log (n : ℝ)) /. n)) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((((-(1 : ℤ)) ^ n) * ((Real.log (n : ℝ)) /. n)))‖ else 0) := by
  sorry

theorem proof_gap_exercise_3094_5
  (P : (ℕ -> ℝ))
  (p : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) = (Real.rpow ((n : ℝ) ^ ((-(1 : ℤ)) ^ n)) (((n : ℝ))⁻¹))))))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) → ((P N) = (∏ n_1 ∈ Finset.Icc (1 : ℕ) N, (p n_1))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) > 0))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((Real.log (p n)) = ((1 /. n) * (Real.log ((n : ℝ) ^ ((-(1 : ℤ)) ^ n))))))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((Real.log (p n)) = ((((-(1 : ℤ)) ^ n) /. n) * (Real.log (n : ℝ)))))))
  (h6 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) * ((Real.log (n : ℝ)) /. n)) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((((-(1 : ℤ)) ^ n) * ((Real.log (n : ℝ)) /. n)))‖ else 0))
  : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (Real.log (p n)) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((Real.log (p n)))‖ else 0) := by
  sorry

theorem proof_gap_exercise_3094_6
  (P : (ℕ -> ℝ))
  (p : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) = (Real.rpow ((n : ℝ) ^ ((-(1 : ℤ)) ^ n)) (((n : ℝ))⁻¹))))))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) → ((P N) = (∏ n_1 ∈ Finset.Icc (1 : ℕ) N, (p n_1))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) > 0))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((Real.log (p n)) = ((1 /. n) * (Real.log ((n : ℝ) ^ ((-(1 : ℤ)) ^ n))))))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((Real.log (p n)) = ((((-(1 : ℤ)) ^ n) /. n) * (Real.log (n : ℝ)))))))
  (h6 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) * ((Real.log (n : ℝ)) /. n)) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((((-(1 : ℤ)) ^ n) * ((Real.log (n : ℝ)) /. n)))‖ else 0))
  (h7 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (Real.log (p n)) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((Real.log (p n)))‖ else 0))
  : (∃ l, Filter.Tendsto P Filter.atTop (𝓝 l)) := by
  sorry

theorem proof_gap_exercise_3094_7
  (P : (ℕ -> ℝ))
  (p : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) = (Real.rpow ((n : ℝ) ^ ((-(1 : ℤ)) ^ n)) (((n : ℝ))⁻¹))))))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) → ((P N) = (∏ n_1 ∈ Finset.Icc (1 : ℕ) N, (p n_1))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) > 0))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((Real.log (p n)) = ((1 /. n) * (Real.log ((n : ℝ) ^ ((-(1 : ℤ)) ^ n))))))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((Real.log (p n)) = ((((-(1 : ℤ)) ^ n) /. n) * (Real.log (n : ℝ)))))))
  (h6 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) * ((Real.log (n : ℝ)) /. n)) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((((-(1 : ℤ)) ^ n) * ((Real.log (n : ℝ)) /. n)))‖ else 0))
  (h7 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (Real.log (p n)) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((Real.log (p n)))‖ else 0))
  (h8 : (∃ l, Filter.Tendsto P Filter.atTop (𝓝 l)))
  : (∃ l, Filter.Tendsto P Filter.atTop (𝓝 l)) := by
  sorry

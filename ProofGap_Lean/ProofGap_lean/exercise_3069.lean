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

-- exercise: exercise_3069

theorem proof_gap_exercise_3069_1
  (a : (ℕ -> ℝ))
  (P : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((a n) = (1 - (1 /. n))))))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (i : ℕ), ((((i ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((P n) = (∏' i_1, if (((i_1 ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (i_1 ≥ 2)) ∧ (i_1 ≤ n)) then (a i_1) else 1)))))))
  : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → (((a n) - 1) = (-(1 /. n))))) := by
  sorry

theorem proof_gap_exercise_3069_2
  (a : (ℕ -> ℝ))
  (P : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((a n) = (1 - (1 /. n))))))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (i : ℕ), ((((i ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((P n) = (∏' i_1, if (((i_1 ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (i_1 ≥ 2)) ∧ (i_1 ≤ n)) then (a i_1) else 1)))))))
  (h3 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → (((a n) - 1) = (-(1 /. n))))))
  : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((-(1 /. n)) < 0))) := by
  sorry

theorem proof_gap_exercise_3069_3
  (a : (ℕ -> ℝ))
  (P : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((a n) = (1 - (1 /. n))))))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (i : ℕ), ((((i ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((P n) = (∏' i_1, if (((i_1 ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (i_1 ≥ 2)) ∧ (i_1 ≤ n)) then (a i_1) else 1)))))))
  (h3 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → (((a n) - 1) = (-(1 /. n))))))
  (h4 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((-(1 /. n)) < 0))))
  : ¬ Summable (fun (n : ℕ) => if (n ∈ ({n_1 : ℕ | 0 < n_1})) then (-(1 /. n)) else 0) := by
  sorry

theorem proof_gap_exercise_3069_4
  (a : (ℕ -> ℝ))
  (P : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((a n) = (1 - (1 /. n))))))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (i : ℕ), ((((i ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((P n) = (∏' i_1, if (((i_1 ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (i_1 ≥ 2)) ∧ (i_1 ≤ n)) then (a i_1) else 1)))))))
  (h3 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → (((a n) - 1) = (-(1 /. n))))))
  (h4 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((-(1 /. n)) < 0))))
  (h5 : ¬ Summable (fun (n : ℕ) => if (n ∈ ({n_1 : ℕ | 0 < n_1})) then (-(1 /. n)) else 0))
  : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((P n) = (1 /. n)))) := by
  sorry

theorem proof_gap_exercise_3069_5
  (a : (ℕ -> ℝ))
  (P : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((a n) = (1 - (1 /. n))))))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (i : ℕ), ((((i ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((P n) = (∏' i_1, if (((i_1 ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (i_1 ≥ 2)) ∧ (i_1 ≤ n)) then (a i_1) else 1)))))))
  (h3 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → (((a n) - 1) = (-(1 /. n))))))
  (h4 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((-(1 /. n)) < 0))))
  (h5 : ¬ Summable (fun (n : ℕ) => if (n ∈ ({n_1 : ℕ | 0 < n_1})) then (-(1 /. n)) else 0))
  (h6 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((P n) = (1 /. n)))))
  : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (Tendsto (fun n_1 : ℕ => (P n_1)) atTop (𝓝 0)))) := by
  sorry

theorem proof_gap_exercise_3069_6
  (a : (ℕ -> ℝ))
  (P : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((a n) = (1 - (1 /. n))))))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (i : ℕ), ((((i ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((P n) = (∏' i_1, if (((i_1 ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (i_1 ≥ 2)) ∧ (i_1 ≤ n)) then (a i_1) else 1)))))))
  (h3 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → (((a n) - 1) = (-(1 /. n))))))
  (h4 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((-(1 /. n)) < 0))))
  (h5 : ¬ Summable (fun (n : ℕ) => if (n ∈ ({n_1 : ℕ | 0 < n_1})) then (-(1 /. n)) else 0))
  (h6 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((P n) = (1 /. n)))))
  (h7 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (Tendsto (fun n_1 : ℕ => (P n_1)) atTop (𝓝 0)))))
  : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (Not (exists (L : ℝ), (((L ∈ (Set.univ : Set ℝ)) ∧ (L ≠ 0)) ∧ (Tendsto (fun n_1 : ℕ => (P n_1)) atTop (𝓝 L))))))) := by
  sorry

theorem proof_gap_exercise_3069_7
  (a : (ℕ -> ℝ))
  (P : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((a n) = (1 - (1 /. n))))))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (i : ℕ), ((((i ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((P n) = (∏' i_1, if (((i_1 ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (i_1 ≥ 2)) ∧ (i_1 ≤ n)) then (a i_1) else 1)))))))
  (h3 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → (((a n) - 1) = (-(1 /. n))))))
  (h4 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((-(1 /. n)) < 0))))
  (h5 : ¬ Summable (fun (n : ℕ) => if (n ∈ ({n_1 : ℕ | 0 < n_1})) then (-(1 /. n)) else 0))
  (h6 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((P n) = (1 /. n)))))
  (h7 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (Tendsto (fun n_1 : ℕ => (P n_1)) atTop (𝓝 0)))))
  (h8 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (Not (exists (L : ℝ), (((L ∈ (Set.univ : Set ℝ)) ∧ (L ≠ 0)) ∧ (Tendsto (fun n_1 : ℕ => (P n_1)) atTop (𝓝 L))))))))
  : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (Not (exists (L : ℝ), (((L ∈ (Set.univ : Set ℝ)) ∧ (L ≠ 0)) ∧ (Tendsto (fun n_1 : ℕ => (P n_1)) atTop (𝓝 L))))))) := by
  sorry

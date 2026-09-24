import Mathlib

attribute [local instance] Classical.propDecidable

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

-- exercise: exercise_3065_2

theorem proof_gap_exercise_3065_2_1
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (P : ℝ)
  (h1 : P ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1))) → (((Q : ℕ → _) n) = (∏ k ∈ Finset.Icc (1 : ℕ) n, ((p k) ^ (2 : ℕ))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((Q n) = ((∏ k ∈ Finset.Icc (1 : ℕ) n, (p k)) ^ (2 : ℕ))))) := by
  sorry

theorem proof_gap_exercise_3065_2_2
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (P : ℝ)
  (h1 : P ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1))) → (((Q : ℕ → _) n) = (∏ k ∈ Finset.Icc (1 : ℕ) n, ((p k) ^ (2 : ℕ))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((Q n) = ((∏ k ∈ Finset.Icc (1 : ℕ) n, (p k)) ^ (2 : ℕ))))))
  : Tendsto (fun n : ℕ => (∏ k ∈ Finset.Icc (1 : ℕ) n, (p k))) atTop (𝓝 P) := by
  sorry

theorem proof_gap_exercise_3065_2_3
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (P : ℝ)
  (h1 : P ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1))) → (((Q : ℕ → _) n) = (∏ k ∈ Finset.Icc (1 : ℕ) n, ((p k) ^ (2 : ℕ))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((Q n) = ((∏ k ∈ Finset.Icc (1 : ℕ) n, (p k)) ^ (2 : ℕ))))))
  (h4 : Tendsto (fun n : ℕ => (∏ k ∈ Finset.Icc (1 : ℕ) n, (p k))) atTop (𝓝 P))
  : Tendsto (fun n : ℕ => (Q n)) atTop (𝓝 (P ^ (2 : ℕ))) := by
  sorry

theorem proof_gap_exercise_3065_2_4
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (P : ℝ)
  (h1 : P ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1))) → (((Q : ℕ → _) n) = (∏ k ∈ Finset.Icc (1 : ℕ) n, ((p k) ^ (2 : ℕ))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((Q n) = ((∏ k ∈ Finset.Icc (1 : ℕ) n, (p k)) ^ (2 : ℕ))))))
  (h4 : Tendsto (fun n : ℕ => (∏ k ∈ Finset.Icc (1 : ℕ) n, (p k))) atTop (𝓝 P))
  (h5 : Tendsto (fun n : ℕ => (Q n)) atTop (𝓝 (P ^ (2 : ℕ))))
  : (let _ : ∀ᶠ n in (Filter.atTop : Filter ℕ), n ∈ ({ x : ℕ | ((x ∈ (Set.univ : Set ℕ)) ∧ (x ≥ 1)) }) := (by filter_upwards [Filter.eventually_gt_atTop (1 : ℕ)] with n hn; simp only [Set.mem_ofPred_eq, Set.mem_univ, true_and, and_true]; omega); Filter.Tendsto (fun (n : ℕ) => (∏ k ∈ Finset.Icc (1 : ℕ) n, ((p k) ^ (2 : ℕ)))) Filter.atTop (𝓝 (P ^ (2 : ℕ)))) := by
  sorry

theorem proof_gap_exercise_3065_2_5
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (P : ℝ)
  (h1 : P ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1))) → (((Q : ℕ → _) n) = (∏ k ∈ Finset.Icc (1 : ℕ) n, ((p k) ^ (2 : ℕ))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((Q n) = ((∏ k ∈ Finset.Icc (1 : ℕ) n, (p k)) ^ (2 : ℕ))))))
  (h4 : Tendsto (fun n : ℕ => (∏ k ∈ Finset.Icc (1 : ℕ) n, (p k))) atTop (𝓝 P))
  (h5 : Tendsto (fun n : ℕ => (Q n)) atTop (𝓝 (P ^ (2 : ℕ))))
  (h6 : (let _ : ∀ᶠ n in (Filter.atTop : Filter ℕ), n ∈ ({ x : ℕ | ((x ∈ (Set.univ : Set ℕ)) ∧ (x ≥ 1)) }) := (by filter_upwards [Filter.eventually_gt_atTop (1 : ℕ)] with n hn; simp only [Set.mem_ofPred_eq, Set.mem_univ, true_and, and_true]; omega); Filter.Tendsto (fun (n : ℕ) => (∏ k ∈ Finset.Icc (1 : ℕ) n, ((p k) ^ (2 : ℕ)))) Filter.atTop (𝓝 (P ^ (2 : ℕ)))))
  : (forall (p_1 : (ℕ -> ℝ)) (q_1 : (ℕ -> ℝ)) (P_1 : ℝ), (((((True ∧ (P_1 ∈ (Set.univ : Set ℝ))) ∧ (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((((p_1 n) ∈ (Set.univ : Set ℝ)) ∧ ((q_1 n) ∈ (Set.univ : Set ℝ))) ∧ ((p_1 n) ≠ 0)) ∧ ((q_1 n) ≠ 0))))) ∧ (let _ : ∀ᶠ n in (Filter.atTop : Filter ℕ), n ∈ ({ x : ℕ | ((x ∈ (Set.univ : Set ℕ)) ∧ (x ≥ 1)) }) := (by filter_upwards [Filter.eventually_gt_atTop (1 : ℕ)] with n hn; simp only [Set.mem_ofPred_eq, Set.mem_univ, true_and, and_true]; omega); Filter.Tendsto (fun (n : ℕ) => (∏ k ∈ Finset.Icc (1 : ℕ) n, (p_1 k))) Filter.atTop (𝓝 P_1))) ∧ (P_1 ≠ 0)) → (let _ : ∀ᶠ n in (Filter.atTop : Filter ℕ), n ∈ ({ x : ℕ | ((x ∈ (Set.univ : Set ℕ)) ∧ (x ≥ 1)) }) := (by filter_upwards [Filter.eventually_gt_atTop (1 : ℕ)] with n hn; simp only [Set.mem_ofPred_eq, Set.mem_univ, true_and, and_true]; omega); Filter.Tendsto (fun (n : ℕ) => (∏ k ∈ Finset.Icc (1 : ℕ) n, ((p_1 k) ^ (2 : ℕ)))) Filter.atTop (𝓝 (P_1 ^ (2 : ℕ)))))) := by
  sorry

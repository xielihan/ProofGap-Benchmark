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

-- exercise: exercise_147

theorem proof_gap_exercise_147_1
  (v_uCE_uB5 : (ℕ -> ℝ))
  (C : ℝ)
  (k : ℕ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : k ∈ (Set.univ : Set ℕ))
  (h3 : (forall (n : ℕ), ((n ∈ ({n_1 : ℕ | 0 < n_1})) → ((v_uCE_uB5 n) = (((∑ k_1 ∈ Finset.Icc (1 : ℕ) n, (1 /. k_1)) - C) - (Real.log (n : ℝ)))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k_1 ∈ Finset.Icc (1 : ℕ) n, (1 /. k_1)) = ((C + (Real.log (n : ℝ))) + (v_uCE_uB5 n))))) := by
  sorry

theorem proof_gap_exercise_147_2
  (v_uCE_uB5 : (ℕ -> ℝ))
  (C : ℝ)
  (k : ℕ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : k ∈ (Set.univ : Set ℕ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k_1 ∈ Finset.Icc (1 : ℕ) n, (1 /. k_1)) = ((C + (Real.log (n : ℝ))) + (v_uCE_uB5 n))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k_1 ∈ Finset.Icc (1 : ℕ) (2 * n), (1 /. k_1)) = ((C + (Real.log (2 * n))) + (v_uCE_uB5 (2 * n)))))) := by
  sorry

theorem proof_gap_exercise_147_3
  (v_uCE_uB5 : (ℕ -> ℝ))
  (C : ℝ)
  (k : ℕ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : k ∈ (Set.univ : Set ℕ))
  (h3 : (forall (n : ℕ), ((n ∈ ({n_1 : ℕ | 0 < n_1})) → ((∑ k_1 ∈ Finset.Icc (1 : ℕ) n, (1 /. k_1)) = ((C + (Real.log (n : ℝ))) + (v_uCE_uB5 n))))))
  (h4 : (forall (n : ℕ), ((n ∈ ({n_1 : ℕ | 0 < n_1})) → ((∑ k_1 ∈ Finset.Icc (1 : ℕ) (2 * n), (1 /. k_1)) = ((C + (Real.log (2 * n))) + (v_uCE_uB5 (2 * n)))))))
  (h5 : Tendsto (fun n : ℕ => ((∑ k_1 ∈ Finset.Icc (1 : ℕ) n, (1 /. k_1)) - (Real.log n))) atTop (𝓝 C))
  : Tendsto (fun n : ℕ => (v_uCE_uB5 n)) atTop (𝓝 0) := by
  sorry

theorem proof_gap_exercise_147_4
  (v_uCE_uB5 : (ℕ -> ℝ))
  (C : ℝ)
  (k : ℕ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : k ∈ (Set.univ : Set ℕ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k_1 ∈ Finset.Icc (1 : ℕ) n, (1 /. k_1)) = ((C + (Real.log (n : ℝ))) + (v_uCE_uB5 n))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k_1 ∈ Finset.Icc (1 : ℕ) (2 * n), (1 /. k_1)) = ((C + (Real.log (2 * n))) + (v_uCE_uB5 (2 * n)))))))
  (h5 : Tendsto (fun n : ℕ => (v_uCE_uB5 n)) atTop (𝓝 0))
  : Tendsto (fun n : ℕ => (v_uCE_uB5 (2 * n))) atTop (𝓝 0) := by
  sorry

theorem proof_gap_exercise_147_5
  (v_uCE_uB5 : (ℕ -> ℝ))
  (C : ℝ)
  (k : ℕ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : k ∈ (Set.univ : Set ℕ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k_1 ∈ Finset.Icc (1 : ℕ) n, (1 /. k_1)) = ((C + (Real.log (n : ℝ))) + (v_uCE_uB5 n))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k_1 ∈ Finset.Icc (1 : ℕ) (2 * n), (1 /. k_1)) = ((C + (Real.log (2 * n))) + (v_uCE_uB5 (2 * n)))))))
  (h5 : Tendsto (fun n : ℕ => (v_uCE_uB5 n)) atTop (𝓝 0))
  (h6 : Tendsto (fun n : ℕ => (v_uCE_uB5 (2 * n))) atTop (𝓝 0))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k_1 ∈ Finset.Icc (n + 1) (2 * n), (1 /. k_1)) = ((((Real.log (2 * n)) - (Real.log (n : ℝ))) + (v_uCE_uB5 (2 * n))) - (v_uCE_uB5 n))))) := by
  sorry

theorem proof_gap_exercise_147_6
  (v_uCE_uB5 : (ℕ -> ℝ))
  (C : ℝ)
  (k : ℕ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : k ∈ (Set.univ : Set ℕ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k_1 ∈ Finset.Icc (1 : ℕ) n, (1 /. k_1)) = ((C + (Real.log (n : ℝ))) + (v_uCE_uB5 n))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k_1 ∈ Finset.Icc (1 : ℕ) (2 * n), (1 /. k_1)) = ((C + (Real.log (2 * n))) + (v_uCE_uB5 (2 * n)))))))
  (h5 : Tendsto (fun n : ℕ => (v_uCE_uB5 n)) atTop (𝓝 0))
  (h6 : Tendsto (fun n : ℕ => (v_uCE_uB5 (2 * n))) atTop (𝓝 0))
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k_1 ∈ Finset.Icc (n + 1) (2 * n), (1 /. k_1)) = ((((Real.log (2 * n)) - (Real.log (n : ℝ))) + (v_uCE_uB5 (2 * n))) - (v_uCE_uB5 n))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k_1 ∈ Finset.Icc (n + 1) (2 * n), (1 /. k_1)) = (((Real.log (2 : ℝ)) + (v_uCE_uB5 (2 * n))) - (v_uCE_uB5 n))))) := by
  sorry

theorem proof_gap_exercise_147_7
  (v_uCE_uB5 : (ℕ -> ℝ))
  (C : ℝ)
  (k : ℕ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : k ∈ (Set.univ : Set ℕ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k_1 ∈ Finset.Icc (1 : ℕ) n, (1 /. k_1)) = ((C + (Real.log (n : ℝ))) + (v_uCE_uB5 n))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k_1 ∈ Finset.Icc (1 : ℕ) (2 * n), (1 /. k_1)) = ((C + (Real.log (2 * n))) + (v_uCE_uB5 (2 * n)))))))
  (h5 : Tendsto (fun n : ℕ => (v_uCE_uB5 n)) atTop (𝓝 0))
  (h6 : Tendsto (fun n : ℕ => (v_uCE_uB5 (2 * n))) atTop (𝓝 0))
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k_1 ∈ Finset.Icc (n + 1) (2 * n), (1 /. k_1)) = ((((Real.log (2 * n)) - (Real.log (n : ℝ))) + (v_uCE_uB5 (2 * n))) - (v_uCE_uB5 n))))))
  (h8 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k_1 ∈ Finset.Icc (n + 1) (2 * n), (1 /. k_1)) = (((Real.log (2 : ℝ)) + (v_uCE_uB5 (2 * n))) - (v_uCE_uB5 n))))))
  : Tendsto (fun n : ℕ => (∑ k_1 ∈ Finset.Icc (n + 1) (2 * n), (1 /. k_1))) atTop (𝓝 (Real.log (2 : ℝ))) := by
  sorry

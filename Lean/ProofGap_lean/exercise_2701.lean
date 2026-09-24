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

-- exercise: exercise_2701

theorem proof_gap_exercise_2701_1
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1))) → (((a : ℕ → _) n) = (((-(1 : ℤ)) ^ n) /. (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1))) → (((b : ℕ → _) n) = ((((-(1 : ℤ)) ^ n) /. (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))) + (1 /. n)))))
  : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0) := by
  sorry

theorem proof_gap_exercise_2701_2
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1))) → (((a : ℕ → _) n) = (((-(1 : ℤ)) ^ n) /. (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1))) → (((b : ℕ → _) n) = ((((-(1 : ℤ)) ^ n) /. (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))) + (1 /. n)))))
  (h3 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0))
  : Tendsto (fun n : ℕ => ((b n) /. (a n))) atTop (𝓝 1) := by
  sorry

theorem proof_gap_exercise_2701_3
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1))) → (((a : ℕ → _) n) = (((-(1 : ℤ)) ^ n) /. (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1))) → (((b : ℕ → _) n) = ((((-(1 : ℤ)) ^ n) /. (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))) + (1 /. n)))))
  (h3 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0))
  (h4 : Tendsto (fun n : ℕ => ((b n) /. (a n))) atTop (𝓝 1))
  : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. n) else 0) := by
  sorry

theorem proof_gap_exercise_2701_4
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1))) → (((a : ℕ → _) n) = (((-(1 : ℤ)) ^ n) /. (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1))) → (((b : ℕ → _) n) = ((((-(1 : ℤ)) ^ n) /. (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))) + (1 /. n)))))
  (h3 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0))
  (h4 : Tendsto (fun n : ℕ => ((b n) /. (a n))) atTop (𝓝 1))
  (h5 : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. n) else 0))
  : (∑' n, if (1 : ℕ) ≤ n then (b n) else 0) = ((∑' n, if (1 : ℕ) ≤ n then (a n) else 0) + (∑' n, if (1 : ℕ) ≤ n then (1 /. n) else 0)) := by
  sorry

theorem proof_gap_exercise_2701_5
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1))) → (((a : ℕ → _) n) = (((-(1 : ℤ)) ^ n) /. (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1))) → (((b : ℕ → _) n) = ((((-(1 : ℤ)) ^ n) /. (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))) + (1 /. n)))))
  (h3 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0))
  (h4 : Tendsto (fun n : ℕ => ((b n) /. (a n))) atTop (𝓝 1))
  (h5 : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. n) else 0))
  (h6 : (∑' n, if (1 : ℕ) ≤ n then (b n) else 0) = ((∑' n, if (1 : ℕ) ≤ n then (a n) else 0) + (∑' n, if (1 : ℕ) ≤ n then (1 /. n) else 0)))
  : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (b n) else 0) := by
  sorry

theorem proof_gap_exercise_2701_6
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1))) → (((a : ℕ → _) n) = (((-(1 : ℤ)) ^ n) /. (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1))) → (((b : ℕ → _) n) = ((((-(1 : ℤ)) ^ n) /. (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))) + (1 /. n)))))
  (h3 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0))
  (h4 : Tendsto (fun n : ℕ => ((b n) /. (a n))) atTop (𝓝 1))
  (h5 : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. n) else 0))
  (h6 : (∑' n, if (1 : ℕ) ≤ n then (b n) else 0) = ((∑' n, if (1 : ℕ) ≤ n then (a n) else 0) + (∑' n, if (1 : ℕ) ≤ n then (1 /. n) else 0)))
  (h7 : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (b n) else 0))
  : Not (forall (a : (ℕ -> ℝ)) (b : (ℕ -> ℝ)), ((((True ∧ (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((((a n) ∈ (Set.univ : Set ℝ)) ∧ ((b n) ∈ (Set.univ : Set ℝ))) ∧ ((a n) ≠ 0))))) ∧ (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0))) ∧ (Tendsto (fun n : ℕ => ((b n) /. (a n))) atTop (𝓝 1))) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (b n) else 0)))) := by
  sorry

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

-- exercise: exercise_2547

theorem proof_gap_exercise_2547_1
  (S : (ℕ -> ℝ))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = (∑ i ∈ Finset.Icc (1 : ℕ) n, ((1 /. ((2 : ℕ) ^ i)) + (1 /. ((3 : ℕ) ^ i))))))) := by
  sorry

theorem proof_gap_exercise_2547_2
  (S : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = (∑ i ∈ Finset.Icc (1 : ℕ) n, ((1 /. ((2 : ℕ) ^ i)) + (1 /. ((3 : ℕ) ^ i))))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = ((∑ i ∈ Finset.Icc (1 : ℕ) n, (1 /. ((2 : ℕ) ^ i))) + (∑ i ∈ Finset.Icc (1 : ℕ) n, (1 /. ((3 : ℕ) ^ i))))))) := by
  sorry

theorem proof_gap_exercise_2547_3
  (S : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = (∑ i ∈ Finset.Icc (1 : ℕ) n, ((1 /. ((2 : ℕ) ^ i)) + (1 /. ((3 : ℕ) ^ i))))))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = ((∑ i ∈ Finset.Icc (1 : ℕ) n, (1 /. ((2 : ℕ) ^ i))) + (∑ i ∈ Finset.Icc (1 : ℕ) n, (1 /. ((3 : ℕ) ^ i))))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = (((1 /. 2) * ((1 - (1 /. ((2 : ℕ) ^ n))) /. (1 - (1 /. 2)))) + ((1 /. 3) * ((1 - (1 /. ((3 : ℕ) ^ n))) /. (1 - (1 /. 3)))))))) := by
  sorry

theorem proof_gap_exercise_2547_4
  (S : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = (∑ i ∈ Finset.Icc (1 : ℕ) n, ((1 /. ((2 : ℕ) ^ i)) + (1 /. ((3 : ℕ) ^ i))))))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = ((∑ i ∈ Finset.Icc (1 : ℕ) n, (1 /. ((2 : ℕ) ^ i))) + (∑ i ∈ Finset.Icc (1 : ℕ) n, (1 /. ((3 : ℕ) ^ i))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = (((1 /. 2) * ((1 - (1 /. ((2 : ℕ) ^ n))) /. (1 - (1 /. 2)))) + ((1 /. 3) * ((1 - (1 /. ((3 : ℕ) ^ n))) /. (1 - (1 /. 3)))))))))
  : Tendsto (fun n : ℕ => (S n)) atTop (𝓝 (((1 /. 2) * (1 /. (1 - (1 /. 2)))) + ((1 /. 3) * (1 /. (1 - (1 /. 3)))))) := by
  sorry

theorem proof_gap_exercise_2547_5
  (S : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = (∑ i ∈ Finset.Icc (1 : ℕ) n, ((1 /. ((2 : ℕ) ^ i)) + (1 /. ((3 : ℕ) ^ i))))))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = ((∑ i ∈ Finset.Icc (1 : ℕ) n, (1 /. ((2 : ℕ) ^ i))) + (∑ i ∈ Finset.Icc (1 : ℕ) n, (1 /. ((3 : ℕ) ^ i))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = (((1 /. 2) * ((1 - (1 /. ((2 : ℕ) ^ n))) /. (1 - (1 /. 2)))) + ((1 /. 3) * ((1 - (1 /. ((3 : ℕ) ^ n))) /. (1 - (1 /. 3)))))))))
  (h4 : Tendsto (fun n : ℕ => (S n)) atTop (𝓝 (((1 /. 2) * (1 /. (1 - (1 /. 2)))) + ((1 /. 3) * (1 /. (1 - (1 /. 3)))))))
  : Tendsto (fun n : ℕ => (S n)) atTop (𝓝 (3 /. 2)) := by
  sorry

theorem proof_gap_exercise_2547_6
  (S : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = (∑ i ∈ Finset.Icc (1 : ℕ) n, ((1 /. ((2 : ℕ) ^ i)) + (1 /. ((3 : ℕ) ^ i))))))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = ((∑ i ∈ Finset.Icc (1 : ℕ) n, (1 /. ((2 : ℕ) ^ i))) + (∑ i ∈ Finset.Icc (1 : ℕ) n, (1 /. ((3 : ℕ) ^ i))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = (((1 /. 2) * ((1 - (1 /. ((2 : ℕ) ^ n))) /. (1 - (1 /. 2)))) + ((1 /. 3) * ((1 - (1 /. ((3 : ℕ) ^ n))) /. (1 - (1 /. 3)))))))))
  (h4 : Tendsto (fun n : ℕ => (S n)) atTop (𝓝 (((1 /. 2) * (1 /. (1 - (1 /. 2)))) + ((1 /. 3) * (1 /. (1 - (1 /. 3)))))))
  (h5 : Tendsto (fun n : ℕ => (S n)) atTop (𝓝 (3 /. 2)))
  : HasSum (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((1 /. ((2 : ℕ) ^ n)) + (1 /. ((3 : ℕ) ^ n))) else 0) (3 /. 2) := by
  sorry

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

-- exercise: exercise_2739_1

theorem proof_gap_exercise_2739_1_1
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∏ k ∈ Finset.Icc (0 : ℕ) (n - 1), (x - k)) = (x * (∏ k ∈ Finset.Icc (1 : ℕ) (n - 1), (x - k)))))) := by
  sorry

theorem proof_gap_exercise_2739_1_2
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∏ k ∈ Finset.Icc (0 : ℕ) (n - 1), (x - k)) = (x * (∏ k ∈ Finset.Icc (1 : ℕ) (n - 1), (x - k)))))))
  : (x ≥ 0) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖(((∏ k ∈ Finset.Icc (0 : ℕ) (n - 1), (x - k)) /. (n)!))‖ else 0)) := by
  sorry

theorem proof_gap_exercise_2739_1_3
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∏ k ∈ Finset.Icc (0 : ℕ) (n - 1), (x - k)) = (x * (∏ k ∈ Finset.Icc (1 : ℕ) (n - 1), (x - k)))))))
  (h3 : (x ≥ 0) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖(((∏ k ∈ Finset.Icc (0 : ℕ) (n - 1), (x - k)) /. (n)!))‖ else 0)))
  : (((-(1 : ℝ)) < x) ∧ (x < 0)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((∏ k ∈ Finset.Icc (0 : ℕ) (n - 1), (x - k)) /. (n)!) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖(((∏ k ∈ Finset.Icc (0 : ℕ) (n - 1), (x - k)) /. (n)!))‖ else 0)) := by
  sorry

theorem proof_gap_exercise_2739_1_4
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∏ k ∈ Finset.Icc (0 : ℕ) (n - 1), (x - k)) = (x * (∏ k ∈ Finset.Icc (1 : ℕ) (n - 1), (x - k)))))))
  (h3 : (x ≥ 0) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖(((∏ k ∈ Finset.Icc (0 : ℕ) (n - 1), (x - k)) /. (n)!))‖ else 0)))
  (h4 : (((-(1 : ℝ)) < x) ∧ (x < 0)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((∏ k ∈ Finset.Icc (0 : ℕ) (n - 1), (x - k)) /. (n)!) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖(((∏ k ∈ Finset.Icc (0 : ℕ) (n - 1), (x - k)) /. (n)!))‖ else 0)))
  : (x ∈ ({x_1 | (x_1 ∈ (Set.univ : Set ℝ)) ∧ (((x_1 ≥ 0) ∧ (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖(((∏ k ∈ Finset.Icc (0 : ℕ) (n - 1), (x_1 - k)) /. (n)!))‖ else 0))) ∨ ((((-(1 : ℝ)) < x_1) ∧ (x_1 < 0)) ∧ (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((∏ k ∈ Finset.Icc (0 : ℕ) (n - 1), (x_1 - k)) /. (n)!) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖(((∏ k ∈ Finset.Icc (0 : ℕ) (n - 1), (x_1 - k)) /. (n)!))‖ else 0))))})) ↔ ((Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖(((∏ k ∈ Finset.Icc (0 : ℕ) (n - 1), (x - k)) /. (n)!))‖ else 0)) ∧ (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((∏ k ∈ Finset.Icc (0 : ℕ) (n - 1), (x - k)) /. (n)!) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖(((∏ k ∈ Finset.Icc (0 : ℕ) (n - 1), (x - k)) /. (n)!))‖ else 0))) := by
  sorry

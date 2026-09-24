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

-- exercise: exercise_3063

theorem proof_gap_exercise_3063_1
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1))) → (((P : ℕ → _) n) = (∏ k ∈ Finset.Icc (1 : ℕ) n, ((((2 * k) + 1) * ((2 * k) + 7)) /. (((2 * k) + 3) * ((2 * k) + 5)))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) → ((P n) = ((3 /. 7) * (((2 * n) + 7) /. ((2 * n) + 3)))))) := by
  sorry

theorem proof_gap_exercise_3063_2
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1))) → (((P : ℕ → _) n) = (∏ k ∈ Finset.Icc (1 : ℕ) n, ((((2 * k) + 1) * ((2 * k) + 7)) /. (((2 * k) + 3) * ((2 * k) + 5)))))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) → ((P n) = ((3 /. 7) * (((2 * n) + 7) /. ((2 * n) + 3)))))))
  : Tendsto (fun n : ℕ => (P n)) atTop (𝓝 (3 /. 7)) := by
  sorry

theorem proof_gap_exercise_3063_3
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1))) → (((P : ℕ → _) n) = (∏ k ∈ Finset.Icc (1 : ℕ) n, ((((2 * k) + 1) * ((2 * k) + 7)) /. (((2 * k) + 3) * ((2 * k) + 5)))))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) → ((P n) = ((3 /. 7) * (((2 * n) + 7) /. ((2 * n) + 3)))))))
  (h3 : Tendsto (fun n : ℕ => (P n)) atTop (𝓝 (3 /. 7)))
  : (∏' n, if (1 : ℕ) ≤ n then ((((2 * n) + 1) * ((2 * n) + 7)) /. (((2 * n) + 3) * ((2 * n) + 5))) else 1) = (3 /. 7) := by
  sorry

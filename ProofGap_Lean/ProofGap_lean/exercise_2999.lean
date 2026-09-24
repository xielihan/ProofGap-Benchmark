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

-- exercise: exercise_2999

theorem proof_gap_exercise_2999_1
  : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (((((-(1 : ℤ)) ^ n) * n) /. (((2 * n) + 1))!) = ((((-(1 : ℤ)) ^ n) /. 2) * ((1 /. ((2 * n))!) - (1 /. (((2 * n) + 1))!)))))) := by
  sorry

theorem proof_gap_exercise_2999_2
  (h1 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (((((-(1 : ℤ)) ^ n) * n) /. (((2 * n) + 1))!) = ((((-(1 : ℤ)) ^ n) /. 2) * ((1 /. ((2 * n))!) - (1 /. (((2 * n) + 1))!)))))))
  : Summable (fun (n : ℕ) => if (0 : ℕ) ≤ n then ‖(((((-(1 : ℤ)) ^ n) * n) /. (((2 * n) + 1))!))‖ else 0) := by
  sorry

theorem proof_gap_exercise_2999_3
  (h1 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (((((-(1 : ℤ)) ^ n) * n) /. (((2 * n) + 1))!) = ((((-(1 : ℤ)) ^ n) /. 2) * ((1 /. ((2 * n))!) - (1 /. (((2 * n) + 1))!)))))))
  (h2 : Summable (fun (n : ℕ) => if (0 : ℕ) ≤ n then ‖(((((-(1 : ℤ)) ^ n) * n) /. (((2 * n) + 1))!))‖ else 0))
  : (∑' n, if (0 : ℕ) ≤ n then ((((-(1 : ℤ)) ^ n) * n) /. (((2 * n) + 1))!) else 0) = ((1 /. 2) * ((∑' n, if (0 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) /. ((2 * n))!) else 0) - (∑' n, if (0 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) /. (((2 * n) + 1))!) else 0))) := by
  sorry

theorem proof_gap_exercise_2999_4
  (h1 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (((((-(1 : ℤ)) ^ n) * n) /. (((2 * n) + 1))!) = ((((-(1 : ℤ)) ^ n) /. 2) * ((1 /. ((2 * n))!) - (1 /. (((2 * n) + 1))!)))))))
  (h2 : Summable (fun (n : ℕ) => if (0 : ℕ) ≤ n then ‖(((((-(1 : ℤ)) ^ n) * n) /. (((2 * n) + 1))!))‖ else 0))
  (h3 : (∑' n, if (0 : ℕ) ≤ n then ((((-(1 : ℤ)) ^ n) * n) /. (((2 * n) + 1))!) else 0) = ((1 /. 2) * ((∑' n, if (0 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) /. ((2 * n))!) else 0) - (∑' n, if (0 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) /. (((2 * n) + 1))!) else 0))))
  : (∑' n, if (0 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) /. ((2 * n))!) else 0) = (Real.cos (1 : ℝ)) := by
  sorry

theorem proof_gap_exercise_2999_5
  (h1 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (((((-(1 : ℤ)) ^ n) * n) /. (((2 * n) + 1))!) = ((((-(1 : ℤ)) ^ n) /. 2) * ((1 /. ((2 * n))!) - (1 /. (((2 * n) + 1))!)))))))
  (h2 : Summable (fun (n : ℕ) => if (0 : ℕ) ≤ n then ‖(((((-(1 : ℤ)) ^ n) * n) /. (((2 * n) + 1))!))‖ else 0))
  (h3 : (∑' n, if (0 : ℕ) ≤ n then ((((-(1 : ℤ)) ^ n) * n) /. (((2 * n) + 1))!) else 0) = ((1 /. 2) * ((∑' n, if (0 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) /. ((2 * n))!) else 0) - (∑' n, if (0 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) /. (((2 * n) + 1))!) else 0))))
  (h4 : (∑' n, if (0 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) /. ((2 * n))!) else 0) = (Real.cos (1 : ℝ)))
  : (∑' n, if (0 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) /. (((2 * n) + 1))!) else 0) = (Real.sin (1 : ℝ)) := by
  sorry

theorem proof_gap_exercise_2999_6
  (h1 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (((((-(1 : ℤ)) ^ n) * n) /. (((2 * n) + 1))!) = ((((-(1 : ℤ)) ^ n) /. 2) * ((1 /. ((2 * n))!) - (1 /. (((2 * n) + 1))!)))))))
  (h2 : Summable (fun (n : ℕ) => if (0 : ℕ) ≤ n then ‖(((((-(1 : ℤ)) ^ n) * n) /. (((2 * n) + 1))!))‖ else 0))
  (h3 : (∑' n, if (0 : ℕ) ≤ n then ((((-(1 : ℤ)) ^ n) * n) /. (((2 * n) + 1))!) else 0) = ((1 /. 2) * ((∑' n, if (0 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) /. ((2 * n))!) else 0) - (∑' n, if (0 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) /. (((2 * n) + 1))!) else 0))))
  (h4 : (∑' n, if (0 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) /. ((2 * n))!) else 0) = (Real.cos (1 : ℝ)))
  (h5 : (∑' n, if (0 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) /. (((2 * n) + 1))!) else 0) = (Real.sin (1 : ℝ)))
  : (∑' n, if (0 : ℕ) ≤ n then ((((-(1 : ℤ)) ^ n) * n) /. (((2 * n) + 1))!) else 0) = ((1 /. 2) * ((Real.cos (1 : ℝ)) - (Real.sin (1 : ℝ)))) := by
  sorry

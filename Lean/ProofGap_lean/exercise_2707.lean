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

-- exercise: exercise_2707

theorem proof_gap_exercise_2707_1
  : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((1 /. ((3 : ℕ) ^ n)) + (((-(1 : ℤ)) ^ n) /. (n ^ (3 : ℕ)))) else 0) := by
  sorry

theorem proof_gap_exercise_2707_2
  (h1 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((1 /. ((3 : ℕ) ^ n)) + (((-(1 : ℤ)) ^ n) /. (n ^ (3 : ℕ)))) else 0))
  : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((1 /. ((3 : ℕ) ^ (n + 1))) + (((-(1 : ℤ)) ^ (n + 1)) /. (n ^ (3 : ℕ)))) else 0) := by
  sorry

theorem proof_gap_exercise_2707_3
  (h1 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((1 /. ((3 : ℕ) ^ n)) + (((-(1 : ℤ)) ^ n) /. (n ^ (3 : ℕ)))) else 0))
  (h2 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((1 /. ((3 : ℕ) ^ (n + 1))) + (((-(1 : ℤ)) ^ (n + 1)) /. (n ^ (3 : ℕ)))) else 0))
  : ((∑' n, if (1 : ℕ) ≤ n then ((1 /. ((3 : ℕ) ^ n)) + (((-(1 : ℤ)) ^ n) /. (n ^ (3 : ℕ)))) else 0) + (∑' n, if (1 : ℕ) ≤ n then ((1 /. ((3 : ℕ) ^ (n + 1))) + (((-(1 : ℤ)) ^ (n + 1)) /. (n ^ (3 : ℕ)))) else 0)) = (∑' n, if (1 : ℕ) ≤ n then ((1 /. ((3 : ℕ) ^ n)) + (1 /. ((3 : ℕ) ^ (n + 1)))) else 0) := by
  sorry

theorem proof_gap_exercise_2707_4
  (h1 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((1 /. ((3 : ℕ) ^ n)) + (((-(1 : ℤ)) ^ n) /. (n ^ (3 : ℕ)))) else 0))
  (h2 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((1 /. ((3 : ℕ) ^ (n + 1))) + (((-(1 : ℤ)) ^ (n + 1)) /. (n ^ (3 : ℕ)))) else 0))
  (h3 : ((∑' n, if (1 : ℕ) ≤ n then ((1 /. ((3 : ℕ) ^ n)) + (((-(1 : ℤ)) ^ n) /. (n ^ (3 : ℕ)))) else 0) + (∑' n, if (1 : ℕ) ≤ n then ((1 /. ((3 : ℕ) ^ (n + 1))) + (((-(1 : ℤ)) ^ (n + 1)) /. (n ^ (3 : ℕ)))) else 0)) = (∑' n, if (1 : ℕ) ≤ n then ((1 /. ((3 : ℕ) ^ n)) + (1 /. ((3 : ℕ) ^ (n + 1)))) else 0))
  : (∑' n, if (1 : ℕ) ≤ n then ((1 /. ((3 : ℕ) ^ n)) + (1 /. ((3 : ℕ) ^ (n + 1)))) else 0) = (∑' n, if (1 : ℕ) ≤ n then (4 /. ((3 : ℕ) ^ (n + 1))) else 0) := by
  sorry

theorem proof_gap_exercise_2707_5
  (h1 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((1 /. ((3 : ℕ) ^ n)) + (((-(1 : ℤ)) ^ n) /. (n ^ (3 : ℕ)))) else 0))
  (h2 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((1 /. ((3 : ℕ) ^ (n + 1))) + (((-(1 : ℤ)) ^ (n + 1)) /. (n ^ (3 : ℕ)))) else 0))
  (h3 : ((∑' n, if (1 : ℕ) ≤ n then ((1 /. ((3 : ℕ) ^ n)) + (((-(1 : ℤ)) ^ n) /. (n ^ (3 : ℕ)))) else 0) + (∑' n, if (1 : ℕ) ≤ n then ((1 /. ((3 : ℕ) ^ (n + 1))) + (((-(1 : ℤ)) ^ (n + 1)) /. (n ^ (3 : ℕ)))) else 0)) = (∑' n, if (1 : ℕ) ≤ n then ((1 /. ((3 : ℕ) ^ n)) + (1 /. ((3 : ℕ) ^ (n + 1)))) else 0))
  (h4 : (∑' n, if (1 : ℕ) ≤ n then ((1 /. ((3 : ℕ) ^ n)) + (1 /. ((3 : ℕ) ^ (n + 1)))) else 0) = (∑' n, if (1 : ℕ) ≤ n then (4 /. ((3 : ℕ) ^ (n + 1))) else 0))
  : (∑' n, if (1 : ℕ) ≤ n then (4 /. ((3 : ℕ) ^ (n + 1))) else 0) = ((4 /. ((3 : ℕ) ^ (2 : ℕ))) * (1 /. (1 - (1 /. 3)))) := by
  sorry

theorem proof_gap_exercise_2707_6
  (h1 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((1 /. ((3 : ℕ) ^ n)) + (((-(1 : ℤ)) ^ n) /. (n ^ (3 : ℕ)))) else 0))
  (h2 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((1 /. ((3 : ℕ) ^ (n + 1))) + (((-(1 : ℤ)) ^ (n + 1)) /. (n ^ (3 : ℕ)))) else 0))
  (h3 : ((∑' n, if (1 : ℕ) ≤ n then ((1 /. ((3 : ℕ) ^ n)) + (((-(1 : ℤ)) ^ n) /. (n ^ (3 : ℕ)))) else 0) + (∑' n, if (1 : ℕ) ≤ n then ((1 /. ((3 : ℕ) ^ (n + 1))) + (((-(1 : ℤ)) ^ (n + 1)) /. (n ^ (3 : ℕ)))) else 0)) = (∑' n, if (1 : ℕ) ≤ n then ((1 /. ((3 : ℕ) ^ n)) + (1 /. ((3 : ℕ) ^ (n + 1)))) else 0))
  (h4 : (∑' n, if (1 : ℕ) ≤ n then ((1 /. ((3 : ℕ) ^ n)) + (1 /. ((3 : ℕ) ^ (n + 1)))) else 0) = (∑' n, if (1 : ℕ) ≤ n then (4 /. ((3 : ℕ) ^ (n + 1))) else 0))
  (h5 : (∑' n, if (1 : ℕ) ≤ n then (4 /. ((3 : ℕ) ^ (n + 1))) else 0) = ((4 /. ((3 : ℕ) ^ (2 : ℕ))) * (1 /. (1 - (1 /. 3)))))
  : ((4 /. ((3 : ℕ) ^ (2 : ℕ))) * (1 /. (1 - (1 /. 3)))) = (2 /. 3) := by
  sorry

theorem proof_gap_exercise_2707_7
  (h1 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((1 /. ((3 : ℕ) ^ n)) + (((-(1 : ℤ)) ^ n) /. (n ^ (3 : ℕ)))) else 0))
  (h2 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((1 /. ((3 : ℕ) ^ (n + 1))) + (((-(1 : ℤ)) ^ (n + 1)) /. (n ^ (3 : ℕ)))) else 0))
  (h3 : ((∑' n, if (1 : ℕ) ≤ n then ((1 /. ((3 : ℕ) ^ n)) + (((-(1 : ℤ)) ^ n) /. (n ^ (3 : ℕ)))) else 0) + (∑' n, if (1 : ℕ) ≤ n then ((1 /. ((3 : ℕ) ^ (n + 1))) + (((-(1 : ℤ)) ^ (n + 1)) /. (n ^ (3 : ℕ)))) else 0)) = (∑' n, if (1 : ℕ) ≤ n then ((1 /. ((3 : ℕ) ^ n)) + (1 /. ((3 : ℕ) ^ (n + 1)))) else 0))
  (h4 : (∑' n, if (1 : ℕ) ≤ n then ((1 /. ((3 : ℕ) ^ n)) + (1 /. ((3 : ℕ) ^ (n + 1)))) else 0) = (∑' n, if (1 : ℕ) ≤ n then (4 /. ((3 : ℕ) ^ (n + 1))) else 0))
  (h5 : (∑' n, if (1 : ℕ) ≤ n then (4 /. ((3 : ℕ) ^ (n + 1))) else 0) = ((4 /. ((3 : ℕ) ^ (2 : ℕ))) * (1 /. (1 - (1 /. 3)))))
  (h6 : ((4 /. ((3 : ℕ) ^ (2 : ℕ))) * (1 /. (1 - (1 /. 3)))) = (2 /. 3))
  : (∑' n, if (1 : ℕ) ≤ n then (4 /. ((3 : ℕ) ^ (n + 1))) else 0) = (2 /. 3) := by
  sorry

theorem proof_gap_exercise_2707_8
  (h1 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((1 /. ((3 : ℕ) ^ n)) + (((-(1 : ℤ)) ^ n) /. (n ^ (3 : ℕ)))) else 0))
  (h2 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((1 /. ((3 : ℕ) ^ (n + 1))) + (((-(1 : ℤ)) ^ (n + 1)) /. (n ^ (3 : ℕ)))) else 0))
  (h3 : ((∑' n, if (1 : ℕ) ≤ n then ((1 /. ((3 : ℕ) ^ n)) + (((-(1 : ℤ)) ^ n) /. (n ^ (3 : ℕ)))) else 0) + (∑' n, if (1 : ℕ) ≤ n then ((1 /. ((3 : ℕ) ^ (n + 1))) + (((-(1 : ℤ)) ^ (n + 1)) /. (n ^ (3 : ℕ)))) else 0)) = (∑' n, if (1 : ℕ) ≤ n then ((1 /. ((3 : ℕ) ^ n)) + (1 /. ((3 : ℕ) ^ (n + 1)))) else 0))
  (h4 : (∑' n, if (1 : ℕ) ≤ n then ((1 /. ((3 : ℕ) ^ n)) + (1 /. ((3 : ℕ) ^ (n + 1)))) else 0) = (∑' n, if (1 : ℕ) ≤ n then (4 /. ((3 : ℕ) ^ (n + 1))) else 0))
  (h5 : (∑' n, if (1 : ℕ) ≤ n then (4 /. ((3 : ℕ) ^ (n + 1))) else 0) = ((4 /. ((3 : ℕ) ^ (2 : ℕ))) * (1 /. (1 - (1 /. 3)))))
  (h6 : ((4 /. ((3 : ℕ) ^ (2 : ℕ))) * (1 /. (1 - (1 /. 3)))) = (2 /. 3))
  (h7 : (∑' n, if (1 : ℕ) ≤ n then (4 /. ((3 : ℕ) ^ (n + 1))) else 0) = (2 /. 3))
  : ((∑' n, if (1 : ℕ) ≤ n then ((1 /. ((3 : ℕ) ^ n)) + (((-(1 : ℤ)) ^ n) /. (n ^ (3 : ℕ)))) else 0) + (∑' n, if (1 : ℕ) ≤ n then ((1 /. ((3 : ℕ) ^ (n + 1))) + (((-(1 : ℤ)) ^ (n + 1)) /. (n ^ (3 : ℕ)))) else 0)) = (2 /. 3) := by
  sorry

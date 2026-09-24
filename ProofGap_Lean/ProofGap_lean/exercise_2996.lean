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

-- exercise: exercise_2996

theorem proof_gap_exercise_2996_1
  (d : (ℕ -> ℝ))
  : (∑' n, if (0 : ℕ) ≤ n then ((((2 : ℕ) ^ n) * (n + 1)) /. (n)!) else 0) = ((1 + (∑' n, if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. ((n - 1))!) else 0)) + (∑' n, if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. (n)!) else 0)) := by
  sorry

theorem proof_gap_exercise_2996_2
  (d : (ℕ -> ℝ))
  (h1 : (∑' n, if (0 : ℕ) ≤ n then ((((2 : ℕ) ^ n) * (n + 1)) /. (n)!) else 0) = ((1 + (∑' n, if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. ((n - 1))!) else 0)) + (∑' n, if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. (n)!) else 0)))
  : ((1 + (∑' n, if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. ((n - 1))!) else 0)) + (∑' n, if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. (n)!) else 0)) = ((2 * (∑' m, if (0 : ℕ) ≤ m then (((2 : ℕ) ^ m) /. (m)!) else 0)) + (∑' n, if (0 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. (n)!) else 0)) := by
  sorry

theorem proof_gap_exercise_2996_3
  (d : (ℕ -> ℝ))
  (h1 : (∑' n, if (0 : ℕ) ≤ n then ((((2 : ℕ) ^ n) * (n + 1)) /. (n)!) else 0) = ((1 + (∑' n, if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. ((n - 1))!) else 0)) + (∑' n, if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. (n)!) else 0)))
  (h2 : ((1 + (∑' n, if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. ((n - 1))!) else 0)) + (∑' n, if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. (n)!) else 0)) = ((2 * (∑' m, if (0 : ℕ) ≤ m then (((2 : ℕ) ^ m) /. (m)!) else 0)) + (∑' n, if (0 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. (n)!) else 0)))
  : ((2 * (∑' m, if (0 : ℕ) ≤ m then (((2 : ℕ) ^ m) /. (m)!) else 0)) + (∑' n, if (0 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. (n)!) else 0)) = (3 * (∑' n, if (0 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. (n)!) else 0)) := by
  sorry

theorem proof_gap_exercise_2996_4
  (d : (ℕ -> ℝ))
  (h1 : (∑' n, if (0 : ℕ) ≤ n then ((((2 : ℕ) ^ n) * (n + 1)) /. (n)!) else 0) = ((1 + (∑' n, if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. ((n - 1))!) else 0)) + (∑' n, if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. (n)!) else 0)))
  (h2 : ((1 + (∑' n, if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. ((n - 1))!) else 0)) + (∑' n, if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. (n)!) else 0)) = ((2 * (∑' m, if (0 : ℕ) ≤ m then (((2 : ℕ) ^ m) /. (m)!) else 0)) + (∑' n, if (0 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. (n)!) else 0)))
  (h3 : ((2 * (∑' m, if (0 : ℕ) ≤ m then (((2 : ℕ) ^ m) /. (m)!) else 0)) + (∑' n, if (0 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. (n)!) else 0)) = (3 * (∑' n, if (0 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. (n)!) else 0)))
  : ((∑' k, if (0 : ℕ) ≤ k then (1 /. (k)!) else 0) * (∑' l, if (0 : ℕ) ≤ l then (1 /. (l)!) else 0)) = (∑' n, if (0 : ℕ) ≤ n then (d n) else 0) := by
  sorry

theorem proof_gap_exercise_2996_5
  (d : (ℕ -> ℝ))
  (h1 : (∑' n, if (0 : ℕ) ≤ n then ((((2 : ℕ) ^ n) * (n + 1)) /. (n)!) else 0) = ((1 + (∑' n, if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. ((n - 1))!) else 0)) + (∑' n, if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. (n)!) else 0)))
  (h2 : ((1 + (∑' n, if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. ((n - 1))!) else 0)) + (∑' n, if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. (n)!) else 0)) = ((2 * (∑' m, if (0 : ℕ) ≤ m then (((2 : ℕ) ^ m) /. (m)!) else 0)) + (∑' n, if (0 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. (n)!) else 0)))
  (h3 : ((2 * (∑' m, if (0 : ℕ) ≤ m then (((2 : ℕ) ^ m) /. (m)!) else 0)) + (∑' n, if (0 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. (n)!) else 0)) = (3 * (∑' n, if (0 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. (n)!) else 0)))
  (h4 : ((∑' k, if (0 : ℕ) ≤ k then (1 /. (k)!) else 0) * (∑' l, if (0 : ℕ) ≤ l then (1 /. (l)!) else 0)) = (∑' n, if (0 : ℕ) ≤ n then (d n) else 0))
  : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((((d n) = (∑ k ∈ Finset.Icc (0 : ℕ) n, (1 /. ((k)! * ((n - k))!)))) ∧ ((∑ k ∈ Finset.Icc (0 : ℕ) n, (1 /. ((k)! * ((n - k))!))) = ((1 /. (n)!) * (∑ k ∈ Finset.Icc (0 : ℕ) n, (Nat.choose n k))))) ∧ (((1 /. (n)!) * (∑ k ∈ Finset.Icc (0 : ℕ) n, (Nat.choose n k))) = (((2 : ℕ) ^ n) /. (n)!))))) := by
  sorry

theorem proof_gap_exercise_2996_6
  (d : (ℕ -> ℝ))
  (h1 : (∑' n, if (0 : ℕ) ≤ n then ((((2 : ℕ) ^ n) * (n + 1)) /. (n)!) else 0) = ((1 + (∑' n, if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. ((n - 1))!) else 0)) + (∑' n, if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. (n)!) else 0)))
  (h2 : ((1 + (∑' n, if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. ((n - 1))!) else 0)) + (∑' n, if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. (n)!) else 0)) = ((2 * (∑' m, if (0 : ℕ) ≤ m then (((2 : ℕ) ^ m) /. (m)!) else 0)) + (∑' n, if (0 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. (n)!) else 0)))
  (h3 : ((2 * (∑' m, if (0 : ℕ) ≤ m then (((2 : ℕ) ^ m) /. (m)!) else 0)) + (∑' n, if (0 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. (n)!) else 0)) = (3 * (∑' n, if (0 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. (n)!) else 0)))
  (h4 : ((∑' k, if (0 : ℕ) ≤ k then (1 /. (k)!) else 0) * (∑' l, if (0 : ℕ) ≤ l then (1 /. (l)!) else 0)) = (∑' n, if (0 : ℕ) ≤ n then (d n) else 0))
  (h5 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((((d n) = (∑ k ∈ Finset.Icc (0 : ℕ) n, (1 /. ((k)! * ((n - k))!)))) ∧ ((∑ k ∈ Finset.Icc (0 : ℕ) n, (1 /. ((k)! * ((n - k))!))) = ((1 /. (n)!) * (∑ k ∈ Finset.Icc (0 : ℕ) n, (Nat.choose n k))))) ∧ (((1 /. (n)!) * (∑ k ∈ Finset.Icc (0 : ℕ) n, (Nat.choose n k))) = (((2 : ℕ) ^ n) /. (n)!))))))
  : (∑' n, if (0 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. (n)!) else 0) = ((∑' k, if (0 : ℕ) ≤ k then (1 /. (k)!) else 0) ^ (2 : ℕ)) := by
  sorry

theorem proof_gap_exercise_2996_7
  (d : (ℕ -> ℝ))
  (h1 : (∑' n, if (0 : ℕ) ≤ n then ((((2 : ℕ) ^ n) * (n + 1)) /. (n)!) else 0) = ((1 + (∑' n, if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. ((n - 1))!) else 0)) + (∑' n, if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. (n)!) else 0)))
  (h2 : ((1 + (∑' n, if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. ((n - 1))!) else 0)) + (∑' n, if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. (n)!) else 0)) = ((2 * (∑' m, if (0 : ℕ) ≤ m then (((2 : ℕ) ^ m) /. (m)!) else 0)) + (∑' n, if (0 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. (n)!) else 0)))
  (h3 : ((2 * (∑' m, if (0 : ℕ) ≤ m then (((2 : ℕ) ^ m) /. (m)!) else 0)) + (∑' n, if (0 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. (n)!) else 0)) = (3 * (∑' n, if (0 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. (n)!) else 0)))
  (h4 : ((∑' k, if (0 : ℕ) ≤ k then (1 /. (k)!) else 0) * (∑' l, if (0 : ℕ) ≤ l then (1 /. (l)!) else 0)) = (∑' n, if (0 : ℕ) ≤ n then (d n) else 0))
  (h5 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((((d n) = (∑ k ∈ Finset.Icc (0 : ℕ) n, (1 /. ((k)! * ((n - k))!)))) ∧ ((∑ k ∈ Finset.Icc (0 : ℕ) n, (1 /. ((k)! * ((n - k))!))) = ((1 /. (n)!) * (∑ k ∈ Finset.Icc (0 : ℕ) n, (Nat.choose n k))))) ∧ (((1 /. (n)!) * (∑ k ∈ Finset.Icc (0 : ℕ) n, (Nat.choose n k))) = (((2 : ℕ) ^ n) /. (n)!))))))
  (h6 : (∑' n, if (0 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. (n)!) else 0) = ((∑' k, if (0 : ℕ) ≤ k then (1 /. (k)!) else 0) ^ (2 : ℕ)))
  : ((∑' k, if (0 : ℕ) ≤ k then (1 /. (k)!) else 0) ^ (2 : ℕ)) = (Real.exp (2 : ℝ)) := by
  sorry

theorem proof_gap_exercise_2996_8
  (d : (ℕ -> ℝ))
  (h1 : (∑' n, if (0 : ℕ) ≤ n then ((((2 : ℕ) ^ n) * (n + 1)) /. (n)!) else 0) = ((1 + (∑' n, if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. ((n - 1))!) else 0)) + (∑' n, if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. (n)!) else 0)))
  (h2 : ((1 + (∑' n, if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. ((n - 1))!) else 0)) + (∑' n, if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. (n)!) else 0)) = ((2 * (∑' m, if (0 : ℕ) ≤ m then (((2 : ℕ) ^ m) /. (m)!) else 0)) + (∑' n, if (0 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. (n)!) else 0)))
  (h3 : ((2 * (∑' m, if (0 : ℕ) ≤ m then (((2 : ℕ) ^ m) /. (m)!) else 0)) + (∑' n, if (0 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. (n)!) else 0)) = (3 * (∑' n, if (0 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. (n)!) else 0)))
  (h4 : ((∑' k, if (0 : ℕ) ≤ k then (1 /. (k)!) else 0) * (∑' l, if (0 : ℕ) ≤ l then (1 /. (l)!) else 0)) = (∑' n, if (0 : ℕ) ≤ n then (d n) else 0))
  (h5 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((((d n) = (∑ k ∈ Finset.Icc (0 : ℕ) n, (1 /. ((k)! * ((n - k))!)))) ∧ ((∑ k ∈ Finset.Icc (0 : ℕ) n, (1 /. ((k)! * ((n - k))!))) = ((1 /. (n)!) * (∑ k ∈ Finset.Icc (0 : ℕ) n, (Nat.choose n k))))) ∧ (((1 /. (n)!) * (∑ k ∈ Finset.Icc (0 : ℕ) n, (Nat.choose n k))) = (((2 : ℕ) ^ n) /. (n)!))))))
  (h6 : (∑' n, if (0 : ℕ) ≤ n then (((2 : ℕ) ^ n) /. (n)!) else 0) = ((∑' k, if (0 : ℕ) ≤ k then (1 /. (k)!) else 0) ^ (2 : ℕ)))
  (h7 : ((∑' k, if (0 : ℕ) ≤ k then (1 /. (k)!) else 0) ^ (2 : ℕ)) = (Real.exp (2 : ℝ)))
  : (∑' n, if (0 : ℕ) ≤ n then ((((2 : ℕ) ^ n) * (n + 1)) /. (n)!) else 0) = (3 * (Real.exp (2 : ℝ))) := by
  sorry

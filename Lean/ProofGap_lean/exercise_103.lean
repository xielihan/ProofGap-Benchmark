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

-- exercise: exercise_103

theorem proof_gap_exercise_103_1
  (x : (ℕ -> ℝ))
  (h1 : True)
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = (1 + ((n /. (n + 1)) * (Real.cos ((n * Real.pi) /. 2))))))))
  : (x (1 : ℕ)) = 1 := by
  sorry

theorem proof_gap_exercise_103_2
  (x : (ℕ -> ℝ))
  (h1 : True)
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = (1 + ((n /. (n + 1)) * (Real.cos ((n * Real.pi) /. 2))))))))
  (h3 : (x (1 : ℕ)) = 1)
  : (x (2 : ℕ)) = (1 - (2 /. 3)) := by
  sorry

theorem proof_gap_exercise_103_3
  (x : (ℕ -> ℝ))
  (h1 : True)
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = (1 + ((n /. (n + 1)) * (Real.cos ((n * Real.pi) /. 2))))))))
  (h3 : (x (1 : ℕ)) = 1)
  (h4 : (x (2 : ℕ)) = (1 - (2 /. 3)))
  : (x (3 : ℕ)) = 1 := by
  sorry

theorem proof_gap_exercise_103_4
  (x : (ℕ -> ℝ))
  (h1 : True)
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = (1 + ((n /. (n + 1)) * (Real.cos ((n * Real.pi) /. 2))))))))
  (h3 : (x (1 : ℕ)) = 1)
  (h4 : (x (2 : ℕ)) = (1 - (2 /. 3)))
  (h5 : (x (3 : ℕ)) = 1)
  : (x (4 : ℕ)) = (1 + (4 /. 5)) := by
  sorry

theorem proof_gap_exercise_103_5
  (x : (ℕ -> ℝ))
  (h1 : True)
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = (1 + ((n /. (n + 1)) * (Real.cos ((n * Real.pi) /. 2))))))))
  (h3 : (x (1 : ℕ)) = 1)
  (h4 : (x (2 : ℕ)) = (1 - (2 /. 3)))
  (h5 : (x (3 : ℕ)) = 1)
  (h6 : (x (4 : ℕ)) = (1 + (4 /. 5)))
  : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x ((2 * k) - 1)) = 1))) := by
  sorry

theorem proof_gap_exercise_103_6
  (x : (ℕ -> ℝ))
  (h1 : True)
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = (1 + ((n /. (n + 1)) * (Real.cos ((n * Real.pi) /. 2))))))))
  (h3 : (x (1 : ℕ)) = 1)
  (h4 : (x (2 : ℕ)) = (1 - (2 /. 3)))
  (h5 : (x (3 : ℕ)) = 1)
  (h6 : (x (4 : ℕ)) = (1 + (4 /. 5)))
  (h7 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x ((2 * k) - 1)) = 1))))
  : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x ((4 * k) - 2)) = (1 - (((4 * k) - 2) /. ((4 * k) - 1)))))) := by
  sorry

theorem proof_gap_exercise_103_7
  (x : (ℕ -> ℝ))
  (h1 : True)
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = (1 + ((n /. (n + 1)) * (Real.cos ((n * Real.pi) /. 2))))))))
  (h3 : (x (1 : ℕ)) = 1)
  (h4 : (x (2 : ℕ)) = (1 - (2 /. 3)))
  (h5 : (x (3 : ℕ)) = 1)
  (h6 : (x (4 : ℕ)) = (1 + (4 /. 5)))
  (h7 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x ((2 * k) - 1)) = 1))))
  (h8 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x ((4 * k) - 2)) = (1 - (((4 * k) - 2) /. ((4 * k) - 1)))))))
  : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x (4 * k)) = (1 + ((4 * k) /. ((4 * k) + 1)))))) := by
  sorry

theorem proof_gap_exercise_103_8
  (x : (ℕ -> ℝ))
  (h1 : True)
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = (1 + ((n /. (n + 1)) * (Real.cos ((n * Real.pi) /. 2))))))))
  (h3 : (x (1 : ℕ)) = 1)
  (h4 : (x (2 : ℕ)) = (1 - (2 /. 3)))
  (h5 : (x (3 : ℕ)) = 1)
  (h6 : (x (4 : ℕ)) = (1 + (4 /. 5)))
  (h7 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x ((2 * k) - 1)) = 1))))
  (h8 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x ((4 * k) - 2)) = (1 - (((4 * k) - 2) /. ((4 * k) - 1)))))))
  (h9 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x (4 * k)) = (1 + ((4 * k) /. ((4 * k) + 1)))))))
  : (sInf ({x_n | (n ∈ ({n_1 : ℕ | 0 < n_1}))})) = 0 := by
  sorry

theorem proof_gap_exercise_103_9
  (x : (ℕ -> ℝ))
  (h1 : True)
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = (1 + ((n /. (n + 1)) * (Real.cos ((n * Real.pi) /. 2))))))))
  (h3 : (x (1 : ℕ)) = 1)
  (h4 : (x (2 : ℕ)) = (1 - (2 /. 3)))
  (h5 : (x (3 : ℕ)) = 1)
  (h6 : (x (4 : ℕ)) = (1 + (4 /. 5)))
  (h7 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x ((2 * k) - 1)) = 1))))
  (h8 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x ((4 * k) - 2)) = (1 - (((4 * k) - 2) /. ((4 * k) - 1)))))))
  (h9 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x (4 * k)) = (1 + ((4 * k) /. ((4 * k) + 1)))))))
  (h10 : (sInf ({x_n | (n ∈ ({n_1 : ℕ | 0 < n_1}))})) = 0)
  : (sSup ({x_n | (n ∈ ({n_1 : ℕ | 0 < n_1}))})) = 2 := by
  sorry

theorem proof_gap_exercise_103_10
  (x : (ℕ -> ℝ))
  (h1 : True)
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = (1 + ((n /. (n + 1)) * (Real.cos ((n * Real.pi) /. 2))))))))
  (h3 : (x (1 : ℕ)) = 1)
  (h4 : (x (2 : ℕ)) = (1 - (2 /. 3)))
  (h5 : (x (3 : ℕ)) = 1)
  (h6 : (x (4 : ℕ)) = (1 + (4 /. 5)))
  (h7 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x ((2 * k) - 1)) = 1))))
  (h8 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x ((4 * k) - 2)) = (1 - (((4 * k) - 2) /. ((4 * k) - 1)))))))
  (h9 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x (4 * k)) = (1 + ((4 * k) /. ((4 * k) + 1)))))))
  (h10 : (sInf ({x_n | (n ∈ ({n_1 : ℕ | 0 < n_1}))})) = 0)
  (h11 : (sSup ({x_n | (n ∈ ({n_1 : ℕ | 0 < n_1}))})) = 2)
  : (Filter.liminf (fun n : ℕ => ((x n) : EReal)) atTop) = 0 := by
  sorry

theorem proof_gap_exercise_103_11
  (x : (ℕ -> ℝ))
  (h1 : True)
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = (1 + ((n /. (n + 1)) * (Real.cos ((n * Real.pi) /. 2))))))))
  (h3 : (x (1 : ℕ)) = 1)
  (h4 : (x (2 : ℕ)) = (1 - (2 /. 3)))
  (h5 : (x (3 : ℕ)) = 1)
  (h6 : (x (4 : ℕ)) = (1 + (4 /. 5)))
  (h7 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x ((2 * k) - 1)) = 1))))
  (h8 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x ((4 * k) - 2)) = (1 - (((4 * k) - 2) /. ((4 * k) - 1)))))))
  (h9 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x (4 * k)) = (1 + ((4 * k) /. ((4 * k) + 1)))))))
  (h10 : (sInf ({x_n | (n ∈ ({n_1 : ℕ | 0 < n_1}))})) = 0)
  (h11 : (sSup ({x_n | (n ∈ ({n_1 : ℕ | 0 < n_1}))})) = 2)
  (h12 : (Filter.liminf (fun n : ℕ => ((x n) : EReal)) atTop) = 0)
  : (Filter.limsup (fun n : ℕ => ((x n) : EReal)) atTop) = 2 := by
  sorry

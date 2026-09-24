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

-- exercise: exercise_104

theorem proof_gap_exercise_104_1
  (x : (ℕ -> ℝ))
  (h1 : True)
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = ((1 + (2 * ((-(1 : ℤ)) ^ (n + 1)))) + (3 * (Real.rpow (-(1 : ℝ)) ((n * (n - 1)) /. 2))))))))
  : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x (4 * k)) = ((1 - 2) + 3)))) := by
  sorry

theorem proof_gap_exercise_104_2
  (x : (ℕ -> ℝ))
  (h1 : True)
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = ((1 + (2 * ((-(1 : ℤ)) ^ (n + 1)))) + (3 * (Real.rpow (-(1 : ℝ)) ((n * (n - 1)) /. 2))))))))
  (h3 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x (4 * k)) = ((1 - 2) + 3)))))
  : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x ((4 * k) + 1)) = ((1 + 2) + 3)))) := by
  sorry

theorem proof_gap_exercise_104_3
  (x : (ℕ -> ℝ))
  (h1 : True)
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = ((1 + (2 * ((-(1 : ℤ)) ^ (n + 1)))) + (3 * (Real.rpow (-(1 : ℝ)) ((n * (n - 1)) /. 2))))))))
  (h3 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x (4 * k)) = ((1 - 2) + 3)))))
  (h4 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x ((4 * k) + 1)) = ((1 + 2) + 3)))))
  : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x ((4 * k) + 2)) = ((1 - 2) - 3)))) := by
  sorry

theorem proof_gap_exercise_104_4
  (x : (ℕ -> ℝ))
  (h1 : True)
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = ((1 + (2 * ((-(1 : ℤ)) ^ (n + 1)))) + (3 * (Real.rpow (-(1 : ℝ)) ((n * (n - 1)) /. 2))))))))
  (h3 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x (4 * k)) = ((1 - 2) + 3)))))
  (h4 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x ((4 * k) + 1)) = ((1 + 2) + 3)))))
  (h5 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x ((4 * k) + 2)) = ((1 - 2) - 3)))))
  : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x ((4 * k) + 3)) = ((1 + 2) - 3)))) := by
  sorry

theorem proof_gap_exercise_104_5
  (x : (ℕ -> ℝ))
  (h1 : True)
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = ((1 + (2 * ((-(1 : ℤ)) ^ (n + 1)))) + (3 * (Real.rpow (-(1 : ℝ)) ((n * (n - 1)) /. 2))))))))
  (h3 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x (4 * k)) = ((1 - 2) + 3)))))
  (h4 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x ((4 * k) + 1)) = ((1 + 2) + 3)))))
  (h5 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x ((4 * k) + 2)) = ((1 - 2) - 3)))))
  (h6 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x ((4 * k) + 3)) = ((1 + 2) - 3)))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) ∈ ({x | x = 2 ∨ x = 6 ∨ x = (-(4 : ℝ)) ∨ x = 0})))) := by
  sorry

theorem proof_gap_exercise_104_6
  (x : (ℕ -> ℝ))
  (h1 : True)
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = ((1 + (2 * ((-(1 : ℤ)) ^ (n + 1)))) + (3 * (Real.rpow (-(1 : ℝ)) ((n * (n - 1)) /. 2))))))))
  (h3 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x (4 * k)) = ((1 - 2) + 3)))))
  (h4 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x ((4 * k) + 1)) = ((1 + 2) + 3)))))
  (h5 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x ((4 * k) + 2)) = ((1 - 2) - 3)))))
  (h6 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x ((4 * k) + 3)) = ((1 + 2) - 3)))))
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) ∈ ({x | x = 2 ∨ x = 6 ∨ x = (-(4 : ℝ)) ∨ x = 0})))))
  : (sInf ({x_n | (n ∈ ({n_1 : ℕ | 0 < n_1}))})) = (-(4 : ℝ)) := by
  sorry

theorem proof_gap_exercise_104_7
  (x : (ℕ -> ℝ))
  (h1 : True)
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = ((1 + (2 * ((-(1 : ℤ)) ^ (n + 1)))) + (3 * (Real.rpow (-(1 : ℝ)) ((n * (n - 1)) /. 2))))))))
  (h3 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x (4 * k)) = ((1 - 2) + 3)))))
  (h4 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x ((4 * k) + 1)) = ((1 + 2) + 3)))))
  (h5 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x ((4 * k) + 2)) = ((1 - 2) - 3)))))
  (h6 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x ((4 * k) + 3)) = ((1 + 2) - 3)))))
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) ∈ ({x | x = 2 ∨ x = 6 ∨ x = (-(4 : ℝ)) ∨ x = 0})))))
  (h8 : (sInf ({x_n | (n ∈ ({n_1 : ℕ | 0 < n_1}))})) = (-(4 : ℝ)))
  : (sSup ({x_n | (n ∈ ({n_1 : ℕ | 0 < n_1}))})) = 6 := by
  sorry

theorem proof_gap_exercise_104_8
  (x : (ℕ -> ℝ))
  (h1 : True)
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = ((1 + (2 * ((-(1 : ℤ)) ^ (n + 1)))) + (3 * (Real.rpow (-(1 : ℝ)) ((n * (n - 1)) /. 2))))))))
  (h3 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x (4 * k)) = ((1 - 2) + 3)))))
  (h4 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x ((4 * k) + 1)) = ((1 + 2) + 3)))))
  (h5 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x ((4 * k) + 2)) = ((1 - 2) - 3)))))
  (h6 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x ((4 * k) + 3)) = ((1 + 2) - 3)))))
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) ∈ ({x | x = 2 ∨ x = 6 ∨ x = (-(4 : ℝ)) ∨ x = 0})))))
  (h8 : (sInf ({x_n | (n ∈ ({n_1 : ℕ | 0 < n_1}))})) = (-(4 : ℝ)))
  (h9 : (sSup ({x_n | (n ∈ ({n_1 : ℕ | 0 < n_1}))})) = 6)
  : (Filter.liminf (fun n : ℕ => ((x n) : EReal)) atTop) = (-(4 : ℝ)) := by
  sorry

theorem proof_gap_exercise_104_9
  (x : (ℕ -> ℝ))
  (h1 : True)
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = ((1 + (2 * ((-(1 : ℤ)) ^ (n + 1)))) + (3 * (Real.rpow (-(1 : ℝ)) ((n * (n - 1)) /. 2))))))))
  (h3 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x (4 * k)) = ((1 - 2) + 3)))))
  (h4 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x ((4 * k) + 1)) = ((1 + 2) + 3)))))
  (h5 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x ((4 * k) + 2)) = ((1 - 2) - 3)))))
  (h6 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x ((4 * k) + 3)) = ((1 + 2) - 3)))))
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) ∈ ({x | x = 2 ∨ x = 6 ∨ x = (-(4 : ℝ)) ∨ x = 0})))))
  (h8 : (sInf ({x_n | (n ∈ ({n_1 : ℕ | 0 < n_1}))})) = (-(4 : ℝ)))
  (h9 : (sSup ({x_n | (n ∈ ({n_1 : ℕ | 0 < n_1}))})) = 6)
  (h10 : (Filter.liminf (fun n : ℕ => ((x n) : EReal)) atTop) = (-(4 : ℝ)))
  : (Filter.limsup (fun n : ℕ => ((x n) : EReal)) atTop) = 6 := by
  sorry

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

-- exercise: exercise_1455_2

theorem proof_gap_exercise_1455_2_1
  (a : (ℕ -> ℝ))
  (f : (ℝ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((Real.rpow (n : ℝ) (((2 : ℝ))⁻¹)) /. (n + 10000))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 <= x_1}))) → ((f x) = ((Real.rpow x (((2 : ℝ))⁻¹)) /. (x + 10000))))))
  : (lpMaximumPointsOn f (Set.Ici 0)) = ({x | x = 10000}) := by
  sorry

theorem proof_gap_exercise_1455_2_2
  (a : (ℕ -> ℝ))
  (f : (ℝ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((Real.rpow (n : ℝ) (((2 : ℝ))⁻¹)) /. (n + 10000))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 <= x_1}))) → ((f x) = ((Real.rpow x (((2 : ℝ))⁻¹)) /. (x + 10000))))))
  (h3 : (lpMaximumPointsOn f (Set.Ici 0)) = ({x | x = 10000}))
  : 10000 ∈ ({n_1 : ℕ | 0 < n_1}) := by
  sorry

theorem proof_gap_exercise_1455_2_3
  (a : (ℕ -> ℝ))
  (f : (ℝ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((Real.rpow (n : ℝ) (((2 : ℝ))⁻¹)) /. (n + 10000))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 <= x_1}))) → ((f x) = ((Real.rpow x (((2 : ℝ))⁻¹)) /. (x + 10000))))))
  (h3 : (lpMaximumPointsOn f (Set.Ici 0)) = ({x | x = 10000}))
  (h4 : 10000 ∈ ({n_1 : ℕ | 0 < n_1}))
  : (sSup (a '' ({n_1 : ℕ | 0 < n_1}))) = (a (10000 : ℕ)) := by
  sorry

theorem proof_gap_exercise_1455_2_4
  (a : (ℕ -> ℝ))
  (f : (ℝ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((Real.rpow (n : ℝ) (((2 : ℝ))⁻¹)) /. (n + 10000))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 <= x_1}))) → ((f x) = ((Real.rpow x (((2 : ℝ))⁻¹)) /. (x + 10000))))))
  (h3 : (lpMaximumPointsOn f (Set.Ici 0)) = ({x | x = 10000}))
  (h4 : 10000 ∈ ({n_1 : ℕ | 0 < n_1}))
  (h5 : (sSup (a '' ({n_1 : ℕ | 0 < n_1}))) = (a (10000 : ℕ)))
  : (a (10000 : ℕ)) = (f (10000 : ℝ)) := by
  sorry

theorem proof_gap_exercise_1455_2_5
  (a : (ℕ -> ℝ))
  (f : (ℝ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((Real.rpow (n : ℝ) (((2 : ℝ))⁻¹)) /. (n + 10000))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 <= x_1}))) → ((f x) = ((Real.rpow x (((2 : ℝ))⁻¹)) /. (x + 10000))))))
  (h3 : (lpMaximumPointsOn f (Set.Ici 0)) = ({x | x = 10000}))
  (h4 : 10000 ∈ ({n_1 : ℕ | 0 < n_1}))
  (h5 : (sSup (a '' ({n_1 : ℕ | 0 < n_1}))) = (a (10000 : ℕ)))
  (h6 : (a (10000 : ℕ)) = (f (10000 : ℝ)))
  : (f (10000 : ℝ)) = (1 /. 200) := by
  sorry

theorem proof_gap_exercise_1455_2_6
  (a : (ℕ -> ℝ))
  (f : (ℝ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((Real.rpow (n : ℝ) (((2 : ℝ))⁻¹)) /. (n + 10000))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 <= x_1}))) → ((f x) = ((Real.rpow x (((2 : ℝ))⁻¹)) /. (x + 10000))))))
  (h3 : (lpMaximumPointsOn f (Set.Ici 0)) = ({x | x = 10000}))
  (h4 : 10000 ∈ ({n_1 : ℕ | 0 < n_1}))
  (h5 : (sSup (a '' ({n_1 : ℕ | 0 < n_1}))) = (a (10000 : ℕ)))
  (h6 : (a (10000 : ℕ)) = (f (10000 : ℝ)))
  (h7 : (f (10000 : ℝ)) = (1 /. 200))
  : (a (10000 : ℕ)) = (1 /. 200) := by
  sorry

theorem proof_gap_exercise_1455_2_7
  (a : (ℕ -> ℝ))
  (f : (ℝ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((Real.rpow (n : ℝ) (((2 : ℝ))⁻¹)) /. (n + 10000))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 <= x_1}))) → ((f x) = ((Real.rpow x (((2 : ℝ))⁻¹)) /. (x + 10000))))))
  (h3 : (lpMaximumPointsOn f (Set.Ici 0)) = ({x | x = 10000}))
  (h4 : 10000 ∈ ({n_1 : ℕ | 0 < n_1}))
  (h5 : (sSup (a '' ({n_1 : ℕ | 0 < n_1}))) = (a (10000 : ℕ)))
  (h6 : (a (10000 : ℕ)) = (f (10000 : ℝ)))
  (h7 : (f (10000 : ℝ)) = (1 /. 200))
  (h8 : (a (10000 : ℕ)) = (1 /. 200))
  : (sSup (a '' ({n_1 : ℕ | 0 < n_1}))) = (1 /. 200) := by
  sorry

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

-- exercise: exercise_1452

theorem proof_gap_exercise_1452_1
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((f x) = ((1 + (x ^ (2 : ℕ))) /. (1 + (x ^ (4 : ℕ))))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((f x) > 0))) := by
  sorry

theorem proof_gap_exercise_1452_2
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((f x) = ((1 + (x ^ (2 : ℕ))) /. (1 + (x ^ (4 : ℕ))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((f x) > 0))))
  : Tendsto (fun x : ℝ => (f x)) atTop (𝓝 0) := by
  sorry

theorem proof_gap_exercise_1452_3
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((f x) = ((1 + (x ^ (2 : ℕ))) /. (1 + (x ^ (4 : ℕ))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((f x) > 0))))
  (h3 : Tendsto (fun x : ℝ => (f x)) atTop (𝓝 0))
  : (sInf (f '' (Set.Ioi 0))) = 0 := by
  sorry

theorem proof_gap_exercise_1452_4
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((f x) = ((1 + (x ^ (2 : ℕ))) /. (1 + (x ^ (4 : ℕ))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((f x) > 0))))
  (h3 : Tendsto (fun x : ℝ => (f x)) atTop (𝓝 0))
  (h4 : (sInf (f '' (Set.Ioi 0))) = 0)
  : (lpMaximumPointsOn f (Set.Ioi 0)) = ({x | x = (Real.rpow ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) - 1) (((2 : ℝ))⁻¹))}) := by
  sorry

theorem proof_gap_exercise_1452_5
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((f x) = ((1 + (x ^ (2 : ℕ))) /. (1 + (x ^ (4 : ℕ))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((f x) > 0))))
  (h3 : Tendsto (fun x : ℝ => (f x)) atTop (𝓝 0))
  (h4 : (sInf (f '' (Set.Ioi 0))) = 0)
  (h5 : (lpMaximumPointsOn f (Set.Ioi 0)) = ({x | x = (Real.rpow ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) - 1) (((2 : ℝ))⁻¹))}))
  : (f (Real.rpow ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) - 1) (((2 : ℝ))⁻¹))) = ((1 /. 2) * (1 + (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)))) := by
  sorry

theorem proof_gap_exercise_1452_6
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((f x) = ((1 + (x ^ (2 : ℕ))) /. (1 + (x ^ (4 : ℕ))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((f x) > 0))))
  (h3 : Tendsto (fun x : ℝ => (f x)) atTop (𝓝 0))
  (h4 : (sInf (f '' (Set.Ioi 0))) = 0)
  (h5 : (lpMaximumPointsOn f (Set.Ioi 0)) = ({x | x = (Real.rpow ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) - 1) (((2 : ℝ))⁻¹))}))
  (h6 : (f (Real.rpow ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) - 1) (((2 : ℝ))⁻¹))) = ((1 /. 2) * (1 + (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)))))
  : (sSup (f '' (Set.Ioi 0))) = ((1 /. 2) * (1 + (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)))) := by
  sorry

theorem proof_gap_exercise_1452_7
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((f x) = ((1 + (x ^ (2 : ℕ))) /. (1 + (x ^ (4 : ℕ))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((f x) > 0))))
  (h3 : Tendsto (fun x : ℝ => (f x)) atTop (𝓝 0))
  (h4 : (sInf (f '' (Set.Ioi 0))) = 0)
  (h5 : (lpMaximumPointsOn f (Set.Ioi 0)) = ({x | x = (Real.rpow ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) - 1) (((2 : ℝ))⁻¹))}))
  (h6 : (f (Real.rpow ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) - 1) (((2 : ℝ))⁻¹))) = ((1 /. 2) * (1 + (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)))))
  (h7 : (sSup (f '' (Set.Ioi 0))) = ((1 /. 2) * (1 + (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)))))
  : |(((1 /. 2) * (1 + (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)))) - (((12 : ℝ) /. (10 : ℝ))))| ≤ (((01 : ℝ) /. (10 : ℝ))) := by
  sorry

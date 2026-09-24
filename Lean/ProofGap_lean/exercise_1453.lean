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

-- exercise: exercise_1453

theorem proof_gap_exercise_1453_1
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((Real.exp (-(x ^ (2 : ℕ)))) * (Real.cos (x ^ (2 : ℕ))))))))
  : (lpMinimumPointsOn f Set.univ) = ({x | x = (Real.rpow ((3 * Real.pi) /. 4) (((2 : ℝ))⁻¹)) ∨ x = (-(Real.rpow ((3 * Real.pi) /. 4) (((2 : ℝ))⁻¹)))}) := by
  sorry

theorem proof_gap_exercise_1453_2
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((Real.exp (-(x ^ (2 : ℕ)))) * (Real.cos (x ^ (2 : ℕ))))))))
  (h2 : (lpMinimumPointsOn f Set.univ) = ({x | x = (Real.rpow ((3 * Real.pi) /. 4) (((2 : ℝ))⁻¹)) ∨ x = (-(Real.rpow ((3 * Real.pi) /. 4) (((2 : ℝ))⁻¹)))}))
  : (f (Real.rpow ((3 * Real.pi) /. 4) (((2 : ℝ))⁻¹))) = ((-((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) /. 2)) * (Real.exp (-((3 * Real.pi) /. 4)))) := by
  sorry

theorem proof_gap_exercise_1453_3
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((Real.exp (-(x ^ (2 : ℕ)))) * (Real.cos (x ^ (2 : ℕ))))))))
  (h2 : (lpMinimumPointsOn f Set.univ) = ({x | x = (Real.rpow ((3 * Real.pi) /. 4) (((2 : ℝ))⁻¹)) ∨ x = (-(Real.rpow ((3 * Real.pi) /. 4) (((2 : ℝ))⁻¹)))}))
  (h3 : (f (Real.rpow ((3 * Real.pi) /. 4) (((2 : ℝ))⁻¹))) = ((-((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) /. 2)) * (Real.exp (-((3 * Real.pi) /. 4)))))
  : (f (-(Real.rpow ((3 * Real.pi) /. 4) (((2 : ℝ))⁻¹)))) = ((-((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) /. 2)) * (Real.exp (-((3 * Real.pi) /. 4)))) := by
  sorry

theorem proof_gap_exercise_1453_4
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((Real.exp (-(x ^ (2 : ℕ)))) * (Real.cos (x ^ (2 : ℕ))))))))
  (h2 : (lpMinimumPointsOn f Set.univ) = ({x | x = (Real.rpow ((3 * Real.pi) /. 4) (((2 : ℝ))⁻¹)) ∨ x = (-(Real.rpow ((3 * Real.pi) /. 4) (((2 : ℝ))⁻¹)))}))
  (h3 : (f (Real.rpow ((3 * Real.pi) /. 4) (((2 : ℝ))⁻¹))) = ((-((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) /. 2)) * (Real.exp (-((3 * Real.pi) /. 4)))))
  (h4 : (f (-(Real.rpow ((3 * Real.pi) /. 4) (((2 : ℝ))⁻¹)))) = ((-((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) /. 2)) * (Real.exp (-((3 * Real.pi) /. 4)))))
  : (lpMaximumPointsOn f Set.univ) = ({x | x = 0}) := by
  sorry

theorem proof_gap_exercise_1453_5
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((Real.exp (-(x ^ (2 : ℕ)))) * (Real.cos (x ^ (2 : ℕ))))))))
  (h2 : (lpMinimumPointsOn f Set.univ) = ({x | x = (Real.rpow ((3 * Real.pi) /. 4) (((2 : ℝ))⁻¹)) ∨ x = (-(Real.rpow ((3 * Real.pi) /. 4) (((2 : ℝ))⁻¹)))}))
  (h3 : (f (Real.rpow ((3 * Real.pi) /. 4) (((2 : ℝ))⁻¹))) = ((-((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) /. 2)) * (Real.exp (-((3 * Real.pi) /. 4)))))
  (h4 : (f (-(Real.rpow ((3 * Real.pi) /. 4) (((2 : ℝ))⁻¹)))) = ((-((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) /. 2)) * (Real.exp (-((3 * Real.pi) /. 4)))))
  (h5 : (lpMaximumPointsOn f Set.univ) = ({x | x = 0}))
  : (f (0 : ℝ)) = 1 := by
  sorry

theorem proof_gap_exercise_1453_6
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((Real.exp (-(x ^ (2 : ℕ)))) * (Real.cos (x ^ (2 : ℕ))))))))
  (h2 : (lpMinimumPointsOn f Set.univ) = ({x | x = (Real.rpow ((3 * Real.pi) /. 4) (((2 : ℝ))⁻¹)) ∨ x = (-(Real.rpow ((3 * Real.pi) /. 4) (((2 : ℝ))⁻¹)))}))
  (h3 : (f (Real.rpow ((3 * Real.pi) /. 4) (((2 : ℝ))⁻¹))) = ((-((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) /. 2)) * (Real.exp (-((3 * Real.pi) /. 4)))))
  (h4 : (f (-(Real.rpow ((3 * Real.pi) /. 4) (((2 : ℝ))⁻¹)))) = ((-((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) /. 2)) * (Real.exp (-((3 * Real.pi) /. 4)))))
  (h5 : (lpMaximumPointsOn f Set.univ) = ({x | x = 0}))
  (h6 : (f (0 : ℝ)) = 1)
  : (sInf (f '' Set.univ)) = ((-((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) /. 2)) * (Real.exp (-((3 * Real.pi) /. 4)))) := by
  sorry

theorem proof_gap_exercise_1453_7
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((Real.exp (-(x ^ (2 : ℕ)))) * (Real.cos (x ^ (2 : ℕ))))))))
  (h2 : (lpMinimumPointsOn f Set.univ) = ({x | x = (Real.rpow ((3 * Real.pi) /. 4) (((2 : ℝ))⁻¹)) ∨ x = (-(Real.rpow ((3 * Real.pi) /. 4) (((2 : ℝ))⁻¹)))}))
  (h3 : (f (Real.rpow ((3 * Real.pi) /. 4) (((2 : ℝ))⁻¹))) = ((-((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) /. 2)) * (Real.exp (-((3 * Real.pi) /. 4)))))
  (h4 : (f (-(Real.rpow ((3 * Real.pi) /. 4) (((2 : ℝ))⁻¹)))) = ((-((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) /. 2)) * (Real.exp (-((3 * Real.pi) /. 4)))))
  (h5 : (lpMaximumPointsOn f Set.univ) = ({x | x = 0}))
  (h6 : (f (0 : ℝ)) = 1)
  (h7 : (sInf (f '' Set.univ)) = ((-((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) /. 2)) * (Real.exp (-((3 * Real.pi) /. 4)))))
  : |(((-((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) /. 2)) * (Real.exp (-((3 * Real.pi) /. 4)))) - (-(((0067 : ℝ) /. (1000 : ℝ)))))| ≤ (((0001 : ℝ) /. (1000 : ℝ))) := by
  sorry

theorem proof_gap_exercise_1453_8
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((Real.exp (-(x ^ (2 : ℕ)))) * (Real.cos (x ^ (2 : ℕ))))))))
  (h2 : (lpMinimumPointsOn f Set.univ) = ({x | x = (Real.rpow ((3 * Real.pi) /. 4) (((2 : ℝ))⁻¹)) ∨ x = (-(Real.rpow ((3 * Real.pi) /. 4) (((2 : ℝ))⁻¹)))}))
  (h3 : (f (Real.rpow ((3 * Real.pi) /. 4) (((2 : ℝ))⁻¹))) = ((-((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) /. 2)) * (Real.exp (-((3 * Real.pi) /. 4)))))
  (h4 : (f (-(Real.rpow ((3 * Real.pi) /. 4) (((2 : ℝ))⁻¹)))) = ((-((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) /. 2)) * (Real.exp (-((3 * Real.pi) /. 4)))))
  (h5 : (lpMaximumPointsOn f Set.univ) = ({x | x = 0}))
  (h6 : (f (0 : ℝ)) = 1)
  (h7 : (sInf (f '' Set.univ)) = ((-((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) /. 2)) * (Real.exp (-((3 * Real.pi) /. 4)))))
  (h8 : |(((-((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) /. 2)) * (Real.exp (-((3 * Real.pi) /. 4)))) - (-(((0067 : ℝ) /. (1000 : ℝ)))))| ≤ (((0001 : ℝ) /. (1000 : ℝ))))
  : (sSup (f '' Set.univ)) = 1 := by
  sorry

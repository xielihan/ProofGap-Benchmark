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

-- exercise: exercise_1456_2

theorem proof_gap_exercise_1456_2_1
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : p > 1)
  (h3 : f = (fun (x : ℝ) => ((Real.rpow x p) + (Real.rpow (1 - x) p))))
  : ContinuousOn f (Set.Icc 0 1) := by
  sorry

theorem proof_gap_exercise_1456_2_2
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : p > 1)
  (h3 : f = (fun (x : ℝ) => ((Real.rpow x p) + (Real.rpow (1 - x) p))))
  (h4 : ContinuousOn f (Set.Icc 0 1))
  : (lpMinimumPointsOn f (Set.Icc 0 1)) = ({x | x = (1 /. 2)}) := by
  sorry

theorem proof_gap_exercise_1456_2_3
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : p > 1)
  (h3 : f = (fun (x : ℝ) => ((Real.rpow x p) + (Real.rpow (1 - x) p))))
  (h4 : ContinuousOn f (Set.Icc 0 1))
  (h5 : (lpMinimumPointsOn f (Set.Icc 0 1)) = ({x | x = (1 /. 2)}))
  : (f (1 /. 2)) = (1 /. (Real.rpow (2 : ℝ) (p - 1))) := by
  sorry

theorem proof_gap_exercise_1456_2_4
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : p > 1)
  (h3 : f = (fun (x : ℝ) => ((Real.rpow x p) + (Real.rpow (1 - x) p))))
  (h4 : ContinuousOn f (Set.Icc 0 1))
  (h5 : (lpMinimumPointsOn f (Set.Icc 0 1)) = ({x | x = (1 /. 2)}))
  (h6 : (f (1 /. 2)) = (1 /. (Real.rpow (2 : ℝ) (p - 1))))
  : (lpMaximumPointsOn f (Set.Icc 0 1)) = ({x | x = 0 ∨ x = 1}) := by
  sorry

theorem proof_gap_exercise_1456_2_5
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : p > 1)
  (h3 : f = (fun (x : ℝ) => ((Real.rpow x p) + (Real.rpow (1 - x) p))))
  (h4 : ContinuousOn f (Set.Icc 0 1))
  (h5 : (lpMinimumPointsOn f (Set.Icc 0 1)) = ({x | x = (1 /. 2)}))
  (h6 : (f (1 /. 2)) = (1 /. (Real.rpow (2 : ℝ) (p - 1))))
  (h7 : (lpMaximumPointsOn f (Set.Icc 0 1)) = ({x | x = 0 ∨ x = 1}))
  : (f 0) = 1 := by
  sorry

theorem proof_gap_exercise_1456_2_6
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : p > 1)
  (h3 : f = (fun (x : ℝ) => ((Real.rpow x p) + (Real.rpow (1 - x) p))))
  (h4 : ContinuousOn f (Set.Icc 0 1))
  (h5 : (lpMinimumPointsOn f (Set.Icc 0 1)) = ({x | x = (1 /. 2)}))
  (h6 : (f (1 /. 2)) = (1 /. (Real.rpow (2 : ℝ) (p - 1))))
  (h7 : (lpMaximumPointsOn f (Set.Icc 0 1)) = ({x | x = 0 ∨ x = 1}))
  (h8 : (f 0) = 1)
  : (f 1) = 1 := by
  sorry

theorem proof_gap_exercise_1456_2_7
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : p > 1)
  (h3 : f = (fun (x : ℝ) => ((Real.rpow x p) + (Real.rpow (1 - x) p))))
  (h4 : ContinuousOn f (Set.Icc 0 1))
  (h5 : (lpMinimumPointsOn f (Set.Icc 0 1)) = ({x | x = (1 /. 2)}))
  (h6 : (f (1 /. 2)) = (1 /. (Real.rpow (2 : ℝ) (p - 1))))
  (h7 : (lpMaximumPointsOn f (Set.Icc 0 1)) = ({x | x = 0 ∨ x = 1}))
  (h8 : (f 0) = 1)
  (h9 : (f 1) = 1)
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((1 /. (Real.rpow (2 : ℝ) (p - 1))) ≤ (f x)))) := by
  sorry

theorem proof_gap_exercise_1456_2_8
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : p > 1)
  (h3 : f = (fun (x : ℝ) => ((Real.rpow x p) + (Real.rpow (1 - x) p))))
  (h4 : ContinuousOn f (Set.Icc 0 1))
  (h5 : (lpMinimumPointsOn f (Set.Icc 0 1)) = ({x | x = (1 /. 2)}))
  (h6 : (f (1 /. 2)) = (1 /. (Real.rpow (2 : ℝ) (p - 1))))
  (h7 : (lpMaximumPointsOn f (Set.Icc 0 1)) = ({x | x = 0 ∨ x = 1}))
  (h8 : (f 0) = 1)
  (h9 : (f 1) = 1)
  (h10 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((1 /. (Real.rpow (2 : ℝ) (p - 1))) ≤ (f x)))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((f x) ≤ 1))) := by
  sorry

theorem proof_gap_exercise_1456_2_9
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : p > 1)
  (h3 : f = (fun (x : ℝ) => ((Real.rpow x p) + (Real.rpow (1 - x) p))))
  (h4 : ContinuousOn f (Set.Icc 0 1))
  (h5 : (lpMinimumPointsOn f (Set.Icc 0 1)) = ({x | x = (1 /. 2)}))
  (h6 : (f (1 /. 2)) = (1 /. (Real.rpow (2 : ℝ) (p - 1))))
  (h7 : (lpMaximumPointsOn f (Set.Icc 0 1)) = ({x | x = 0 ∨ x = 1}))
  (h8 : (f 0) = 1)
  (h9 : (f 1) = 1)
  (h10 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((1 /. (Real.rpow (2 : ℝ) (p - 1))) ≤ (f x)))))
  (h11 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((f x) ≤ 1))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((1 /. (Real.rpow (2 : ℝ) (p - 1))) ≤ ((Real.rpow x p) + (Real.rpow (1 - x) p))))) := by
  sorry

theorem proof_gap_exercise_1456_2_10
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : p > 1)
  (h3 : f = (fun (x : ℝ) => ((Real.rpow x p) + (Real.rpow (1 - x) p))))
  (h4 : ContinuousOn f (Set.Icc 0 1))
  (h5 : (lpMinimumPointsOn f (Set.Icc 0 1)) = ({x | x = (1 /. 2)}))
  (h6 : (f (1 /. 2)) = (1 /. (Real.rpow (2 : ℝ) (p - 1))))
  (h7 : (lpMaximumPointsOn f (Set.Icc 0 1)) = ({x | x = 0 ∨ x = 1}))
  (h8 : (f 0) = 1)
  (h9 : (f 1) = 1)
  (h10 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((1 /. (Real.rpow (2 : ℝ) (p - 1))) ≤ (f x)))))
  (h11 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((f x) ≤ 1))))
  (h12 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((1 /. (Real.rpow (2 : ℝ) (p - 1))) ≤ ((Real.rpow x p) + (Real.rpow (1 - x) p))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → (((Real.rpow x p) + (Real.rpow (1 - x) p)) ≤ 1))) := by
  sorry

theorem proof_gap_exercise_1456_2_11
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : p > 1)
  (h3 : f = (fun (x : ℝ) => ((Real.rpow x p) + (Real.rpow (1 - x) p))))
  (h4 : ContinuousOn f (Set.Icc 0 1))
  (h5 : (lpMinimumPointsOn f (Set.Icc 0 1)) = ({x | x = (1 /. 2)}))
  (h6 : (f (1 /. 2)) = (1 /. (Real.rpow (2 : ℝ) (p - 1))))
  (h7 : (lpMaximumPointsOn f (Set.Icc 0 1)) = ({x | x = 0 ∨ x = 1}))
  (h8 : (f 0) = 1)
  (h9 : (f 1) = 1)
  (h10 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((1 /. (Real.rpow (2 : ℝ) (p - 1))) ≤ (f x)))))
  (h11 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((f x) ≤ 1))))
  (h12 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((1 /. (Real.rpow (2 : ℝ) (p - 1))) ≤ ((Real.rpow x p) + (Real.rpow (1 - x) p))))))
  (h13 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → (((Real.rpow x p) + (Real.rpow (1 - x) p)) ≤ 1))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → (((1 /. (Real.rpow (2 : ℝ) (p - 1))) ≤ ((Real.rpow x p) + (Real.rpow (1 - x) p))) ∧ (((Real.rpow x p) + (Real.rpow (1 - x) p)) ≤ 1)))) := by
  sorry

theorem proof_gap_exercise_1456_2_12
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : p > 1)
  (h3 : f = (fun (x : ℝ) => ((Real.rpow x p) + (Real.rpow (1 - x) p))))
  (h4 : ContinuousOn f (Set.Icc 0 1))
  (h5 : (lpMinimumPointsOn f (Set.Icc 0 1)) = ({x | x = (1 /. 2)}))
  (h6 : (f (1 /. 2)) = (1 /. (Real.rpow (2 : ℝ) (p - 1))))
  (h7 : (lpMaximumPointsOn f (Set.Icc 0 1)) = ({x | x = 0 ∨ x = 1}))
  (h8 : (f 0) = 1)
  (h9 : (f 1) = 1)
  (h10 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((1 /. (Real.rpow (2 : ℝ) (p - 1))) ≤ (f x)))))
  (h11 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((f x) ≤ 1))))
  (h12 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((1 /. (Real.rpow (2 : ℝ) (p - 1))) ≤ ((Real.rpow x p) + (Real.rpow (1 - x) p))))))
  (h13 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → (((Real.rpow x p) + (Real.rpow (1 - x) p)) ≤ 1))))
  (h14 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → (((1 /. (Real.rpow (2 : ℝ) (p - 1))) ≤ ((Real.rpow x p) + (Real.rpow (1 - x) p))) ∧ (((Real.rpow x p) + (Real.rpow (1 - x) p)) ≤ 1)))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → (((1 /. (Real.rpow (2 : ℝ) (p - 1))) ≤ ((Real.rpow x p) + (Real.rpow (1 - x) p))) ∧ (((Real.rpow x p) + (Real.rpow (1 - x) p)) ≤ 1)))) := by
  sorry

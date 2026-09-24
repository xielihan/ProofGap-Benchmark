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

-- exercise: exercise_1435

theorem proof_gap_exercise_1435_1
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 2))) → ((y x) = (Real.rpow ((2 * x) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 2)) → ((iteratedDeriv 1 (fun t => y t) x) = ((1 - x) /. (Real.rpow ((2 * x) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))))) := by
  sorry

theorem proof_gap_exercise_1435_2
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 2))) → ((y x) = (Real.rpow ((2 * x) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 2)) → ((iteratedDeriv 1 (fun t => y t) x) = ((1 - x) /. (Real.rpow ((2 * x) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 2)) → (((iteratedDeriv 1 (fun t => y t) x) = 0) ↔ (x = 1)))) := by
  sorry

theorem proof_gap_exercise_1435_3
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 2))) → ((y x) = (Real.rpow ((2 * x) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 2)) → ((iteratedDeriv 1 (fun t => y t) x) = ((1 - x) /. (Real.rpow ((2 * x) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 2)) → (((iteratedDeriv 1 (fun t => y t) x) = 0) ↔ (x = 1)))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 1)) → ((iteratedDeriv 1 (fun t => y t) x) > 0))) := by
  sorry

theorem proof_gap_exercise_1435_4
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 2))) → ((y x) = (Real.rpow ((2 * x) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 2)) → ((iteratedDeriv 1 (fun t => y t) x) = ((1 - x) /. (Real.rpow ((2 * x) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 2)) → (((iteratedDeriv 1 (fun t => y t) x) = 0) ↔ (x = 1)))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 1)) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (1 < x)) ∧ (x < 2)) → ((iteratedDeriv 1 (fun t => y t) x) < 0))) := by
  sorry

theorem proof_gap_exercise_1435_5
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 2))) → ((y x) = (Real.rpow ((2 * x) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 2)) → ((iteratedDeriv 1 (fun t => y t) x) = ((1 - x) /. (Real.rpow ((2 * x) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 2)) → (((iteratedDeriv 1 (fun t => y t) x) = 0) ↔ (x = 1)))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 1)) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (1 < x)) ∧ (x < 2)) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  : (lpMaximumPointsOn y (Set.Icc 0 2)) = ({x | x = 1}) := by
  sorry

theorem proof_gap_exercise_1435_6
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 2))) → ((y x) = (Real.rpow ((2 * x) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 2)) → ((iteratedDeriv 1 (fun t => y t) x) = ((1 - x) /. (Real.rpow ((2 * x) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 2)) → (((iteratedDeriv 1 (fun t => y t) x) = 0) ↔ (x = 1)))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 1)) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (1 < x)) ∧ (x < 2)) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  (h6 : (lpMaximumPointsOn y (Set.Icc 0 2)) = ({x | x = 1}))
  : (y (1 : ℝ)) = 1 := by
  sorry

theorem proof_gap_exercise_1435_7
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 2))) → ((y x) = (Real.rpow ((2 * x) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 2)) → ((iteratedDeriv 1 (fun t => y t) x) = ((1 - x) /. (Real.rpow ((2 * x) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 2)) → (((iteratedDeriv 1 (fun t => y t) x) = 0) ↔ (x = 1)))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 1)) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (1 < x)) ∧ (x < 2)) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  (h6 : (lpMaximumPointsOn y (Set.Icc 0 2)) = ({x | x = 1}))
  (h7 : (y (1 : ℝ)) = 1)
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 2))) → ((y x) ≥ 0))) := by
  sorry

theorem proof_gap_exercise_1435_8
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 2))) → ((y x) = (Real.rpow ((2 * x) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 2)) → ((iteratedDeriv 1 (fun t => y t) x) = ((1 - x) /. (Real.rpow ((2 * x) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 2)) → (((iteratedDeriv 1 (fun t => y t) x) = 0) ↔ (x = 1)))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 1)) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (1 < x)) ∧ (x < 2)) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  (h6 : (lpMaximumPointsOn y (Set.Icc 0 2)) = ({x | x = 1}))
  (h7 : (y (1 : ℝ)) = 1)
  (h8 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 2))) → ((y x) ≥ 0))))
  : (lpMinimumPointsOn y (Set.Icc 0 2)) = ({x | x = 0 ∨ x = 2}) := by
  sorry

theorem proof_gap_exercise_1435_9
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 2))) → ((y x) = (Real.rpow ((2 * x) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 2)) → ((iteratedDeriv 1 (fun t => y t) x) = ((1 - x) /. (Real.rpow ((2 * x) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 2)) → (((iteratedDeriv 1 (fun t => y t) x) = 0) ↔ (x = 1)))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 1)) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (1 < x)) ∧ (x < 2)) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  (h6 : (lpMaximumPointsOn y (Set.Icc 0 2)) = ({x | x = 1}))
  (h7 : (y (1 : ℝ)) = 1)
  (h8 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 2))) → ((y x) ≥ 0))))
  (h9 : (lpMinimumPointsOn y (Set.Icc 0 2)) = ({x | x = 0 ∨ x = 2}))
  : (y (0 : ℝ)) = 0 := by
  sorry

theorem proof_gap_exercise_1435_10
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 2))) → ((y x) = (Real.rpow ((2 * x) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 2)) → ((iteratedDeriv 1 (fun t => y t) x) = ((1 - x) /. (Real.rpow ((2 * x) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 2)) → (((iteratedDeriv 1 (fun t => y t) x) = 0) ↔ (x = 1)))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 1)) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (1 < x)) ∧ (x < 2)) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  (h6 : (lpMaximumPointsOn y (Set.Icc 0 2)) = ({x | x = 1}))
  (h7 : (y (1 : ℝ)) = 1)
  (h8 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 2))) → ((y x) ≥ 0))))
  (h9 : (lpMinimumPointsOn y (Set.Icc 0 2)) = ({x | x = 0 ∨ x = 2}))
  (h10 : (y (0 : ℝ)) = 0)
  : (y (2 : ℝ)) = 0 := by
  sorry

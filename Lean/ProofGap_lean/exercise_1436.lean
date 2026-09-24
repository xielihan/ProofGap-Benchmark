import Mathlib

attribute [local instance] Classical.propDecidable

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

-- exercise: exercise_1436

theorem proof_gap_exercise_1436_1
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (x * (Real.rpow (x - 1) (((3 : ℝ))⁻¹)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((iteratedDeriv 1 (fun t => y t) x) = (((4 * x) - 3) /. (3 * (Real.rpow (x - 1) (2 /. 3))))))) := by
  sorry

theorem proof_gap_exercise_1436_2
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (x * (Real.rpow (x - 1) (((3 : ℝ))⁻¹)))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((iteratedDeriv 1 (fun t => y t) x) = (((4 * x) - 3) /. (3 * (Real.rpow (x - 1) (2 /. 3))))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → (((iteratedDeriv 1 (fun t => y t) x) = 0) ↔ (x = (3 /. 4))))) := by
  sorry

theorem proof_gap_exercise_1436_3
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (x * (Real.rpow (x - 1) (((3 : ℝ))⁻¹)))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((iteratedDeriv 1 (fun t => y t) x) = (((4 * x) - 3) /. (3 * (Real.rpow (x - 1) (2 /. 3))))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → (((iteratedDeriv 1 (fun t => y t) x) = 0) ↔ (x = (3 /. 4))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x < (3 /. 4))) → ((iteratedDeriv 1 (fun t => y t) x) < 0))) := by
  sorry

theorem proof_gap_exercise_1436_4
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (x * (Real.rpow (x - 1) (((3 : ℝ))⁻¹)))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((iteratedDeriv 1 (fun t => y t) x) = (((4 * x) - 3) /. (3 * (Real.rpow (x - 1) (2 /. 3))))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → (((iteratedDeriv 1 (fun t => y t) x) = 0) ↔ (x = (3 /. 4))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x < (3 /. 4))) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x > (3 /. 4))) ∧ (x ≠ 1)) → ((iteratedDeriv 1 (fun t => y t) x) > 0))) := by
  sorry

theorem proof_gap_exercise_1436_5
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (x * (Real.rpow (x - 1) (((3 : ℝ))⁻¹)))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((iteratedDeriv 1 (fun t => y t) x) = (((4 * x) - 3) /. (3 * (Real.rpow (x - 1) (2 /. 3))))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → (((iteratedDeriv 1 (fun t => y t) x) = 0) ↔ (x = (3 /. 4))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x < (3 /. 4))) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x > (3 /. 4))) ∧ (x ≠ 1)) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  : (lpMinimumPoints y) = ({x | x = (3 /. 4)}) := by
  sorry

theorem proof_gap_exercise_1436_6
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (x * (Real.rpow (x - 1) (((3 : ℝ))⁻¹)))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((iteratedDeriv 1 (fun t => y t) x) = (((4 * x) - 3) /. (3 * (Real.rpow (x - 1) (2 /. 3))))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → (((iteratedDeriv 1 (fun t => y t) x) = 0) ↔ (x = (3 /. 4))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x < (3 /. 4))) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x > (3 /. 4))) ∧ (x ≠ 1)) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  (h6 : (lpMinimumPoints y) = ({x | x = (3 /. 4)}))
  : (y (3 /. 4)) = ((-(3 /. 8)) * (Real.rpow (2 : ℝ) (((3 : ℝ))⁻¹))) := by
  sorry

theorem proof_gap_exercise_1436_7
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (x * (Real.rpow (x - 1) (((3 : ℝ))⁻¹)))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((iteratedDeriv 1 (fun t => y t) x) = (((4 * x) - 3) /. (3 * (Real.rpow (x - 1) (2 /. 3))))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → (((iteratedDeriv 1 (fun t => y t) x) = 0) ↔ (x = (3 /. 4))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x < (3 /. 4))) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x > (3 /. 4))) ∧ (x ≠ 1)) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  (h6 : (lpMinimumPoints y) = ({x | x = (3 /. 4)}))
  (h7 : (y (3 /. 4)) = ((-(3 /. 8)) * (Real.rpow (2 : ℝ) (((3 : ℝ))⁻¹))))
  : Tendsto (fun x : ℝ => (((iteratedDeriv 1 (fun t => y t) x) : ℝ) : EReal)) (𝓝[≠] 1) (𝓝 ⊤) := by
  sorry

theorem proof_gap_exercise_1436_8
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (x * (Real.rpow (x - 1) (((3 : ℝ))⁻¹)))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((iteratedDeriv 1 (fun t => y t) x) = (((4 * x) - 3) /. (3 * (Real.rpow (x - 1) (2 /. 3))))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → (((iteratedDeriv 1 (fun t => y t) x) = 0) ↔ (x = (3 /. 4))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x < (3 /. 4))) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x > (3 /. 4))) ∧ (x ≠ 1)) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  (h6 : (lpMinimumPoints y) = ({x | x = (3 /. 4)}))
  (h7 : (y (3 /. 4)) = ((-(3 /. 8)) * (Real.rpow (2 : ℝ) (((3 : ℝ))⁻¹))))
  (h8 : Tendsto (fun x : ℝ => (((iteratedDeriv 1 (fun t => y t) x) : ℝ) : EReal)) (𝓝[≠] 1) (𝓝 ⊤))
  : Not (1 ∈ (lpMaximumPoints y)) := by
  sorry

theorem proof_gap_exercise_1436_9
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (x * (Real.rpow (x - 1) (((3 : ℝ))⁻¹)))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((iteratedDeriv 1 (fun t => y t) x) = (((4 * x) - 3) /. (3 * (Real.rpow (x - 1) (2 /. 3))))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → (((iteratedDeriv 1 (fun t => y t) x) = 0) ↔ (x = (3 /. 4))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x < (3 /. 4))) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x > (3 /. 4))) ∧ (x ≠ 1)) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  (h6 : (lpMinimumPoints y) = ({x | x = (3 /. 4)}))
  (h7 : (y (3 /. 4)) = ((-(3 /. 8)) * (Real.rpow (2 : ℝ) (((3 : ℝ))⁻¹))))
  (h8 : Tendsto (fun x : ℝ => (((iteratedDeriv 1 (fun t => y t) x) : ℝ) : EReal)) (𝓝[≠] 1) (𝓝 ⊤))
  (h9 : Not (1 ∈ (lpMaximumPoints y)))
  : Not (1 ∈ (lpMinimumPoints y)) := by
  sorry

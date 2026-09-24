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

-- exercise: exercise_1303

theorem proof_gap_exercise_1303_1
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (x + (Real.sin x))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (1 + (Real.cos x))))) := by
  sorry

theorem proof_gap_exercise_1303_2
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (x + (Real.sin x))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (1 + (Real.cos x))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => y t) x) = (-(Real.sin x))))) := by
  sorry

theorem proof_gap_exercise_1303_3
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (x + (Real.sin x))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (1 + (Real.cos x))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => y t) x) = (-(Real.sin x))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (k : ℤ), ((((k ∈ (Set.univ : Set ℤ)) ∧ (((2 * k) * Real.pi) < x)) ∧ (x < (((2 * k) + 1) * Real.pi))) → ((iteratedDeriv 2 (fun t => y t) x) < 0))))) := by
  sorry

theorem proof_gap_exercise_1303_4
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (x + (Real.sin x))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (1 + (Real.cos x))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => y t) x) = (-(Real.sin x))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (k : ℤ), ((((k ∈ (Set.univ : Set ℤ)) ∧ (((2 * k) * Real.pi) < x)) ∧ (x < (((2 * k) + 1) * Real.pi))) → ((iteratedDeriv 2 (fun t => y t) x) < 0))))))
  : (forall (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) → (ConcaveOn ℝ (Set.Ioo ((2 * k) * Real.pi) (((2 * k) + 1) * Real.pi)) y))) := by
  sorry

theorem proof_gap_exercise_1303_5
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (x + (Real.sin x))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (1 + (Real.cos x))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => y t) x) = (-(Real.sin x))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (k : ℤ), ((((k ∈ (Set.univ : Set ℤ)) ∧ (((2 * k) * Real.pi) < x)) ∧ (x < (((2 * k) + 1) * Real.pi))) → ((iteratedDeriv 2 (fun t => y t) x) < 0))))))
  (h5 : (forall (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) → (ConcaveOn ℝ (Set.Ioo ((2 * k) * Real.pi) (((2 * k) + 1) * Real.pi)) y))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (k : ℤ), ((((k ∈ (Set.univ : Set ℤ)) ∧ ((((2 * k) + 1) * Real.pi) < x)) ∧ (x < (((2 * k) + 2) * Real.pi))) → ((iteratedDeriv 2 (fun t => y t) x) > 0))))) := by
  sorry

theorem proof_gap_exercise_1303_6
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (x + (Real.sin x))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (1 + (Real.cos x))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => y t) x) = (-(Real.sin x))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (k : ℤ), ((((k ∈ (Set.univ : Set ℤ)) ∧ (((2 * k) * Real.pi) < x)) ∧ (x < (((2 * k) + 1) * Real.pi))) → ((iteratedDeriv 2 (fun t => y t) x) < 0))))))
  (h5 : (forall (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) → (ConcaveOn ℝ (Set.Ioo ((2 * k) * Real.pi) (((2 * k) + 1) * Real.pi)) y))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (k : ℤ), ((((k ∈ (Set.univ : Set ℤ)) ∧ ((((2 * k) + 1) * Real.pi) < x)) ∧ (x < (((2 * k) + 2) * Real.pi))) → ((iteratedDeriv 2 (fun t => y t) x) > 0))))))
  : (forall (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) → (ConvexOn ℝ (Set.Ioo (((2 * k) + 1) * Real.pi) (((2 * k) + 2) * Real.pi)) y))) := by
  sorry

theorem proof_gap_exercise_1303_7
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (x + (Real.sin x))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (1 + (Real.cos x))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => y t) x) = (-(Real.sin x))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (k : ℤ), ((((k ∈ (Set.univ : Set ℤ)) ∧ (((2 * k) * Real.pi) < x)) ∧ (x < (((2 * k) + 1) * Real.pi))) → ((iteratedDeriv 2 (fun t => y t) x) < 0))))))
  (h5 : (forall (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) → (ConcaveOn ℝ (Set.Ioo ((2 * k) * Real.pi) (((2 * k) + 1) * Real.pi)) y))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (k : ℤ), ((((k ∈ (Set.univ : Set ℤ)) ∧ ((((2 * k) + 1) * Real.pi) < x)) ∧ (x < (((2 * k) + 2) * Real.pi))) → ((iteratedDeriv 2 (fun t => y t) x) > 0))))))
  (h7 : (forall (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) → (ConvexOn ℝ (Set.Ioo (((2 * k) + 1) * Real.pi) (((2 * k) + 2) * Real.pi)) y))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 2 (fun t => y t) x) = 0) ↔ (exists (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) ∧ (x = (k * Real.pi))))))) := by
  sorry

theorem proof_gap_exercise_1303_8
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (x + (Real.sin x))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (1 + (Real.cos x))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => y t) x) = (-(Real.sin x))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (k : ℤ), ((((k ∈ (Set.univ : Set ℤ)) ∧ (((2 * k) * Real.pi) < x)) ∧ (x < (((2 * k) + 1) * Real.pi))) → ((iteratedDeriv 2 (fun t => y t) x) < 0))))))
  (h5 : (forall (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) → (ConcaveOn ℝ (Set.Ioo ((2 * k) * Real.pi) (((2 * k) + 1) * Real.pi)) y))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (k : ℤ), ((((k ∈ (Set.univ : Set ℤ)) ∧ ((((2 * k) + 1) * Real.pi) < x)) ∧ (x < (((2 * k) + 2) * Real.pi))) → ((iteratedDeriv 2 (fun t => y t) x) > 0))))))
  (h7 : (forall (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) → (ConvexOn ℝ (Set.Ioo (((2 * k) + 1) * Real.pi) (((2 * k) + 2) * Real.pi)) y))))
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 2 (fun t => y t) x) = 0) ↔ (exists (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) ∧ (x = (k * Real.pi))))))))
  : ({p | (exists (k : ℤ), p = ((k * Real.pi), (y (k * Real.pi))) ∧ (k ∈ (Set.univ : Set ℤ)))}) = ({p | (exists (k : ℤ), p = ((k * Real.pi), (k * Real.pi)) ∧ (k ∈ (Set.univ : Set ℤ)))}) := by
  sorry

theorem proof_gap_exercise_1303_9
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (x + (Real.sin x))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (1 + (Real.cos x))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => y t) x) = (-(Real.sin x))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (k : ℤ), ((((k ∈ (Set.univ : Set ℤ)) ∧ (((2 * k) * Real.pi) < x)) ∧ (x < (((2 * k) + 1) * Real.pi))) → ((iteratedDeriv 2 (fun t => y t) x) < 0))))))
  (h5 : (forall (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) → (ConcaveOn ℝ (Set.Ioo ((2 * k) * Real.pi) (((2 * k) + 1) * Real.pi)) y))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (k : ℤ), ((((k ∈ (Set.univ : Set ℤ)) ∧ ((((2 * k) + 1) * Real.pi) < x)) ∧ (x < (((2 * k) + 2) * Real.pi))) → ((iteratedDeriv 2 (fun t => y t) x) > 0))))))
  (h7 : (forall (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) → (ConvexOn ℝ (Set.Ioo (((2 * k) + 1) * Real.pi) (((2 * k) + 2) * Real.pi)) y))))
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 2 (fun t => y t) x) = 0) ↔ (exists (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) ∧ (x = (k * Real.pi))))))))
  (h9 : ({p | (exists (k : ℤ), p = ((k * Real.pi), (y (k * Real.pi))) ∧ (k ∈ (Set.univ : Set ℤ)))}) = ({p | (exists (k : ℤ), p = ((k * Real.pi), (k * Real.pi)) ∧ (k ∈ (Set.univ : Set ℤ)))}))
  : (forall (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) → (((ConcaveOn ℝ (Set.Ioo ((2 * k) * Real.pi) (((2 * k) + 1) * Real.pi)) y) ∧ (ConvexOn ℝ (Set.Ioo (((2 * k) + 1) * Real.pi) (((2 * k) + 2) * Real.pi)) y)) ∧ (((k * Real.pi), (k * Real.pi)) ∈ ({p | (exists (k_1 : ℤ), p = ((k_1 * Real.pi), (k_1 * Real.pi)) ∧ (k_1 ∈ (Set.univ : Set ℤ)))}))))) → ((forall (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) → ((ConcaveOn ℝ (Set.Ioo ((2 * k) * Real.pi) (((2 * k) + 1) * Real.pi)) y) ∧ (ConvexOn ℝ (Set.Ioo (((2 * k) + 1) * Real.pi) (((2 * k) + 2) * Real.pi)) y)))) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 2 (fun t => y t) x) = 0) ↔ (exists (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) ∧ (x = (k * Real.pi)))))))) := by
  sorry

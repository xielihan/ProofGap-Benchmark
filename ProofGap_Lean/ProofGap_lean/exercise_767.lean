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

-- exercise: exercise_767

theorem proof_gap_exercise_767_1
  (y : (ℝ -> ℝ))
  (g_1 : (ℝ -> ℝ))
  (g_2 : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (x ^ (2 : ℕ))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 0)) → ((g_1 (y x)) = x))))
  : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Ici 0))) → ((g_1 t) = (Real.rpow t (((2 : ℝ))⁻¹))))) := by
  sorry

theorem proof_gap_exercise_767_2
  (y : (ℝ -> ℝ))
  (g_1 : (ℝ -> ℝ))
  (g_2 : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (x ^ (2 : ℕ))))))
  (h2 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Ici 0))) → ((g_1 t) = (Real.rpow t (((2 : ℝ))⁻¹))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≤ 0)) → ((g_2 (y x)) = x))))
  : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Ici 0))) → ((g_2 t) = (-(Real.rpow t (((2 : ℝ))⁻¹)))))) := by
  sorry

theorem proof_gap_exercise_767_3
  (y : (ℝ -> ℝ))
  (g_1 : (ℝ -> ℝ))
  (g_2 : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (x ^ (2 : ℕ))))))
  (h2 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Ici 0))) → ((g_1 t) = (Real.rpow t (((2 : ℝ))⁻¹))))))
  (h3 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Ici 0))) → ((g_2 t) = (-(Real.rpow t (((2 : ℝ))⁻¹)))))))
  : ContinuousOn g_1 (Set.Ici 0) := by
  sorry

theorem proof_gap_exercise_767_4
  (y : (ℝ -> ℝ))
  (g_1 : (ℝ -> ℝ))
  (g_2 : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (x ^ (2 : ℕ))))))
  (h2 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Ici 0))) → ((g_1 t) = (Real.rpow t (((2 : ℝ))⁻¹))))))
  (h3 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Ici 0))) → ((g_2 t) = (-(Real.rpow t (((2 : ℝ))⁻¹)))))))
  (h4 : ContinuousOn g_1 (Set.Ici 0))
  : ContinuousOn g_2 (Set.Ici 0) := by
  sorry

theorem proof_gap_exercise_767_5
  (y : (ℝ -> ℝ))
  (g_1 : (ℝ -> ℝ))
  (g_2 : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (x ^ (2 : ℕ))))))
  (h2 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Ici 0))) → ((g_1 t) = (Real.rpow t (((2 : ℝ))⁻¹))))))
  (h3 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Ici 0))) → ((g_2 t) = (-(Real.rpow t (((2 : ℝ))⁻¹)))))))
  (h4 : ContinuousOn g_1 (Set.Ici 0))
  (h5 : ContinuousOn g_2 (Set.Ici 0))
  : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Ici 0))) → (((g_1 t) = (Real.rpow t (((2 : ℝ))⁻¹))) ∧ ((g_2 t) = (-(Real.rpow t (((2 : ℝ))⁻¹))))))) → (((ContinuousOn g_1 (Set.Ici 0)) ∧ (ContinuousOn g_2 (Set.Ici 0))) ∧ (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Ici 0))) → (((y (g_1 t)) = t) ∧ ((y (g_2 t)) = t))))) := by
  sorry

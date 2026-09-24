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

-- exercise: exercise_1144

theorem proof_gap_exercise_1144_1
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (f : (ℝ -> ℝ))
  (I : (Set ℝ))
  (h1 : I ⊆ (Set.univ : Set ℝ))
  (h2 : ContDiffOn ℝ (3 : ℕ∞) f I)
  (h3 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ I)) → (((x t) = (iteratedDeriv 1 (fun t_1 => f t_1) t)) ∧ ((y t) = ((t * (iteratedDeriv 1 (fun t_1 => f t_1) t)) - (f t)))))))
  (h4 : OpenSet I)
  : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ I)) ∧ ((iteratedDeriv 2 (fun t_1 => f t_1) t) ≠ 0)) → (((lpFunDeri y x) t) = ((t * (iteratedDeriv 2 (fun t_1 => f t_1) t)) /. (iteratedDeriv 2 (fun t_1 => f t_1) t))))) := by
  sorry

theorem proof_gap_exercise_1144_2
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (f : (ℝ -> ℝ))
  (I : (Set ℝ))
  (h1 : I ⊆ (Set.univ : Set ℝ))
  (h2 : ContDiffOn ℝ (3 : ℕ∞) f I)
  (h3 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ I)) → (((x t) = (iteratedDeriv 1 (fun t_1 => f t_1) t)) ∧ ((y t) = ((t * (iteratedDeriv 1 (fun t_1 => f t_1) t)) - (f t)))))))
  (h4 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ I)) ∧ ((iteratedDeriv 2 (fun t_1 => f t_1) t) ≠ 0)) → (((lpFunDeri y x) t) = ((t * (iteratedDeriv 2 (fun t_1 => f t_1) t)) /. (iteratedDeriv 2 (fun t_1 => f t_1) t))))))
  : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ I)) ∧ ((iteratedDeriv 2 (fun t_1 => f t_1) t) ≠ 0)) → (((t * (iteratedDeriv 2 (fun t_1 => f t_1) t)) /. (iteratedDeriv 2 (fun t_1 => f t_1) t)) = t))) := by
  sorry

theorem proof_gap_exercise_1144_3
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (f : (ℝ -> ℝ))
  (I : (Set ℝ))
  (h1 : I ⊆ (Set.univ : Set ℝ))
  (h2 : ContDiffOn ℝ (3 : ℕ∞) f I)
  (h3 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ I)) → (((x t) = (iteratedDeriv 1 (fun t_1 => f t_1) t)) ∧ ((y t) = ((t * (iteratedDeriv 1 (fun t_1 => f t_1) t)) - (f t)))))))
  (h4 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ I)) ∧ ((iteratedDeriv 2 (fun t_1 => f t_1) t) ≠ 0)) → (((lpFunDeri y x) t) = ((t * (iteratedDeriv 2 (fun t_1 => f t_1) t)) /. (iteratedDeriv 2 (fun t_1 => f t_1) t))))))
  (h5 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ I)) ∧ ((iteratedDeriv 2 (fun t_1 => f t_1) t) ≠ 0)) → (((t * (iteratedDeriv 2 (fun t_1 => f t_1) t)) /. (iteratedDeriv 2 (fun t_1 => f t_1) t)) = t))))
  : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ I)) ∧ ((iteratedDeriv 2 (fun t_1 => f t_1) t) ≠ 0)) → (((lpFunDeri y x) t) = t))) := by
  sorry

theorem proof_gap_exercise_1144_4
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (f : (ℝ -> ℝ))
  (I : (Set ℝ))
  (h1 : I ⊆ (Set.univ : Set ℝ))
  (h2 : ContDiffOn ℝ (3 : ℕ∞) f I)
  (h3 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ I)) → (((x t) = (iteratedDeriv 1 (fun t_1 => f t_1) t)) ∧ ((y t) = ((t * (iteratedDeriv 1 (fun t_1 => f t_1) t)) - (f t)))))))
  (h4 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ I)) ∧ ((iteratedDeriv 2 (fun t_1 => f t_1) t) ≠ 0)) → (((lpFunDeri y x) t) = ((t * (iteratedDeriv 2 (fun t_1 => f t_1) t)) /. (iteratedDeriv 2 (fun t_1 => f t_1) t))))))
  (h5 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ I)) ∧ ((iteratedDeriv 2 (fun t_1 => f t_1) t) ≠ 0)) → (((t * (iteratedDeriv 2 (fun t_1 => f t_1) t)) /. (iteratedDeriv 2 (fun t_1 => f t_1) t)) = t))))
  (h6 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ I)) ∧ ((iteratedDeriv 2 (fun t_1 => f t_1) t) ≠ 0)) → (((lpFunDeri y x) t) = t))))
  : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ I)) ∧ ((iteratedDeriv 2 (fun t_1 => f t_1) t) ≠ 0)) → (((lpFunDeri (lpFunDeri y x) x) t) = (1 /. (iteratedDeriv 2 (fun t_1 => f t_1) t))))) := by
  sorry

theorem proof_gap_exercise_1144_5
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (f : (ℝ -> ℝ))
  (I : (Set ℝ))
  (h1 : I ⊆ (Set.univ : Set ℝ))
  (h2 : ContDiffOn ℝ (3 : ℕ∞) f I)
  (h3 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ I)) → (((x t) = (iteratedDeriv 1 (fun t_1 => f t_1) t)) ∧ ((y t) = ((t * (iteratedDeriv 1 (fun t_1 => f t_1) t)) - (f t)))))))
  (h4 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ I)) ∧ ((iteratedDeriv 2 (fun t_1 => f t_1) t) ≠ 0)) → (((lpFunDeri y x) t) = ((t * (iteratedDeriv 2 (fun t_1 => f t_1) t)) /. (iteratedDeriv 2 (fun t_1 => f t_1) t))))))
  (h5 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ I)) ∧ ((iteratedDeriv 2 (fun t_1 => f t_1) t) ≠ 0)) → (((t * (iteratedDeriv 2 (fun t_1 => f t_1) t)) /. (iteratedDeriv 2 (fun t_1 => f t_1) t)) = t))))
  (h6 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ I)) ∧ ((iteratedDeriv 2 (fun t_1 => f t_1) t) ≠ 0)) → (((lpFunDeri y x) t) = t))))
  (h7 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ I)) ∧ ((iteratedDeriv 2 (fun t_1 => f t_1) t) ≠ 0)) → (((lpFunDeri (lpFunDeri y x) x) t) = (1 /. (iteratedDeriv 2 (fun t_1 => f t_1) t))))))
  : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ I)) ∧ ((iteratedDeriv 2 (fun t_1 => f t_1) t) ≠ 0)) → (((lpFunDeri (lpFunDeri (lpFunDeri y x) x) x) t) = (-(((iteratedDeriv 3 (fun t_1 => f t_1) t) /. ((iteratedDeriv 2 (fun t_1 => f t_1) t) ^ (2 : ℕ))) /. (iteratedDeriv 2 (fun t_1 => f t_1) t)))))) := by
  sorry

theorem proof_gap_exercise_1144_6
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (f : (ℝ -> ℝ))
  (I : (Set ℝ))
  (h1 : I ⊆ (Set.univ : Set ℝ))
  (h2 : ContDiffOn ℝ (3 : ℕ∞) f I)
  (h3 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ I)) → (((x t) = (iteratedDeriv 1 (fun t_1 => f t_1) t)) ∧ ((y t) = ((t * (iteratedDeriv 1 (fun t_1 => f t_1) t)) - (f t)))))))
  (h4 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ I)) ∧ ((iteratedDeriv 2 (fun t_1 => f t_1) t) ≠ 0)) → (((lpFunDeri y x) t) = ((t * (iteratedDeriv 2 (fun t_1 => f t_1) t)) /. (iteratedDeriv 2 (fun t_1 => f t_1) t))))))
  (h5 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ I)) ∧ ((iteratedDeriv 2 (fun t_1 => f t_1) t) ≠ 0)) → (((t * (iteratedDeriv 2 (fun t_1 => f t_1) t)) /. (iteratedDeriv 2 (fun t_1 => f t_1) t)) = t))))
  (h6 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ I)) ∧ ((iteratedDeriv 2 (fun t_1 => f t_1) t) ≠ 0)) → (((lpFunDeri y x) t) = t))))
  (h7 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ I)) ∧ ((iteratedDeriv 2 (fun t_1 => f t_1) t) ≠ 0)) → (((lpFunDeri (lpFunDeri y x) x) t) = (1 /. (iteratedDeriv 2 (fun t_1 => f t_1) t))))))
  (h8 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ I)) ∧ ((iteratedDeriv 2 (fun t_1 => f t_1) t) ≠ 0)) → (((lpFunDeri (lpFunDeri (lpFunDeri y x) x) x) t) = (-(((iteratedDeriv 3 (fun t_1 => f t_1) t) /. ((iteratedDeriv 2 (fun t_1 => f t_1) t) ^ (2 : ℕ))) /. (iteratedDeriv 2 (fun t_1 => f t_1) t)))))))
  : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ I)) ∧ ((iteratedDeriv 2 (fun t_1 => f t_1) t) ≠ 0)) → ((-(((iteratedDeriv 3 (fun t_1 => f t_1) t) /. ((iteratedDeriv 2 (fun t_1 => f t_1) t) ^ (2 : ℕ))) /. (iteratedDeriv 2 (fun t_1 => f t_1) t))) = (-((iteratedDeriv 3 (fun t_1 => f t_1) t) /. ((iteratedDeriv 2 (fun t_1 => f t_1) t) ^ (3 : ℕ))))))) := by
  sorry

theorem proof_gap_exercise_1144_7
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (f : (ℝ -> ℝ))
  (I : (Set ℝ))
  (h1 : I ⊆ (Set.univ : Set ℝ))
  (h2 : ContDiffOn ℝ (3 : ℕ∞) f I)
  (h3 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ I)) → (((x t) = (iteratedDeriv 1 (fun t_1 => f t_1) t)) ∧ ((y t) = ((t * (iteratedDeriv 1 (fun t_1 => f t_1) t)) - (f t)))))))
  (h4 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ I)) ∧ ((iteratedDeriv 2 (fun t_1 => f t_1) t) ≠ 0)) → (((lpFunDeri y x) t) = ((t * (iteratedDeriv 2 (fun t_1 => f t_1) t)) /. (iteratedDeriv 2 (fun t_1 => f t_1) t))))))
  (h5 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ I)) ∧ ((iteratedDeriv 2 (fun t_1 => f t_1) t) ≠ 0)) → (((t * (iteratedDeriv 2 (fun t_1 => f t_1) t)) /. (iteratedDeriv 2 (fun t_1 => f t_1) t)) = t))))
  (h6 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ I)) ∧ ((iteratedDeriv 2 (fun t_1 => f t_1) t) ≠ 0)) → (((lpFunDeri y x) t) = t))))
  (h7 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ I)) ∧ ((iteratedDeriv 2 (fun t_1 => f t_1) t) ≠ 0)) → (((lpFunDeri (lpFunDeri y x) x) t) = (1 /. (iteratedDeriv 2 (fun t_1 => f t_1) t))))))
  (h8 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ I)) ∧ ((iteratedDeriv 2 (fun t_1 => f t_1) t) ≠ 0)) → (((lpFunDeri (lpFunDeri (lpFunDeri y x) x) x) t) = (-(((iteratedDeriv 3 (fun t_1 => f t_1) t) /. ((iteratedDeriv 2 (fun t_1 => f t_1) t) ^ (2 : ℕ))) /. (iteratedDeriv 2 (fun t_1 => f t_1) t)))))))
  (h9 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ I)) ∧ ((iteratedDeriv 2 (fun t_1 => f t_1) t) ≠ 0)) → ((-(((iteratedDeriv 3 (fun t_1 => f t_1) t) /. ((iteratedDeriv 2 (fun t_1 => f t_1) t) ^ (2 : ℕ))) /. (iteratedDeriv 2 (fun t_1 => f t_1) t))) = (-((iteratedDeriv 3 (fun t_1 => f t_1) t) /. ((iteratedDeriv 2 (fun t_1 => f t_1) t) ^ (3 : ℕ))))))))
  : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ I)) ∧ ((iteratedDeriv 2 (fun t_1 => f t_1) t) ≠ 0)) → (((lpFunDeri (lpFunDeri (lpFunDeri y x) x) x) t) = (-((iteratedDeriv 3 (fun t_1 => f t_1) t) /. ((iteratedDeriv 2 (fun t_1 => f t_1) t) ^ (3 : ℕ))))))) := by
  sorry

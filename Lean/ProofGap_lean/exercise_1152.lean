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

-- exercise: exercise_1152

theorem proof_gap_exercise_1152_1
  (s : (ℝ -> ℝ))
  (v : (ℝ -> ℝ))
  (w : (ℝ -> ℝ))
  (h1 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((s t) = ((10 + (20 * t)) - (5 * (t ^ (2 : ℕ))))))))
  (h2 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((v t) = (20 - (10 * t))))))
  : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((v t) = (iteratedDeriv 1 (fun t_1 => s t_1) t)))) := by
  sorry

theorem proof_gap_exercise_1152_2
  (s : (ℝ -> ℝ))
  (v : (ℝ -> ℝ))
  (w : (ℝ -> ℝ))
  (h1 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((s t) = ((10 + (20 * t)) - (5 * (t ^ (2 : ℕ))))))))
  (h2 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((v t) = (iteratedDeriv 1 (fun t_1 => s t_1) t)))))
  : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((v t) = (20 - (10 * t))))) := by
  sorry

theorem proof_gap_exercise_1152_3
  (s : (ℝ -> ℝ))
  (v : (ℝ -> ℝ))
  (w : (ℝ -> ℝ))
  (h1 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((s t) = ((10 + (20 * t)) - (5 * (t ^ (2 : ℕ))))))))
  (h2 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((v t) = (iteratedDeriv 1 (fun t_1 => s t_1) t)))))
  (h3 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((v t) = (20 - (10 * t))))))
  : (v (2 : ℝ)) = 0 := by
  sorry

theorem proof_gap_exercise_1152_4
  (s : (ℝ -> ℝ))
  (v : (ℝ -> ℝ))
  (w : (ℝ -> ℝ))
  (h1 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((s t) = ((10 + (20 * t)) - (5 * (t ^ (2 : ℕ))))))))
  (h2 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((v t) = (iteratedDeriv 1 (fun t_1 => s t_1) t)))))
  (h3 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((v t) = (20 - (10 * t))))))
  (h4 : (v (2 : ℝ)) = 0)
  (h5 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((w t) = (-(10 : ℝ))))))
  : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((w t) = (iteratedDeriv 2 (fun t_1 => s t_1) t)))) := by
  sorry

theorem proof_gap_exercise_1152_5
  (s : (ℝ -> ℝ))
  (v : (ℝ -> ℝ))
  (w : (ℝ -> ℝ))
  (h1 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((s t) = ((10 + (20 * t)) - (5 * (t ^ (2 : ℕ))))))))
  (h2 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((v t) = (iteratedDeriv 1 (fun t_1 => s t_1) t)))))
  (h3 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((v t) = (20 - (10 * t))))))
  (h4 : (v (2 : ℝ)) = 0)
  (h5 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((w t) = (iteratedDeriv 2 (fun t_1 => s t_1) t)))))
  : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((w t) = (-(10 : ℝ))))) := by
  sorry

theorem proof_gap_exercise_1152_6
  (s : (ℝ -> ℝ))
  (v : (ℝ -> ℝ))
  (w : (ℝ -> ℝ))
  (h1 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((s t) = ((10 + (20 * t)) - (5 * (t ^ (2 : ℕ))))))))
  (h2 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((v t) = (iteratedDeriv 1 (fun t_1 => s t_1) t)))))
  (h3 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((v t) = (20 - (10 * t))))))
  (h4 : (v (2 : ℝ)) = 0)
  (h5 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((w t) = (iteratedDeriv 2 (fun t_1 => s t_1) t)))))
  (h6 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((w t) = (-(10 : ℝ))))))
  : (w (2 : ℝ)) = (-(10 : ℝ)) := by
  sorry

theorem proof_gap_exercise_1152_7
  (s : (ℝ -> ℝ))
  (v : (ℝ -> ℝ))
  (w : (ℝ -> ℝ))
  (h1 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((s t) = ((10 + (20 * t)) - (5 * (t ^ (2 : ℕ))))))))
  (h2 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((v t) = (iteratedDeriv 1 (fun t_1 => s t_1) t)))))
  (h3 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((v t) = (20 - (10 * t))))))
  (h4 : (v (2 : ℝ)) = 0)
  (h5 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((w t) = (iteratedDeriv 2 (fun t_1 => s t_1) t)))))
  (h6 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((w t) = (-(10 : ℝ))))))
  (h7 : (w (2 : ℝ)) = (-(10 : ℝ)))
  : (v, w, (v (2 : ℝ)), (w (2 : ℝ))) = ((fun (t : ℝ) => (20 - (10 * t))), (fun (t : ℝ) => (-(10 : ℝ))), 0, (-(10 : ℝ))) := by
  sorry

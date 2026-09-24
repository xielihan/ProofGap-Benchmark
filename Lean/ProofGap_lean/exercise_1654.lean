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

-- exercise: exercise_1654

theorem proof_gap_exercise_1654_1
  (f : (ℝ -> ℝ))
  (F : (ℝ -> ℝ))
  (F_1 : (ℝ -> ℝ))
  (F_2 : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (I : (Set ℝ))
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : I ⊆ (Set.univ : Set ℝ))
  (h4 : a ≠ 0)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((a * x) + b) ∈ I))))
  (h6 : ({F_1_1 : (ℝ -> ℝ) | (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → ((iteratedDeriv 1 (fun t => F_1_1 t) x) = ((f x) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_2_1 : (ℝ -> ℝ) | (exists (C : ℝ), ((C ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → ((F_2_1 x) = ((F x) + C))))))}))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → ((iteratedDeriv 1 (fun t => F t) x) = (f x)))) := by
  sorry

theorem proof_gap_exercise_1654_2
  (f : (ℝ -> ℝ))
  (F : (ℝ -> ℝ))
  (F_1 : (ℝ -> ℝ))
  (F_2 : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (I : (Set ℝ))
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : I ⊆ (Set.univ : Set ℝ))
  (h4 : a ≠ 0)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((a * x) + b) ∈ I))))
  (h6 : ({F_1_1 : (ℝ -> ℝ) | (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → ((iteratedDeriv 1 (fun t => F_1_1 t) x) = ((f x) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_2_1 : (ℝ -> ℝ) | (exists (C : ℝ), ((C ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → ((F_2_1 x) = ((F x) + C))))))}))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → ((iteratedDeriv 1 (fun t => F t) x) = (f x)))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F t) ((a * x) + b)) = (f ((a * x) + b))))) := by
  sorry

theorem proof_gap_exercise_1654_3
  (f : (ℝ -> ℝ))
  (F : (ℝ -> ℝ))
  (F_1 : (ℝ -> ℝ))
  (F_2 : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (I : (Set ℝ))
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : I ⊆ (Set.univ : Set ℝ))
  (h4 : a ≠ 0)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((a * x) + b) ∈ I))))
  (h6 : ({F_1_1 : (ℝ -> ℝ) | (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → ((iteratedDeriv 1 (fun t => F_1_1 t) x) = ((f x) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_2_1 : (ℝ -> ℝ) | (exists (C : ℝ), ((C ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → ((F_2_1 x) = ((F x) + C))))))}))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → ((iteratedDeriv 1 (fun t => F t) x) = (f x)))))
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F t) ((a * x) + b)) = (f ((a * x) + b))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => ((1 /. a) * (F ((a * t) + b)))) x) = (iteratedDeriv 1 (fun t => F t) ((a * x) + b))))) := by
  sorry

theorem proof_gap_exercise_1654_4
  (f : (ℝ -> ℝ))
  (F : (ℝ -> ℝ))
  (F_1 : (ℝ -> ℝ))
  (F_2 : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (I : (Set ℝ))
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : I ⊆ (Set.univ : Set ℝ))
  (h4 : a ≠ 0)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((a * x) + b) ∈ I))))
  (h6 : ({F_1_1 : (ℝ -> ℝ) | (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → ((iteratedDeriv 1 (fun t => F_1_1 t) x) = ((f x) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_2_1 : (ℝ -> ℝ) | (exists (C : ℝ), ((C ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → ((F_2_1 x) = ((F x) + C))))))}))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → ((iteratedDeriv 1 (fun t => F t) x) = (f x)))))
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F t) ((a * x) + b)) = (f ((a * x) + b))))))
  (h9 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => ((1 /. a) * (F ((a * t) + b)))) x) = (iteratedDeriv 1 (fun t => F t) ((a * x) + b))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => ((1 /. a) * (F ((a * t) + b)))) x) = (f ((a * x) + b))))) := by
  sorry

theorem proof_gap_exercise_1654_5
  (f : (ℝ -> ℝ))
  (F : (ℝ -> ℝ))
  (F_1 : (ℝ -> ℝ))
  (F_2 : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (I : (Set ℝ))
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : I ⊆ (Set.univ : Set ℝ))
  (h4 : a ≠ 0)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((a * x) + b) ∈ I))))
  (h6 : ({F_1_1 : (ℝ -> ℝ) | (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → ((iteratedDeriv 1 (fun t => F_1_1 t) x) = ((f x) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_2_1 : (ℝ -> ℝ) | (exists (C : ℝ), ((C ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → ((F_2_1 x) = ((F x) + C))))))}))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → ((iteratedDeriv 1 (fun t => F t) x) = (f x)))))
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F t) ((a * x) + b)) = (f ((a * x) + b))))))
  (h9 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => ((1 /. a) * (F ((a * t) + b)))) x) = (iteratedDeriv 1 (fun t => F t) ((a * x) + b))))))
  (h10 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => ((1 /. a) * (F ((a * t) + b)))) x) = (f ((a * x) + b))))))
  : ({F_5 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_5 t) x) = ((f ((a * x) + b)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_6 : (ℝ -> ℝ) | (exists (C : ℝ), ((C ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_6 x) = (((1 /. a) * (F ((a * x) + b))) + C))))))}) := by
  sorry

theorem proof_gap_exercise_1654_6
  (f : (ℝ -> ℝ))
  (F : (ℝ -> ℝ))
  (F_1 : (ℝ -> ℝ))
  (F_2 : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (I : (Set ℝ))
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : I ⊆ (Set.univ : Set ℝ))
  (h4 : a ≠ 0)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((a * x) + b) ∈ I))))
  (h6 : ({F_1_1 : (ℝ -> ℝ) | (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → ((iteratedDeriv 1 (fun t => F_1_1 t) x) = ((f x) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_2_1 : (ℝ -> ℝ) | (exists (C : ℝ), ((C ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → ((F_2_1 x) = ((F x) + C))))))}))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → ((iteratedDeriv 1 (fun t => F t) x) = (f x)))))
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F t) ((a * x) + b)) = (f ((a * x) + b))))))
  (h9 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => ((1 /. a) * (F ((a * t) + b)))) x) = (iteratedDeriv 1 (fun t => F t) ((a * x) + b))))))
  (h10 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => ((1 /. a) * (F ((a * t) + b)))) x) = (f ((a * x) + b))))))
  (h11 : ({F_5 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_5 t) x) = ((f ((a * x) + b)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_6 : (ℝ -> ℝ) | (exists (C : ℝ), ((C ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_6 x) = (((1 /. a) * (F ((a * x) + b))) + C))))))}))
  : ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = ((f ((a * x) + b)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (C : ℝ), ((C ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_4 x) = (((1 /. a) * (F ((a * x) + b))) + C))))))}) := by
  sorry

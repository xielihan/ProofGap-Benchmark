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

-- exercise: exercise_1424

theorem proof_gap_exercise_1424_1
  (P : (ℝ -> ℝ))
  (Q : (ℝ -> ℝ))
  (P_1 : (ℝ -> ℝ))
  (f : (ℝ -> ℝ))
  (I : (Set ℝ))
  (x_0 : ℝ)
  (h1 : I ⊆ (Set.univ : Set ℝ))
  (h2 : x_0 ∈ (Set.univ : Set ℝ))
  (h3 : x_0 ∈ I)
  (h4 : DifferentiableOn ℝ P I)
  (h5 : DifferentiableOn ℝ Q I)
  (h6 : DifferentiableOn ℝ P_1 I)
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → ((Q x) ≠ 0))))
  (h8 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → ((f x) = ((P x) /. (Q x))))))
  (h9 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → ((iteratedDeriv 1 (fun t => f t) x) = ((P_1 x) /. ((Q x) ^ (2 : ℕ)))))))
  (h10 : (P_1 x_0) = 0)
  (h11 : (Q x_0) ≠ 0)
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → ((iteratedDeriv 2 (fun t => f t) x) = ((((iteratedDeriv 1 (fun t => P_1 t) x) * ((Q x) ^ (2 : ℕ))) - (((2 * (Q x)) * (iteratedDeriv 1 (fun t => Q t) x)) * (P_1 x))) /. ((Q x) ^ (4 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_1424_2
  (P : (ℝ -> ℝ))
  (Q : (ℝ -> ℝ))
  (P_1 : (ℝ -> ℝ))
  (f : (ℝ -> ℝ))
  (I : (Set ℝ))
  (x_0 : ℝ)
  (h1 : I ⊆ (Set.univ : Set ℝ))
  (h2 : x_0 ∈ (Set.univ : Set ℝ))
  (h3 : x_0 ∈ I)
  (h4 : DifferentiableOn ℝ P I)
  (h5 : DifferentiableOn ℝ Q I)
  (h6 : DifferentiableOn ℝ P_1 I)
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → ((Q x) ≠ 0))))
  (h8 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → ((f x) = ((P x) /. (Q x))))))
  (h9 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → ((iteratedDeriv 1 (fun t => f t) x) = ((P_1 x) /. ((Q x) ^ (2 : ℕ)))))))
  (h10 : (P_1 x_0) = 0)
  (h11 : (Q x_0) ≠ 0)
  (h12 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → ((iteratedDeriv 2 (fun t => f t) x) = ((((iteratedDeriv 1 (fun t => P_1 t) x) * ((Q x) ^ (2 : ℕ))) - (((2 * (Q x)) * (iteratedDeriv 1 (fun t => Q t) x)) * (P_1 x))) /. ((Q x) ^ (4 : ℕ)))))))
  : (iteratedDeriv 2 (fun t => f t) x_0) = ((((iteratedDeriv 1 (fun t => P_1 t) x_0) * ((Q x_0) ^ (2 : ℕ))) - (((2 * (Q x_0)) * (iteratedDeriv 1 (fun t => Q t) x_0)) * (P_1 x_0))) /. ((Q x_0) ^ (4 : ℕ))) := by
  sorry

theorem proof_gap_exercise_1424_3
  (P : (ℝ -> ℝ))
  (Q : (ℝ -> ℝ))
  (P_1 : (ℝ -> ℝ))
  (f : (ℝ -> ℝ))
  (I : (Set ℝ))
  (x_0 : ℝ)
  (h1 : I ⊆ (Set.univ : Set ℝ))
  (h2 : x_0 ∈ (Set.univ : Set ℝ))
  (h3 : x_0 ∈ I)
  (h4 : DifferentiableOn ℝ P I)
  (h5 : DifferentiableOn ℝ Q I)
  (h6 : DifferentiableOn ℝ P_1 I)
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → ((Q x) ≠ 0))))
  (h8 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → ((f x) = ((P x) /. (Q x))))))
  (h9 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → ((iteratedDeriv 1 (fun t => f t) x) = ((P_1 x) /. ((Q x) ^ (2 : ℕ)))))))
  (h10 : (P_1 x_0) = 0)
  (h11 : (Q x_0) ≠ 0)
  (h12 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → ((iteratedDeriv 2 (fun t => f t) x) = ((((iteratedDeriv 1 (fun t => P_1 t) x) * ((Q x) ^ (2 : ℕ))) - (((2 * (Q x)) * (iteratedDeriv 1 (fun t => Q t) x)) * (P_1 x))) /. ((Q x) ^ (4 : ℕ)))))))
  (h13 : (iteratedDeriv 2 (fun t => f t) x_0) = ((((iteratedDeriv 1 (fun t => P_1 t) x_0) * ((Q x_0) ^ (2 : ℕ))) - (((2 * (Q x_0)) * (iteratedDeriv 1 (fun t => Q t) x_0)) * (P_1 x_0))) /. ((Q x_0) ^ (4 : ℕ))))
  : (iteratedDeriv 2 (fun t => f t) x_0) = ((iteratedDeriv 1 (fun t => P_1 t) x_0) /. ((Q x_0) ^ (2 : ℕ))) := by
  sorry

theorem proof_gap_exercise_1424_4
  (P : (ℝ -> ℝ))
  (Q : (ℝ -> ℝ))
  (P_1 : (ℝ -> ℝ))
  (f : (ℝ -> ℝ))
  (I : (Set ℝ))
  (x_0 : ℝ)
  (h1 : I ⊆ (Set.univ : Set ℝ))
  (h2 : x_0 ∈ (Set.univ : Set ℝ))
  (h3 : x_0 ∈ I)
  (h4 : DifferentiableOn ℝ P I)
  (h5 : DifferentiableOn ℝ Q I)
  (h6 : DifferentiableOn ℝ P_1 I)
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → ((Q x) ≠ 0))))
  (h8 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → ((f x) = ((P x) /. (Q x))))))
  (h9 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → ((iteratedDeriv 1 (fun t => f t) x) = ((P_1 x) /. ((Q x) ^ (2 : ℕ)))))))
  (h10 : (P_1 x_0) = 0)
  (h11 : (Q x_0) ≠ 0)
  (h12 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → ((iteratedDeriv 2 (fun t => f t) x) = ((((iteratedDeriv 1 (fun t => P_1 t) x) * ((Q x) ^ (2 : ℕ))) - (((2 * (Q x)) * (iteratedDeriv 1 (fun t => Q t) x)) * (P_1 x))) /. ((Q x) ^ (4 : ℕ)))))))
  (h13 : (iteratedDeriv 2 (fun t => f t) x_0) = ((((iteratedDeriv 1 (fun t => P_1 t) x_0) * ((Q x_0) ^ (2 : ℕ))) - (((2 * (Q x_0)) * (iteratedDeriv 1 (fun t => Q t) x_0)) * (P_1 x_0))) /. ((Q x_0) ^ (4 : ℕ))))
  (h14 : (iteratedDeriv 2 (fun t => f t) x_0) = ((iteratedDeriv 1 (fun t => P_1 t) x_0) /. ((Q x_0) ^ (2 : ℕ))))
  : ((Q x_0) ^ (2 : ℕ)) > 0 := by
  sorry

theorem proof_gap_exercise_1424_5
  (P : (ℝ -> ℝ))
  (Q : (ℝ -> ℝ))
  (P_1 : (ℝ -> ℝ))
  (f : (ℝ -> ℝ))
  (I : (Set ℝ))
  (x_0 : ℝ)
  (h1 : I ⊆ (Set.univ : Set ℝ))
  (h2 : x_0 ∈ (Set.univ : Set ℝ))
  (h3 : x_0 ∈ I)
  (h4 : DifferentiableOn ℝ P I)
  (h5 : DifferentiableOn ℝ Q I)
  (h6 : DifferentiableOn ℝ P_1 I)
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → ((Q x) ≠ 0))))
  (h8 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → ((f x) = ((P x) /. (Q x))))))
  (h9 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → ((iteratedDeriv 1 (fun t => f t) x) = ((P_1 x) /. ((Q x) ^ (2 : ℕ)))))))
  (h10 : (P_1 x_0) = 0)
  (h11 : (Q x_0) ≠ 0)
  (h12 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → ((iteratedDeriv 2 (fun t => f t) x) = ((((iteratedDeriv 1 (fun t => P_1 t) x) * ((Q x) ^ (2 : ℕ))) - (((2 * (Q x)) * (iteratedDeriv 1 (fun t => Q t) x)) * (P_1 x))) /. ((Q x) ^ (4 : ℕ)))))))
  (h13 : (iteratedDeriv 2 (fun t => f t) x_0) = ((((iteratedDeriv 1 (fun t => P_1 t) x_0) * ((Q x_0) ^ (2 : ℕ))) - (((2 * (Q x_0)) * (iteratedDeriv 1 (fun t => Q t) x_0)) * (P_1 x_0))) /. ((Q x_0) ^ (4 : ℕ))))
  (h14 : (iteratedDeriv 2 (fun t => f t) x_0) = ((iteratedDeriv 1 (fun t => P_1 t) x_0) /. ((Q x_0) ^ (2 : ℕ))))
  (h15 : ((Q x_0) ^ (2 : ℕ)) > 0)
  : (SignType.sign (iteratedDeriv 2 (fun t => f t) x_0) : ℝ) = (SignType.sign (iteratedDeriv 1 (fun t => P_1 t) x_0) : ℝ) := by
  sorry

theorem proof_gap_exercise_1424_6
  (P : (ℝ -> ℝ))
  (Q : (ℝ -> ℝ))
  (P_1 : (ℝ -> ℝ))
  (f : (ℝ -> ℝ))
  (I : (Set ℝ))
  (x_0 : ℝ)
  (h1 : I ⊆ (Set.univ : Set ℝ))
  (h2 : x_0 ∈ (Set.univ : Set ℝ))
  (h3 : x_0 ∈ I)
  (h4 : DifferentiableOn ℝ P I)
  (h5 : DifferentiableOn ℝ Q I)
  (h6 : DifferentiableOn ℝ P_1 I)
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → ((Q x) ≠ 0))))
  (h8 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → ((f x) = ((P x) /. (Q x))))))
  (h9 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → ((iteratedDeriv 1 (fun t => f t) x) = ((P_1 x) /. ((Q x) ^ (2 : ℕ)))))))
  (h10 : (P_1 x_0) = 0)
  (h11 : (Q x_0) ≠ 0)
  (h12 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ I)) → ((iteratedDeriv 2 (fun t => f t) x) = ((((iteratedDeriv 1 (fun t => P_1 t) x) * ((Q x) ^ (2 : ℕ))) - (((2 * (Q x)) * (iteratedDeriv 1 (fun t => Q t) x)) * (P_1 x))) /. ((Q x) ^ (4 : ℕ)))))))
  (h13 : (iteratedDeriv 2 (fun t => f t) x_0) = ((((iteratedDeriv 1 (fun t => P_1 t) x_0) * ((Q x_0) ^ (2 : ℕ))) - (((2 * (Q x_0)) * (iteratedDeriv 1 (fun t => Q t) x_0)) * (P_1 x_0))) /. ((Q x_0) ^ (4 : ℕ))))
  (h14 : (iteratedDeriv 2 (fun t => f t) x_0) = ((iteratedDeriv 1 (fun t => P_1 t) x_0) /. ((Q x_0) ^ (2 : ℕ))))
  (h15 : ((Q x_0) ^ (2 : ℕ)) > 0)
  (h16 : (SignType.sign (iteratedDeriv 2 (fun t => f t) x_0) : ℝ) = (SignType.sign (iteratedDeriv 1 (fun t => P_1 t) x_0) : ℝ))
  : (SignType.sign (iteratedDeriv 2 (fun t => f t) x_0) : ℝ) = (SignType.sign (iteratedDeriv 1 (fun t => P_1 t) x_0) : ℝ) := by
  sorry

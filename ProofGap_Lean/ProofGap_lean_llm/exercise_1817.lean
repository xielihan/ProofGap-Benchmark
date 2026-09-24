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

abbrev SetValueAt (S : Set (ℝ -> ℝ)) (x value : ℝ) : Prop := ∃ F ∈ S, F x = value

-- exercise: exercise_1817

theorem proof_gap_exercise_1817_1
  (a : ℝ)
  (C : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((a ^ (2 : ℕ)) + (x ^ (2 : ℕ))) ≠ 0))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (a = 0)) → (x ≠ 0))) := by
  sorry

theorem proof_gap_exercise_1817_2
  (a : ℝ)
  (C : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((a ^ (2 : ℕ)) + (x ^ (2 : ℕ))) ≠ 0))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (a = 0)) → (x ≠ 0))))
  : (a = 0) → (({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((1 /. (((a ^ (2 : ℕ)) + (x ^ (2 : ℕ))) ^ (2 : ℕ))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = ((1 /. (x ^ (4 : ℕ))) * (iteratedDeriv 1 (fun t => t) x)))))})) := by
  sorry

theorem proof_gap_exercise_1817_3
  (a : ℝ)
  (C : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((a ^ (2 : ℕ)) + (x ^ (2 : ℕ))) ≠ 0))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (a = 0)) → (x ≠ 0))))
  (h5 : (a = 0) → (({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((1 /. (((a ^ (2 : ℕ)) + (x ^ (2 : ℕ))) ^ (2 : ℕ))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = ((1 /. (x ^ (4 : ℕ))) * (iteratedDeriv 1 (fun t => t) x)))))})))
  : (a = 0) → (({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = ((1 /. (x ^ (4 : ℕ))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_4 x) = ((-(1 /. (3 * (x ^ (3 : ℕ))))) + C_1))))))})) := by
  sorry

theorem proof_gap_exercise_1817_4
  (a : ℝ)
  (C : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((a ^ (2 : ℕ)) + (x ^ (2 : ℕ))) ≠ 0))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (a = 0)) → (x ≠ 0))))
  (h5 : (a = 0) → (({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((1 /. (((a ^ (2 : ℕ)) + (x ^ (2 : ℕ))) ^ (2 : ℕ))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = ((1 /. (x ^ (4 : ℕ))) * (iteratedDeriv 1 (fun t => t) x)))))})))
  (h6 : (a = 0) → (({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = ((1 /. (x ^ (4 : ℕ))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_4 x) = ((-(1 /. (3 * (x ^ (3 : ℕ))))) + C_1))))))})))
  : (a = 0) → (({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((1 /. (((a ^ (2 : ℕ)) + (x ^ (2 : ℕ))) ^ (2 : ℕ))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_4 x) = ((-(1 /. (3 * (x ^ (3 : ℕ))))) + C_1))))))})) := by
  sorry

theorem proof_gap_exercise_1817_5
  (a : ℝ)
  (C : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((a ^ (2 : ℕ)) + (x ^ (2 : ℕ))) ≠ 0))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (a = 0)) → (x ≠ 0))))
  (h5 : (a = 0) → (({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((1 /. (((a ^ (2 : ℕ)) + (x ^ (2 : ℕ))) ^ (2 : ℕ))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = ((1 /. (x ^ (4 : ℕ))) * (iteratedDeriv 1 (fun t => t) x)))))})))
  (h6 : (a = 0) → (({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = ((1 /. (x ^ (4 : ℕ))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_4 x) = ((-(1 /. (3 * (x ^ (3 : ℕ))))) + C_1))))))})))
  (h7 : (a = 0) → (({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((1 /. (((a ^ (2 : ℕ)) + (x ^ (2 : ℕ))) ^ (2 : ℕ))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_4 x) = ((-(1 /. (3 * (x ^ (3 : ℕ))))) + C_1))))))})))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (a ≠ 0)) → SetValueAt ({F_5 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_5 t) x_1) = ((1 /. ((x_1 ^ (2 : ℕ)) + (a ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => t) x_1)))))} : Set (ℝ -> ℝ)) x ((1 /. a) * (Real.arctan (x /. a))))) := by
  sorry

theorem proof_gap_exercise_1817_6
  (a : ℝ)
  (C : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((a ^ (2 : ℕ)) + (x ^ (2 : ℕ))) ≠ 0))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (a = 0)) → (x ≠ 0))))
  (h5 : (a = 0) → (({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((1 /. (((a ^ (2 : ℕ)) + (x ^ (2 : ℕ))) ^ (2 : ℕ))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = ((1 /. (x ^ (4 : ℕ))) * (iteratedDeriv 1 (fun t => t) x)))))})))
  (h6 : (a = 0) → (({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = ((1 /. (x ^ (4 : ℕ))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_4 x) = ((-(1 /. (3 * (x ^ (3 : ℕ))))) + C_1))))))})))
  (h7 : (a = 0) → (({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((1 /. (((a ^ (2 : ℕ)) + (x ^ (2 : ℕ))) ^ (2 : ℕ))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_4 x) = ((-(1 /. (3 * (x ^ (3 : ℕ))))) + C_1))))))})))
  (h8 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (a ≠ 0)) → SetValueAt ({F_5 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_5 t) x_1) = ((1 /. ((x_1 ^ (2 : ℕ)) + (a ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => t) x_1)))))} : Set (ℝ -> ℝ)) x ((1 /. a) * (Real.arctan (x /. a))))))
  : (a ≠ 0) → (({F_6 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_6 t) x) = ((1 /. ((x ^ (2 : ℕ)) + (a ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_10 : (ℝ -> ℝ) | (exists (F_7 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_7 t) x) = (((((x ^ (2 : ℕ)) + (a ^ (2 : ℕ))) - (a ^ (2 : ℕ))) /. (((x ^ (2 : ℕ)) + (a ^ (2 : ℕ))) ^ (2 : ℕ))) * (iteratedDeriv 1 (fun t => t) x))) ∧ ((F_10 x) = ((x /. ((x ^ (2 : ℕ)) + (a ^ (2 : ℕ)))) + (2 * (F_7 x))))))))})) := by
  sorry

theorem proof_gap_exercise_1817_7
  (a : ℝ)
  (C : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((a ^ (2 : ℕ)) + (x ^ (2 : ℕ))) ≠ 0))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (a = 0)) → (x ≠ 0))))
  (h5 : (a = 0) → (({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((1 /. (((a ^ (2 : ℕ)) + (x ^ (2 : ℕ))) ^ (2 : ℕ))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = ((1 /. (x ^ (4 : ℕ))) * (iteratedDeriv 1 (fun t => t) x)))))})))
  (h6 : (a = 0) → (({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = ((1 /. (x ^ (4 : ℕ))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_4 x) = ((-(1 /. (3 * (x ^ (3 : ℕ))))) + C_1))))))})))
  (h7 : (a = 0) → (({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((1 /. (((a ^ (2 : ℕ)) + (x ^ (2 : ℕ))) ^ (2 : ℕ))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_4 x) = ((-(1 /. (3 * (x ^ (3 : ℕ))))) + C_1))))))})))
  (h8 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (a ≠ 0)) → SetValueAt ({F_5 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_5 t) x_1) = ((1 /. ((x_1 ^ (2 : ℕ)) + (a ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => t) x_1)))))} : Set (ℝ -> ℝ)) x ((1 /. a) * (Real.arctan (x /. a))))))
  (h9 : (a ≠ 0) → (({F_6 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_6 t) x) = ((1 /. ((x ^ (2 : ℕ)) + (a ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_10 : (ℝ -> ℝ) | (exists (F_7 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_7 t) x) = (((((x ^ (2 : ℕ)) + (a ^ (2 : ℕ))) - (a ^ (2 : ℕ))) /. (((x ^ (2 : ℕ)) + (a ^ (2 : ℕ))) ^ (2 : ℕ))) * (iteratedDeriv 1 (fun t => t) x))) ∧ ((F_10 x) = ((x /. ((x ^ (2 : ℕ)) + (a ^ (2 : ℕ)))) + (2 * (F_7 x))))))))})))
  : (a ≠ 0) → (({F_11 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_11 t) x) = ((1 /. (((x ^ (2 : ℕ)) + (a ^ (2 : ℕ))) ^ (2 : ℕ))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_12 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_12 x) = (((1 /. (2 * (a ^ (2 : ℕ)))) * ((x /. ((x ^ (2 : ℕ)) + (a ^ (2 : ℕ)))) + ((1 /. a) * (Real.arctan (x /. a))))) + C_1))))))})) := by
  sorry

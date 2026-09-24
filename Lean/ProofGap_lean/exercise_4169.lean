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

-- exercise: exercise_4169

theorem proof_gap_exercise_4169_1
  (p : ℝ)
  (q : ℝ)
  (I : ℝ)
  (h1 : (p ∈ (Set.univ : Set ℝ)) ∧ (p ∈ ({x_1 : ℝ | 0 < x_1})))
  (h2 : (q ∈ (Set.univ : Set ℝ)) ∧ (q ∈ ({x_1 : ℝ | 0 < x_1})))
  (h3 : I ∈ (Set.univ : Set ℝ))
  (h4 : I = (∫ x in Set.Ioi (1 : ℝ), ((((1 : ℝ) /. (Real.rpow x p)) * (∫ y in Set.Ioi (1 /. x), (((1 : ℝ) /. (Real.rpow y q)) * (1 : ℝ)))) * (1 : ℝ))))
  : I = (∫ x in Set.Ioi (1 : ℝ), ((((1 : ℝ) /. (Real.rpow x p)) * (∫ y in Set.Ioi (1 /. x), (((1 : ℝ) /. (Real.rpow y q)) * (1 : ℝ)))) * (1 : ℝ))) := by
  sorry

theorem proof_gap_exercise_4169_2
  (p : ℝ)
  (q : ℝ)
  (I : ℝ)
  (h1 : (p ∈ (Set.univ : Set ℝ)) ∧ (p ∈ ({x_1 : ℝ | 0 < x_1})))
  (h2 : (q ∈ (Set.univ : Set ℝ)) ∧ (q ∈ ({x_1 : ℝ | 0 < x_1})))
  (h3 : I ∈ (Set.univ : Set ℝ))
  (h4 : I = (∫ x in Set.Ioi (1 : ℝ), ((((1 : ℝ) /. (Real.rpow x p)) * (∫ y in Set.Ioi (1 /. x), (((1 : ℝ) /. (Real.rpow y q)) * (1 : ℝ)))) * (1 : ℝ))))
  (h5 : I = (∫ x in Set.Ioi (1 : ℝ), ((((1 : ℝ) /. (Real.rpow x p)) * (∫ y in Set.Ioi (1 /. x), (((1 : ℝ) /. (Real.rpow y q)) * (1 : ℝ)))) * (1 : ℝ))))
  : (q > 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 1)) → ((∫ y in Set.Ioi (1 /. x), (((1 : ℝ) /. (Real.rpow y q)) * (1 : ℝ))) = ((Real.rpow x (q - 1)) /. (q - 1))))) := by
  sorry

theorem proof_gap_exercise_4169_3
  (p : ℝ)
  (q : ℝ)
  (I : ℝ)
  (h1 : (p ∈ (Set.univ : Set ℝ)) ∧ (p ∈ ({x_1 : ℝ | 0 < x_1})))
  (h2 : (q ∈ (Set.univ : Set ℝ)) ∧ (q ∈ ({x_1 : ℝ | 0 < x_1})))
  (h3 : I ∈ (Set.univ : Set ℝ))
  (h4 : I = (∫ x in Set.Ioi (1 : ℝ), ((((1 : ℝ) /. (Real.rpow x p)) * (∫ y in Set.Ioi (1 /. x), (((1 : ℝ) /. (Real.rpow y q)) * (1 : ℝ)))) * (1 : ℝ))))
  (h5 : I = (∫ x in Set.Ioi (1 : ℝ), ((((1 : ℝ) /. (Real.rpow x p)) * (∫ y in Set.Ioi (1 /. x), (((1 : ℝ) /. (Real.rpow y q)) * (1 : ℝ)))) * (1 : ℝ))))
  (h6 : (q > 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 1)) → ((∫ y in Set.Ioi (1 /. x), (((1 : ℝ) /. (Real.rpow y q)) * (1 : ℝ))) = ((Real.rpow x (q - 1)) /. (q - 1))))))
  : (q > 1) → (I = ((1 /. (q - 1)) * (∫ x in Set.Ioi (1 : ℝ), ((Real.rpow x ((q - p) - 1)) * (1 : ℝ))))) := by
  sorry

theorem proof_gap_exercise_4169_4
  (p : ℝ)
  (q : ℝ)
  (I : ℝ)
  (h1 : (p ∈ (Set.univ : Set ℝ)) ∧ (p ∈ ({x_1 : ℝ | 0 < x_1})))
  (h2 : (q ∈ (Set.univ : Set ℝ)) ∧ (q ∈ ({x_1 : ℝ | 0 < x_1})))
  (h3 : I ∈ (Set.univ : Set ℝ))
  (h4 : I = (∫ x in Set.Ioi (1 : ℝ), ((((1 : ℝ) /. (Real.rpow x p)) * (∫ y in Set.Ioi (1 /. x), (((1 : ℝ) /. (Real.rpow y q)) * (1 : ℝ)))) * (1 : ℝ))))
  (h5 : I = (∫ x in Set.Ioi (1 : ℝ), ((((1 : ℝ) /. (Real.rpow x p)) * (∫ y in Set.Ioi (1 /. x), (((1 : ℝ) /. (Real.rpow y q)) * (1 : ℝ)))) * (1 : ℝ))))
  (h6 : (q > 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 1)) → ((∫ y in Set.Ioi (1 /. x), (((1 : ℝ) /. (Real.rpow y q)) * (1 : ℝ))) = ((Real.rpow x (q - 1)) /. (q - 1))))))
  (h7 : (q > 1) → (I = ((1 /. (q - 1)) * (∫ x in Set.Ioi (1 : ℝ), ((Real.rpow x ((q - p) - 1)) * (1 : ℝ))))))
  : ((p > q) ∧ (q > 1)) → (I = (1 /. ((p - q) * (q - 1)))) := by
  sorry

theorem proof_gap_exercise_4169_5
  (p : ℝ)
  (q : ℝ)
  (I : ℝ)
  (h1 : (p ∈ (Set.univ : Set ℝ)) ∧ (p ∈ ({x_1 : ℝ | 0 < x_1})))
  (h2 : (q ∈ (Set.univ : Set ℝ)) ∧ (q ∈ ({x_1 : ℝ | 0 < x_1})))
  (h3 : I ∈ (Set.univ : Set ℝ))
  (h4 : I = (∫ x in Set.Ioi (1 : ℝ), ((((1 : ℝ) /. (Real.rpow x p)) * (∫ y in Set.Ioi (1 /. x), (((1 : ℝ) /. (Real.rpow y q)) * (1 : ℝ)))) * (1 : ℝ))))
  (h5 : I = (∫ x in Set.Ioi (1 : ℝ), ((((1 : ℝ) /. (Real.rpow x p)) * (∫ y in Set.Ioi (1 /. x), (((1 : ℝ) /. (Real.rpow y q)) * (1 : ℝ)))) * (1 : ℝ))))
  (h6 : (q > 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 1)) → ((∫ y in Set.Ioi (1 /. x), (((1 : ℝ) /. (Real.rpow y q)) * (1 : ℝ))) = ((Real.rpow x (q - 1)) /. (q - 1))))))
  (h7 : (q > 1) → (I = ((1 /. (q - 1)) * (∫ x in Set.Ioi (1 : ℝ), ((Real.rpow x ((q - p) - 1)) * (1 : ℝ))))))
  (h8 : ((p > q) ∧ (q > 1)) → (I = (1 /. ((p - q) * (q - 1)))))
  : (q ≤ 1) → ((I : EReal) = ⊤) := by
  sorry

theorem proof_gap_exercise_4169_6
  (p : ℝ)
  (q : ℝ)
  (I : ℝ)
  (h1 : (p ∈ (Set.univ : Set ℝ)) ∧ (p ∈ ({x_1 : ℝ | 0 < x_1})))
  (h2 : (q ∈ (Set.univ : Set ℝ)) ∧ (q ∈ ({x_1 : ℝ | 0 < x_1})))
  (h3 : I ∈ (Set.univ : Set ℝ))
  (h4 : I = (∫ x in Set.Ioi (1 : ℝ), ((((1 : ℝ) /. (Real.rpow x p)) * (∫ y in Set.Ioi (1 /. x), (((1 : ℝ) /. (Real.rpow y q)) * (1 : ℝ)))) * (1 : ℝ))))
  (h5 : I = (∫ x in Set.Ioi (1 : ℝ), ((((1 : ℝ) /. (Real.rpow x p)) * (∫ y in Set.Ioi (1 /. x), (((1 : ℝ) /. (Real.rpow y q)) * (1 : ℝ)))) * (1 : ℝ))))
  (h6 : (q > 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 1)) → ((∫ y in Set.Ioi (1 /. x), (((1 : ℝ) /. (Real.rpow y q)) * (1 : ℝ))) = ((Real.rpow x (q - 1)) /. (q - 1))))))
  (h7 : (q > 1) → (I = ((1 /. (q - 1)) * (∫ x in Set.Ioi (1 : ℝ), ((Real.rpow x ((q - p) - 1)) * (1 : ℝ))))))
  (h8 : ((p > q) ∧ (q > 1)) → (I = (1 /. ((p - q) * (q - 1)))))
  (h9 : (q ≤ 1) → ((I : EReal) = ⊤))
  : (p ≤ q) → ((I : EReal) = ⊤) := by
  sorry

theorem proof_gap_exercise_4169_7
  (p : ℝ)
  (q : ℝ)
  (I : ℝ)
  (h1 : (p ∈ (Set.univ : Set ℝ)) ∧ (p ∈ ({x_1 : ℝ | 0 < x_1})))
  (h2 : (q ∈ (Set.univ : Set ℝ)) ∧ (q ∈ ({x_1 : ℝ | 0 < x_1})))
  (h3 : I ∈ (Set.univ : Set ℝ))
  (h4 : I = (∫ x in Set.Ioi (1 : ℝ), ((((1 : ℝ) /. (Real.rpow x p)) * (∫ y in Set.Ioi (1 /. x), (((1 : ℝ) /. (Real.rpow y q)) * (1 : ℝ)))) * (1 : ℝ))))
  (h5 : I = (∫ x in Set.Ioi (1 : ℝ), ((((1 : ℝ) /. (Real.rpow x p)) * (∫ y in Set.Ioi (1 /. x), (((1 : ℝ) /. (Real.rpow y q)) * (1 : ℝ)))) * (1 : ℝ))))
  (h6 : (q > 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 1)) → ((∫ y in Set.Ioi (1 /. x), (((1 : ℝ) /. (Real.rpow y q)) * (1 : ℝ))) = ((Real.rpow x (q - 1)) /. (q - 1))))))
  (h7 : (q > 1) → (I = ((1 /. (q - 1)) * (∫ x in Set.Ioi (1 : ℝ), ((Real.rpow x ((q - p) - 1)) * (1 : ℝ))))))
  (h8 : ((p > q) ∧ (q > 1)) → (I = (1 /. ((p - q) * (q - 1)))))
  (h9 : (q ≤ 1) → ((I : EReal) = ⊤))
  (h10 : (p ≤ q) → ((I : EReal) = ⊤))
  : ((p > q) ∧ (q > 1)) → (I = (1 /. ((p - q) * (q - 1)))) := by
  sorry

theorem proof_gap_exercise_4169_8
  (p : ℝ)
  (q : ℝ)
  (I : ℝ)
  (h1 : (p ∈ (Set.univ : Set ℝ)) ∧ (p ∈ ({x_1 : ℝ | 0 < x_1})))
  (h2 : (q ∈ (Set.univ : Set ℝ)) ∧ (q ∈ ({x_1 : ℝ | 0 < x_1})))
  (h3 : I ∈ (Set.univ : Set ℝ))
  (h4 : I = (∫ x in Set.Ioi (1 : ℝ), ((((1 : ℝ) /. (Real.rpow x p)) * (∫ y in Set.Ioi (1 /. x), (((1 : ℝ) /. (Real.rpow y q)) * (1 : ℝ)))) * (1 : ℝ))))
  (h5 : I = (∫ x in Set.Ioi (1 : ℝ), ((((1 : ℝ) /. (Real.rpow x p)) * (∫ y in Set.Ioi (1 /. x), (((1 : ℝ) /. (Real.rpow y q)) * (1 : ℝ)))) * (1 : ℝ))))
  (h6 : (q > 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 1)) → ((∫ y in Set.Ioi (1 /. x), (((1 : ℝ) /. (Real.rpow y q)) * (1 : ℝ))) = ((Real.rpow x (q - 1)) /. (q - 1))))))
  (h7 : (q > 1) → (I = ((1 /. (q - 1)) * (∫ x in Set.Ioi (1 : ℝ), ((Real.rpow x ((q - p) - 1)) * (1 : ℝ))))))
  (h8 : ((p > q) ∧ (q > 1)) → (I = (1 /. ((p - q) * (q - 1)))))
  (h9 : (q ≤ 1) → ((I : EReal) = ⊤))
  (h10 : (p ≤ q) → ((I : EReal) = ⊤))
  (h11 : ((p > q) ∧ (q > 1)) → (I = (1 /. ((p - q) * (q - 1)))))
  : ((q ≤ 1) ∨ (p ≤ q)) → ((I : EReal) = ⊤) := by
  sorry

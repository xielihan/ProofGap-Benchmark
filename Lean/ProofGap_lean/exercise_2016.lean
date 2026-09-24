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

-- exercise: exercise_2016

theorem proof_gap_exercise_2016_1
  (x : ℝ)
  (a : ℝ)
  (b : ℝ)
  (C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : b ∈ (Set.univ : Set ℝ))
  (h4 : C ∈ (Set.univ : Set ℝ))
  : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = ((((Real.sin x_1) * (Real.sin (x_1 + a))) * (Real.sin (x_1 + b))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_3 t) x_1) = (((Real.sin x_1) * ((Real.cos (a - b)) - (Real.cos (((2 * x_1) + a) + b)))) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((F_4 x_1) = ((1 /. 2) * (F_3 x_1)))))))}) := by
  sorry

theorem proof_gap_exercise_2016_2
  (x : ℝ)
  (a : ℝ)
  (b : ℝ)
  (C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : b ∈ (Set.univ : Set ℝ))
  (h4 : C ∈ (Set.univ : Set ℝ))
  (h5 : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = ((((Real.sin x_1) * (Real.sin (x_1 + a))) * (Real.sin (x_1 + b))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_3 t) x_1) = (((Real.sin x_1) * ((Real.cos (a - b)) - (Real.cos (((2 * x_1) + a) + b)))) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((F_4 x_1) = ((1 /. 2) * (F_3 x_1)))))))}))
  : ({F_6 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_5 t) x_1) = (((Real.sin x_1) * ((Real.cos (a - b)) - (Real.cos (((2 * x_1) + a) + b)))) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((F_6 x_1) = ((1 /. 2) * (F_5 x_1)))))))}) = ({F_10 : (ℝ -> ℝ) | (exists (F_7 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_7 t) x_1) = (((Real.sin (((3 * x_1) + a) + b)) - (Real.sin ((x_1 + a) + b))) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((F_10 x_1) = ((((-(1 /. 2)) * (Real.cos x_1)) * (Real.cos (a - b))) - ((1 /. 4) * (F_7 x_1))))))))}) := by
  sorry

theorem proof_gap_exercise_2016_3
  (x : ℝ)
  (a : ℝ)
  (b : ℝ)
  (C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : b ∈ (Set.univ : Set ℝ))
  (h4 : C ∈ (Set.univ : Set ℝ))
  (h5 : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = ((((Real.sin x_1) * (Real.sin (x_1 + a))) * (Real.sin (x_1 + b))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_3 t) x_1) = (((Real.sin x_1) * ((Real.cos (a - b)) - (Real.cos (((2 * x_1) + a) + b)))) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((F_4 x_1) = ((1 /. 2) * (F_3 x_1)))))))}))
  (h6 : ({F_6 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_5 t) x_1) = (((Real.sin x_1) * ((Real.cos (a - b)) - (Real.cos (((2 * x_1) + a) + b)))) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((F_6 x_1) = ((1 /. 2) * (F_5 x_1)))))))}) = ({F_10 : (ℝ -> ℝ) | (exists (F_7 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_7 t) x_1) = (((Real.sin (((3 * x_1) + a) + b)) - (Real.sin ((x_1 + a) + b))) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((F_10 x_1) = ((((-(1 /. 2)) * (Real.cos x_1)) * (Real.cos (a - b))) - ((1 /. 4) * (F_7 x_1))))))))}))
  : ({F_14 : (ℝ -> ℝ) | (exists (F_11 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_11 t) x_1) = (((Real.sin (((3 * x_1) + a) + b)) - (Real.sin ((x_1 + a) + b))) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((F_14 x_1) = ((((-(1 /. 2)) * (Real.cos x_1)) * (Real.cos (a - b))) - ((1 /. 4) * (F_11 x_1))))))))}) = ({F_15 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((F_15 x_1) = ((((((-(1 /. 2)) * (Real.cos x_1)) * (Real.cos (a - b))) + ((1 /. 12) * (Real.cos (((3 * x_1) + a) + b)))) - ((1 /. 4) * (Real.cos ((x_1 + a) + b)))) + C_1))))))}) := by
  sorry

theorem proof_gap_exercise_2016_4
  (x : ℝ)
  (a : ℝ)
  (b : ℝ)
  (C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : b ∈ (Set.univ : Set ℝ))
  (h4 : C ∈ (Set.univ : Set ℝ))
  (h5 : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = ((((Real.sin x_1) * (Real.sin (x_1 + a))) * (Real.sin (x_1 + b))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_3 t) x_1) = (((Real.sin x_1) * ((Real.cos (a - b)) - (Real.cos (((2 * x_1) + a) + b)))) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((F_4 x_1) = ((1 /. 2) * (F_3 x_1)))))))}))
  (h6 : ({F_6 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_5 t) x_1) = (((Real.sin x_1) * ((Real.cos (a - b)) - (Real.cos (((2 * x_1) + a) + b)))) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((F_6 x_1) = ((1 /. 2) * (F_5 x_1)))))))}) = ({F_10 : (ℝ -> ℝ) | (exists (F_7 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_7 t) x_1) = (((Real.sin (((3 * x_1) + a) + b)) - (Real.sin ((x_1 + a) + b))) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((F_10 x_1) = ((((-(1 /. 2)) * (Real.cos x_1)) * (Real.cos (a - b))) - ((1 /. 4) * (F_7 x_1))))))))}))
  (h7 : ({F_14 : (ℝ -> ℝ) | (exists (F_11 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_11 t) x_1) = (((Real.sin (((3 * x_1) + a) + b)) - (Real.sin ((x_1 + a) + b))) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((F_14 x_1) = ((((-(1 /. 2)) * (Real.cos x_1)) * (Real.cos (a - b))) - ((1 /. 4) * (F_11 x_1))))))))}) = ({F_15 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((F_15 x_1) = ((((((-(1 /. 2)) * (Real.cos x_1)) * (Real.cos (a - b))) + ((1 /. 12) * (Real.cos (((3 * x_1) + a) + b)))) - ((1 /. 4) * (Real.cos ((x_1 + a) + b)))) + C_1))))))}))
  : ({F_16 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_16 t) x_1) = ((((Real.sin x_1) * (Real.sin (x_1 + a))) * (Real.sin (x_1 + b))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_17 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((F_17 x_1) = ((((((-(1 /. 2)) * (Real.cos x_1)) * (Real.cos (a - b))) + ((1 /. 12) * (Real.cos (((3 * x_1) + a) + b)))) - ((1 /. 4) * (Real.cos ((x_1 + a) + b)))) + C_1))))))}) := by
  sorry

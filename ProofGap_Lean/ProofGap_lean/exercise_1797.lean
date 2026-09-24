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

-- exercise: exercise_1797

theorem proof_gap_exercise_1797_1
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((x ^ (3 : ℕ)) * (Real.exp (-(x ^ (2 : ℕ))))) • (fderiv ℝ (fun (x_1 : ℝ) => x_1))) = (((-(1 /. 2)) * (x ^ (2 : ℕ))) • (fderiv ℝ (fun (x_1 : ℝ) => (Real.exp (-(x_1 ^ (2 : ℕ)))))))))) := by
  sorry

theorem proof_gap_exercise_1797_2
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((x ^ (3 : ℕ)) * (Real.exp (-(x ^ (2 : ℕ))))) • (fderiv ℝ (fun (x_1 : ℝ) => x_1))) = (((-(1 /. 2)) * (x ^ (2 : ℕ))) • (fderiv ℝ (fun (x_1 : ℝ) => (Real.exp (-(x_1 ^ (2 : ℕ)))))))))))
  : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = (((x ^ (3 : ℕ)) * (Real.exp (-(x ^ (2 : ℕ))))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_3 t) x) = ((x ^ (2 : ℕ)) * (iteratedDeriv 1 (fun t => (Real.exp (-(t ^ (2 : ℕ))))) x))) ∧ ((F_4 x) = ((-(1 /. 2)) * (F_3 x)))))))}) := by
  sorry

theorem proof_gap_exercise_1797_3
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((x ^ (3 : ℕ)) * (Real.exp (-(x ^ (2 : ℕ))))) • (fderiv ℝ (fun (x_1 : ℝ) => x_1))) = (((-(1 /. 2)) * (x ^ (2 : ℕ))) • (fderiv ℝ (fun (x_1 : ℝ) => (Real.exp (-(x_1 ^ (2 : ℕ)))))))))))
  (h2 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = (((x ^ (3 : ℕ)) * (Real.exp (-(x ^ (2 : ℕ))))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_3 t) x) = ((x ^ (2 : ℕ)) * (iteratedDeriv 1 (fun t => (Real.exp (-(t ^ (2 : ℕ))))) x))) ∧ ((F_4 x) = ((-(1 /. 2)) * (F_3 x)))))))}))
  : ({F_6 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_5 t) x) = ((x ^ (2 : ℕ)) * (iteratedDeriv 1 (fun t => (Real.exp (-(t ^ (2 : ℕ))))) x))) ∧ ((F_6 x) = ((-(1 /. 2)) * (F_5 x)))))))}) = ({F_10 : (ℝ -> ℝ) | (exists (F_7 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_7 t) x) = ((Real.exp (-(x ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => (t ^ (2 : ℕ))) x))) ∧ ((F_10 x) = ((((-(1 /. 2)) * (x ^ (2 : ℕ))) * (Real.exp (-(x ^ (2 : ℕ))))) + ((1 /. 2) * (F_7 x))))))))}) := by
  sorry

theorem proof_gap_exercise_1797_4
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((x ^ (3 : ℕ)) * (Real.exp (-(x ^ (2 : ℕ))))) • (fderiv ℝ (fun (x_1 : ℝ) => x_1))) = (((-(1 /. 2)) * (x ^ (2 : ℕ))) • (fderiv ℝ (fun (x_1 : ℝ) => (Real.exp (-(x_1 ^ (2 : ℕ)))))))))))
  (h2 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = (((x ^ (3 : ℕ)) * (Real.exp (-(x ^ (2 : ℕ))))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_3 t) x) = ((x ^ (2 : ℕ)) * (iteratedDeriv 1 (fun t => (Real.exp (-(t ^ (2 : ℕ))))) x))) ∧ ((F_4 x) = ((-(1 /. 2)) * (F_3 x)))))))}))
  (h3 : ({F_6 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_5 t) x) = ((x ^ (2 : ℕ)) * (iteratedDeriv 1 (fun t => (Real.exp (-(t ^ (2 : ℕ))))) x))) ∧ ((F_6 x) = ((-(1 /. 2)) * (F_5 x)))))))}) = ({F_10 : (ℝ -> ℝ) | (exists (F_7 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_7 t) x) = ((Real.exp (-(x ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => (t ^ (2 : ℕ))) x))) ∧ ((F_10 x) = ((((-(1 /. 2)) * (x ^ (2 : ℕ))) * (Real.exp (-(x ^ (2 : ℕ))))) + ((1 /. 2) * (F_7 x))))))))}))
  : ({F_11 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_11 t) x) = (((x ^ (3 : ℕ)) * (Real.exp (-(x ^ (2 : ℕ))))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_12 : (ℝ -> ℝ) | (exists (C : ℝ), ((C ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_12 x) = (((-(((x ^ (2 : ℕ)) + 1) /. 2)) * (Real.exp (-(x ^ (2 : ℕ))))) + C))))))}) := by
  sorry

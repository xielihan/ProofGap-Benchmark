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

-- exercise: exercise_1184

theorem proof_gap_exercise_1184_1
  (y : (ℝ -> ℝ))
  (C_1 : ℝ)
  (C_2 : ℝ)
  (n : ℝ)
  (h1 : C_1 ∈ (Set.univ : Set ℝ))
  (h2 : C_2 ∈ (Set.univ : Set ℝ))
  (h3 : n ∈ (Set.univ : Set ℝ))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((y x) = ((Real.rpow x n) * ((C_1 * (Real.cos (Real.log x))) + (C_2 * (Real.sin (Real.log x)))))))))
  (h5 : A = (fun (x : ℝ) => ((C_1 * (Real.cos (Real.log x))) + (C_2 * (Real.sin (Real.log x))))))
  (h6 : B = (fun (x : ℝ) => ((C_2 * (Real.cos (Real.log x))) - (C_1 * (Real.sin (Real.log x))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((iteratedDeriv 1 (fun t => y t) x) = (((n * (Real.rpow x (n - 1))) * (A x)) + ((Real.rpow x (n - 1)) * (B x)))))) := by
  sorry

theorem proof_gap_exercise_1184_2
  (y : (ℝ -> ℝ))
  (C_1 : ℝ)
  (C_2 : ℝ)
  (n : ℝ)
  (h1 : C_1 ∈ (Set.univ : Set ℝ))
  (h2 : C_2 ∈ (Set.univ : Set ℝ))
  (h3 : n ∈ (Set.univ : Set ℝ))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((y x) = ((Real.rpow x n) * ((C_1 * (Real.cos (Real.log x))) + (C_2 * (Real.sin (Real.log x)))))))))
  (h5 : A = (fun (x : ℝ) => ((C_1 * (Real.cos (Real.log x))) + (C_2 * (Real.sin (Real.log x))))))
  (h6 : B = (fun (x : ℝ) => ((C_2 * (Real.cos (Real.log x))) - (C_1 * (Real.sin (Real.log x))))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((iteratedDeriv 1 (fun t => y t) x) = (((n * (Real.rpow x (n - 1))) * (A x)) + ((Real.rpow x (n - 1)) * (B x)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((iteratedDeriv 2 (fun t => y t) x) = ((Real.rpow x (n - 2)) * (((((n ^ (2 : ℕ)) - n) - 1) * (A x)) + (((2 * n) - 1) * (B x))))))) := by
  sorry

theorem proof_gap_exercise_1184_3
  (y : (ℝ -> ℝ))
  (C_1 : ℝ)
  (C_2 : ℝ)
  (n : ℝ)
  (h1 : C_1 ∈ (Set.univ : Set ℝ))
  (h2 : C_2 ∈ (Set.univ : Set ℝ))
  (h3 : n ∈ (Set.univ : Set ℝ))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((y x) = ((Real.rpow x n) * ((C_1 * (Real.cos (Real.log x))) + (C_2 * (Real.sin (Real.log x)))))))))
  (h5 : A = (fun (x : ℝ) => ((C_1 * (Real.cos (Real.log x))) + (C_2 * (Real.sin (Real.log x))))))
  (h6 : B = (fun (x : ℝ) => ((C_2 * (Real.cos (Real.log x))) - (C_1 * (Real.sin (Real.log x))))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((iteratedDeriv 1 (fun t => y t) x) = (((n * (Real.rpow x (n - 1))) * (A x)) + ((Real.rpow x (n - 1)) * (B x)))))))
  (h8 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((iteratedDeriv 2 (fun t => y t) x) = ((Real.rpow x (n - 2)) * (((((n ^ (2 : ℕ)) - n) - 1) * (A x)) + (((2 * n) - 1) * (B x))))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((((((x ^ (2 : ℕ)) * (iteratedDeriv 2 (fun t => y t) x)) + (((1 - (2 * n)) * x) * (iteratedDeriv 1 (fun t => y t) x))) + ((1 + (n ^ (2 : ℕ))) * (y x))) = ((((Real.rpow x n) * (((((n ^ (2 : ℕ)) - n) - 1) * (A x)) + (((2 * n) - 1) * (B x)))) + (((1 - (2 * n)) * (Real.rpow x n)) * ((n * (A x)) + (B x)))) + (((1 + (n ^ (2 : ℕ))) * (Real.rpow x n)) * (A x)))) ∧ (((((Real.rpow x n) * (((((n ^ (2 : ℕ)) - n) - 1) * (A x)) + (((2 * n) - 1) * (B x)))) + (((1 - (2 * n)) * (Real.rpow x n)) * ((n * (A x)) + (B x)))) + (((1 + (n ^ (2 : ℕ))) * (Real.rpow x n)) * (A x))) = 0)))) := by
  sorry

theorem proof_gap_exercise_1184_4
  (y : (ℝ -> ℝ))
  (C_1 : ℝ)
  (C_2 : ℝ)
  (n : ℝ)
  (h1 : C_1 ∈ (Set.univ : Set ℝ))
  (h2 : C_2 ∈ (Set.univ : Set ℝ))
  (h3 : n ∈ (Set.univ : Set ℝ))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((y x) = ((Real.rpow x n) * ((C_1 * (Real.cos (Real.log x))) + (C_2 * (Real.sin (Real.log x)))))))))
  (h5 : A = (fun (x : ℝ) => ((C_1 * (Real.cos (Real.log x))) + (C_2 * (Real.sin (Real.log x))))))
  (h6 : B = (fun (x : ℝ) => ((C_2 * (Real.cos (Real.log x))) - (C_1 * (Real.sin (Real.log x))))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((iteratedDeriv 1 (fun t => y t) x) = (((n * (Real.rpow x (n - 1))) * (A x)) + ((Real.rpow x (n - 1)) * (B x)))))))
  (h8 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((iteratedDeriv 2 (fun t => y t) x) = ((Real.rpow x (n - 2)) * (((((n ^ (2 : ℕ)) - n) - 1) * (A x)) + (((2 * n) - 1) * (B x))))))))
  (h9 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((((((x ^ (2 : ℕ)) * (iteratedDeriv 2 (fun t => y t) x)) + (((1 - (2 * n)) * x) * (iteratedDeriv 1 (fun t => y t) x))) + ((1 + (n ^ (2 : ℕ))) * (y x))) = ((((Real.rpow x n) * (((((n ^ (2 : ℕ)) - n) - 1) * (A x)) + (((2 * n) - 1) * (B x)))) + (((1 - (2 * n)) * (Real.rpow x n)) * ((n * (A x)) + (B x)))) + (((1 + (n ^ (2 : ℕ))) * (Real.rpow x n)) * (A x)))) ∧ (((((Real.rpow x n) * (((((n ^ (2 : ℕ)) - n) - 1) * (A x)) + (((2 * n) - 1) * (B x)))) + (((1 - (2 * n)) * (Real.rpow x n)) * ((n * (A x)) + (B x)))) + (((1 + (n ^ (2 : ℕ))) * (Real.rpow x n)) * (A x))) = 0)))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → (((((x ^ (2 : ℕ)) * (iteratedDeriv 2 (fun t => y t) x)) + (((1 - (2 * n)) * x) * (iteratedDeriv 1 (fun t => y t) x))) + ((1 + (n ^ (2 : ℕ))) * (y x))) = 0))) := by
  sorry

theorem proof_gap_exercise_1184_5
  (y : (ℝ -> ℝ))
  (C_1 : ℝ)
  (C_2 : ℝ)
  (n : ℝ)
  (h1 : C_1 ∈ (Set.univ : Set ℝ))
  (h2 : C_2 ∈ (Set.univ : Set ℝ))
  (h3 : n ∈ (Set.univ : Set ℝ))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((y x) = ((Real.rpow x n) * ((C_1 * (Real.cos (Real.log x))) + (C_2 * (Real.sin (Real.log x)))))))))
  (h5 : A = (fun (x : ℝ) => ((C_1 * (Real.cos (Real.log x))) + (C_2 * (Real.sin (Real.log x))))))
  (h6 : B = (fun (x : ℝ) => ((C_2 * (Real.cos (Real.log x))) - (C_1 * (Real.sin (Real.log x))))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((iteratedDeriv 1 (fun t => y t) x) = (((n * (Real.rpow x (n - 1))) * (A x)) + ((Real.rpow x (n - 1)) * (B x)))))))
  (h8 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((iteratedDeriv 2 (fun t => y t) x) = ((Real.rpow x (n - 2)) * (((((n ^ (2 : ℕ)) - n) - 1) * (A x)) + (((2 * n) - 1) * (B x))))))))
  (h9 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((((((x ^ (2 : ℕ)) * (iteratedDeriv 2 (fun t => y t) x)) + (((1 - (2 * n)) * x) * (iteratedDeriv 1 (fun t => y t) x))) + ((1 + (n ^ (2 : ℕ))) * (y x))) = ((((Real.rpow x n) * (((((n ^ (2 : ℕ)) - n) - 1) * (A x)) + (((2 * n) - 1) * (B x)))) + (((1 - (2 * n)) * (Real.rpow x n)) * ((n * (A x)) + (B x)))) + (((1 + (n ^ (2 : ℕ))) * (Real.rpow x n)) * (A x)))) ∧ (((((Real.rpow x n) * (((((n ^ (2 : ℕ)) - n) - 1) * (A x)) + (((2 * n) - 1) * (B x)))) + (((1 - (2 * n)) * (Real.rpow x n)) * ((n * (A x)) + (B x)))) + (((1 + (n ^ (2 : ℕ))) * (Real.rpow x n)) * (A x))) = 0)))))
  (h10 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → (((((x ^ (2 : ℕ)) * (iteratedDeriv 2 (fun t => y t) x)) + (((1 - (2 * n)) * x) * (iteratedDeriv 1 (fun t => y t) x))) + ((1 + (n ^ (2 : ℕ))) * (y x))) = 0))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → (((((x ^ (2 : ℕ)) * (iteratedDeriv 2 (fun t => y t) x)) + (((1 - (2 * n)) * x) * (iteratedDeriv 1 (fun t => y t) x))) + ((1 + (n ^ (2 : ℕ))) * (y x))) = 0))) := by
  sorry

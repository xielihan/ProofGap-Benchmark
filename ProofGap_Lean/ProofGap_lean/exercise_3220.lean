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

-- exercise: exercise_3220

theorem proof_gap_exercise_3220_1
  (u : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) ∧ (y ∈ (Set.univ : Set ℝ))) → ((u (x, y)) = (Real.rpow x y)))))
  : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (x > 0)) → (((u (x, y)) = (Real.rpow x y)) ∧ ((Real.rpow x y) = (Real.exp (y * (Real.log x))))))) := by
  sorry

theorem proof_gap_exercise_3220_2
  (u : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) ∧ (y ∈ (Set.univ : Set ℝ))) → ((u (x, y)) = (Real.rpow x y)))))
  (h2 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (x > 0)) → (((u (x, y)) = (Real.rpow x y)) ∧ ((Real.rpow x y) = (Real.exp (y * (Real.log x))))))))
  : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (x > 0)) → ((iteratedDeriv 1 (fun t => u (t, y)) x) = (y * (Real.rpow x (y - 1)))))) := by
  sorry

theorem proof_gap_exercise_3220_3
  (u : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) ∧ (y ∈ (Set.univ : Set ℝ))) → ((u (x, y)) = (Real.rpow x y)))))
  (h2 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (x > 0)) → (((u (x, y)) = (Real.rpow x y)) ∧ ((Real.rpow x y) = (Real.exp (y * (Real.log x))))))))
  (h3 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (x > 0)) → ((iteratedDeriv 1 (fun t => u (t, y)) x) = (y * (Real.rpow x (y - 1)))))))
  : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (x > 0)) → (((iteratedDeriv 1 (fun t => u (x, t)) y) = ((Real.exp (y * (Real.log x))) * (Real.log x))) ∧ (((Real.exp (y * (Real.log x))) * (Real.log x)) = ((Real.rpow x y) * (Real.log x)))))) := by
  sorry

theorem proof_gap_exercise_3220_4
  (u : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) ∧ (y ∈ (Set.univ : Set ℝ))) → ((u (x, y)) = (Real.rpow x y)))))
  (h2 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (x > 0)) → (((u (x, y)) = (Real.rpow x y)) ∧ ((Real.rpow x y) = (Real.exp (y * (Real.log x))))))))
  (h3 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (x > 0)) → ((iteratedDeriv 1 (fun t => u (t, y)) x) = (y * (Real.rpow x (y - 1)))))))
  (h4 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (x > 0)) → (((iteratedDeriv 1 (fun t => u (x, t)) y) = ((Real.exp (y * (Real.log x))) * (Real.log x))) ∧ (((Real.exp (y * (Real.log x))) * (Real.log x)) = ((Real.rpow x y) * (Real.log x)))))))
  : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => u (t, y)) x) = ((y * (y - 1)) * (Real.rpow x (y - 2)))))) := by
  sorry

theorem proof_gap_exercise_3220_5
  (u : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) ∧ (y ∈ (Set.univ : Set ℝ))) → ((u (x, y)) = (Real.rpow x y)))))
  (h2 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (x > 0)) → (((u (x, y)) = (Real.rpow x y)) ∧ ((Real.rpow x y) = (Real.exp (y * (Real.log x))))))))
  (h3 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (x > 0)) → ((iteratedDeriv 1 (fun t => u (t, y)) x) = (y * (Real.rpow x (y - 1)))))))
  (h4 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (x > 0)) → (((iteratedDeriv 1 (fun t => u (x, t)) y) = ((Real.exp (y * (Real.log x))) * (Real.log x))) ∧ (((Real.exp (y * (Real.log x))) * (Real.log x)) = ((Real.rpow x y) * (Real.log x)))))))
  (h5 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => u (t, y)) x) = ((y * (y - 1)) * (Real.rpow x (y - 2)))))))
  : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => u (x, t)) y) = ((Real.rpow x y) * ((Real.log x) ^ (2 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_3220_6
  (u : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) ∧ (y ∈ (Set.univ : Set ℝ))) → ((u (x, y)) = (Real.rpow x y)))))
  (h2 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (x > 0)) → (((u (x, y)) = (Real.rpow x y)) ∧ ((Real.rpow x y) = (Real.exp (y * (Real.log x))))))))
  (h3 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (x > 0)) → ((iteratedDeriv 1 (fun t => u (t, y)) x) = (y * (Real.rpow x (y - 1)))))))
  (h4 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (x > 0)) → (((iteratedDeriv 1 (fun t => u (x, t)) y) = ((Real.exp (y * (Real.log x))) * (Real.log x))) ∧ (((Real.exp (y * (Real.log x))) * (Real.log x)) = ((Real.rpow x y) * (Real.log x)))))))
  (h5 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => u (t, y)) x) = ((y * (y - 1)) * (Real.rpow x (y - 2)))))))
  (h6 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => u (x, t)) y) = ((Real.rpow x y) * ((Real.log x) ^ (2 : ℕ)))))))
  : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (x > 0)) → (((iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => u (t, p.2)) p.1)) (x, t)) y) = ((Real.rpow x (y - 1)) + ((y * (Real.rpow x (y - 1))) * (Real.log x)))) ∧ (((Real.rpow x (y - 1)) + ((y * (Real.rpow x (y - 1))) * (Real.log x))) = ((Real.rpow x (y - 1)) * (1 + (y * (Real.log x)))))))) := by
  sorry

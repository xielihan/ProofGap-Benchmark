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

-- exercise: exercise_3307

theorem proof_gap_exercise_3307_1
  (u : (ℝ × ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (a, b))) → ((u (x, y)) = (Real.log (Real.rpow (((x - a) ^ (2 : ℕ)) + ((y - b) ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (a, b))) → ((iteratedDeriv 1 (fun t => u (t, y)) x) = ((x - a) /. (((x - a) ^ (2 : ℕ)) + ((y - b) ^ (2 : ℕ))))))))) := by
  sorry

theorem proof_gap_exercise_3307_2
  (u : (ℝ × ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (a, b))) → ((u (x, y)) = (Real.log (Real.rpow (((x - a) ^ (2 : ℕ)) + ((y - b) ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (a, b))) → ((iteratedDeriv 1 (fun t => u (t, y)) x) = ((x - a) /. (((x - a) ^ (2 : ℕ)) + ((y - b) ^ (2 : ℕ))))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (a, b))) → ((iteratedDeriv 2 (fun t => u (t, y)) x) = ((((y - b) ^ (2 : ℕ)) - ((x - a) ^ (2 : ℕ))) /. ((((x - a) ^ (2 : ℕ)) + ((y - b) ^ (2 : ℕ))) ^ (2 : ℕ)))))))) := by
  sorry

theorem proof_gap_exercise_3307_3
  (u : (ℝ × ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (a, b))) → ((u (x, y)) = (Real.log (Real.rpow (((x - a) ^ (2 : ℕ)) + ((y - b) ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (a, b))) → ((iteratedDeriv 1 (fun t => u (t, y)) x) = ((x - a) /. (((x - a) ^ (2 : ℕ)) + ((y - b) ^ (2 : ℕ))))))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (a, b))) → ((iteratedDeriv 2 (fun t => u (t, y)) x) = ((((y - b) ^ (2 : ℕ)) - ((x - a) ^ (2 : ℕ))) /. ((((x - a) ^ (2 : ℕ)) + ((y - b) ^ (2 : ℕ))) ^ (2 : ℕ)))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (a, b))) → ((iteratedDeriv 2 (fun t => u (x, t)) y) = ((((x - a) ^ (2 : ℕ)) - ((y - b) ^ (2 : ℕ))) /. ((((x - a) ^ (2 : ℕ)) + ((y - b) ^ (2 : ℕ))) ^ (2 : ℕ)))))))) := by
  sorry

theorem proof_gap_exercise_3307_4
  (u : (ℝ × ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (a, b))) → ((u (x, y)) = (Real.log (Real.rpow (((x - a) ^ (2 : ℕ)) + ((y - b) ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (a, b))) → ((iteratedDeriv 1 (fun t => u (t, y)) x) = ((x - a) /. (((x - a) ^ (2 : ℕ)) + ((y - b) ^ (2 : ℕ))))))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (a, b))) → ((iteratedDeriv 2 (fun t => u (t, y)) x) = ((((y - b) ^ (2 : ℕ)) - ((x - a) ^ (2 : ℕ))) /. ((((x - a) ^ (2 : ℕ)) + ((y - b) ^ (2 : ℕ))) ^ (2 : ℕ)))))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (a, b))) → ((iteratedDeriv 2 (fun t => u (x, t)) y) = ((((x - a) ^ (2 : ℕ)) - ((y - b) ^ (2 : ℕ))) /. ((((x - a) ^ (2 : ℕ)) + ((y - b) ^ (2 : ℕ))) ^ (2 : ℕ)))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (a, b))) → (((iteratedDeriv 2 (fun t => u (t, y)) x) + (iteratedDeriv 2 (fun t => u (x, t)) y)) = 0))))) := by
  sorry

theorem proof_gap_exercise_3307_5
  (u : (ℝ × ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (a, b))) → ((u (x, y)) = (Real.log (Real.rpow (((x - a) ^ (2 : ℕ)) + ((y - b) ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (a, b))) → ((iteratedDeriv 1 (fun t => u (t, y)) x) = ((x - a) /. (((x - a) ^ (2 : ℕ)) + ((y - b) ^ (2 : ℕ))))))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (a, b))) → ((iteratedDeriv 2 (fun t => u (t, y)) x) = ((((y - b) ^ (2 : ℕ)) - ((x - a) ^ (2 : ℕ))) /. ((((x - a) ^ (2 : ℕ)) + ((y - b) ^ (2 : ℕ))) ^ (2 : ℕ)))))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (a, b))) → ((iteratedDeriv 2 (fun t => u (x, t)) y) = ((((x - a) ^ (2 : ℕ)) - ((y - b) ^ (2 : ℕ))) /. ((((x - a) ^ (2 : ℕ)) + ((y - b) ^ (2 : ℕ))) ^ (2 : ℕ)))))))))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (a, b))) → (((iteratedDeriv 2 (fun t => u (t, y)) x) + (iteratedDeriv 2 (fun t => u (x, t)) y)) = 0))))))
  : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (a, b))) → (((iteratedDeriv 2 (fun t => u (t, y)) x) + (iteratedDeriv 2 (fun t => u (x, t)) y)) = 0))) := by
  sorry

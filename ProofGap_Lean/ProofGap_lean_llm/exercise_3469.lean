import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat

open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

open scoped RealInnerProductSpace

noncomputable def lpFunDeri {E : Type*} (f g : E -> ℝ) : E -> ℝ :=
  fun _ => 0

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

-- exercise: exercise_3469

theorem proof_gap_exercise_3469_1
  (u : (ℝ × (ℝ × ℝ) -> ℝ))
  (v_uCE_uBE : (ℝ × (ℝ × ℝ) -> ℝ))
  (v_uCE_uB7 : (ℝ × (ℝ × ℝ) -> ℝ))
  (v_uCE_uB6 : (ℝ × (ℝ × ℝ) -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((((v_uCE_uBE (x, (y, z))) = x) ∧ ((v_uCE_uB7 (x, (y, z))) = (y - x))) ∧ ((v_uCE_uB6 (x, (y, z))) = (z - x))))))
  (h2 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((((iteratedDeriv 1 (fun t => u (t, (y, z))) x) + (iteratedDeriv 1 (fun t => u (x, (t, z))) y)) + (iteratedDeriv 1 (fun t => u (x, (y, t))) z)) = 0))))
  : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => u (t, (y, z))) x) = (((((lpFunDeri u v_uCE_uBE) (x, (y, z))) * (iteratedDeriv 1 (fun t => v_uCE_uBE (t, (y, z))) x)) + (((lpFunDeri u v_uCE_uB7) (x, (y, z))) * (iteratedDeriv 1 (fun t => v_uCE_uB7 (t, (y, z))) x))) + (((lpFunDeri u v_uCE_uB6) (x, (y, z))) * (iteratedDeriv 1 (fun t => v_uCE_uB6 (t, (y, z))) x)))))) := by
  sorry

theorem proof_gap_exercise_3469_2
  (u : (ℝ × (ℝ × ℝ) -> ℝ))
  (v_uCE_uBE : (ℝ × (ℝ × ℝ) -> ℝ))
  (v_uCE_uB7 : (ℝ × (ℝ × ℝ) -> ℝ))
  (v_uCE_uB6 : (ℝ × (ℝ × ℝ) -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((((v_uCE_uBE (x, (y, z))) = x) ∧ ((v_uCE_uB7 (x, (y, z))) = (y - x))) ∧ ((v_uCE_uB6 (x, (y, z))) = (z - x))))))
  (h2 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((((iteratedDeriv 1 (fun t => u (t, (y, z))) x) + (iteratedDeriv 1 (fun t => u (x, (t, z))) y)) + (iteratedDeriv 1 (fun t => u (x, (y, t))) z)) = 0))))
  (h3 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => u (t, (y, z))) x) = (((((lpFunDeri u v_uCE_uBE) (x, (y, z))) * (iteratedDeriv 1 (fun t => v_uCE_uBE (t, (y, z))) x)) + (((lpFunDeri u v_uCE_uB7) (x, (y, z))) * (iteratedDeriv 1 (fun t => v_uCE_uB7 (t, (y, z))) x))) + (((lpFunDeri u v_uCE_uB6) (x, (y, z))) * (iteratedDeriv 1 (fun t => v_uCE_uB6 (t, (y, z))) x)))))))
  : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => u (t, (y, z))) x) = ((((lpFunDeri u v_uCE_uBE) (x, (y, z))) - ((lpFunDeri u v_uCE_uB7) (x, (y, z)))) - ((lpFunDeri u v_uCE_uB6) (x, (y, z))))))) := by
  sorry

theorem proof_gap_exercise_3469_3
  (u : (ℝ × (ℝ × ℝ) -> ℝ))
  (v_uCE_uBE : (ℝ × (ℝ × ℝ) -> ℝ))
  (v_uCE_uB7 : (ℝ × (ℝ × ℝ) -> ℝ))
  (v_uCE_uB6 : (ℝ × (ℝ × ℝ) -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((((v_uCE_uBE (x, (y, z))) = x) ∧ ((v_uCE_uB7 (x, (y, z))) = (y - x))) ∧ ((v_uCE_uB6 (x, (y, z))) = (z - x))))))
  (h2 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((((iteratedDeriv 1 (fun t => u (t, (y, z))) x) + (iteratedDeriv 1 (fun t => u (x, (t, z))) y)) + (iteratedDeriv 1 (fun t => u (x, (y, t))) z)) = 0))))
  (h3 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => u (t, (y, z))) x) = (((((lpFunDeri u v_uCE_uBE) (x, (y, z))) * (iteratedDeriv 1 (fun t => v_uCE_uBE (t, (y, z))) x)) + (((lpFunDeri u v_uCE_uB7) (x, (y, z))) * (iteratedDeriv 1 (fun t => v_uCE_uB7 (t, (y, z))) x))) + (((lpFunDeri u v_uCE_uB6) (x, (y, z))) * (iteratedDeriv 1 (fun t => v_uCE_uB6 (t, (y, z))) x)))))))
  (h4 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => u (t, (y, z))) x) = ((((lpFunDeri u v_uCE_uBE) (x, (y, z))) - ((lpFunDeri u v_uCE_uB7) (x, (y, z)))) - ((lpFunDeri u v_uCE_uB6) (x, (y, z))))))))
  : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => u (x, (t, z))) y) = ((lpFunDeri u v_uCE_uB7) (x, (y, z)))))) := by
  sorry

theorem proof_gap_exercise_3469_4
  (u : (ℝ × (ℝ × ℝ) -> ℝ))
  (v_uCE_uBE : (ℝ × (ℝ × ℝ) -> ℝ))
  (v_uCE_uB7 : (ℝ × (ℝ × ℝ) -> ℝ))
  (v_uCE_uB6 : (ℝ × (ℝ × ℝ) -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((((v_uCE_uBE (x, (y, z))) = x) ∧ ((v_uCE_uB7 (x, (y, z))) = (y - x))) ∧ ((v_uCE_uB6 (x, (y, z))) = (z - x))))))
  (h2 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((((iteratedDeriv 1 (fun t => u (t, (y, z))) x) + (iteratedDeriv 1 (fun t => u (x, (t, z))) y)) + (iteratedDeriv 1 (fun t => u (x, (y, t))) z)) = 0))))
  (h3 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => u (t, (y, z))) x) = (((((lpFunDeri u v_uCE_uBE) (x, (y, z))) * (iteratedDeriv 1 (fun t => v_uCE_uBE (t, (y, z))) x)) + (((lpFunDeri u v_uCE_uB7) (x, (y, z))) * (iteratedDeriv 1 (fun t => v_uCE_uB7 (t, (y, z))) x))) + (((lpFunDeri u v_uCE_uB6) (x, (y, z))) * (iteratedDeriv 1 (fun t => v_uCE_uB6 (t, (y, z))) x)))))))
  (h4 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => u (t, (y, z))) x) = ((((lpFunDeri u v_uCE_uBE) (x, (y, z))) - ((lpFunDeri u v_uCE_uB7) (x, (y, z)))) - ((lpFunDeri u v_uCE_uB6) (x, (y, z))))))))
  (h5 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => u (x, (t, z))) y) = ((lpFunDeri u v_uCE_uB7) (x, (y, z)))))))
  : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => u (x, (y, t))) z) = ((lpFunDeri u v_uCE_uB6) (x, (y, z)))))) := by
  sorry

theorem proof_gap_exercise_3469_5
  (u : (ℝ × (ℝ × ℝ) -> ℝ))
  (v_uCE_uBE : (ℝ × (ℝ × ℝ) -> ℝ))
  (v_uCE_uB7 : (ℝ × (ℝ × ℝ) -> ℝ))
  (v_uCE_uB6 : (ℝ × (ℝ × ℝ) -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((((v_uCE_uBE (x, (y, z))) = x) ∧ ((v_uCE_uB7 (x, (y, z))) = (y - x))) ∧ ((v_uCE_uB6 (x, (y, z))) = (z - x))))))
  (h2 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((((iteratedDeriv 1 (fun t => u (t, (y, z))) x) + (iteratedDeriv 1 (fun t => u (x, (t, z))) y)) + (iteratedDeriv 1 (fun t => u (x, (y, t))) z)) = 0))))
  (h3 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => u (t, (y, z))) x) = (((((lpFunDeri u v_uCE_uBE) (x, (y, z))) * (iteratedDeriv 1 (fun t => v_uCE_uBE (t, (y, z))) x)) + (((lpFunDeri u v_uCE_uB7) (x, (y, z))) * (iteratedDeriv 1 (fun t => v_uCE_uB7 (t, (y, z))) x))) + (((lpFunDeri u v_uCE_uB6) (x, (y, z))) * (iteratedDeriv 1 (fun t => v_uCE_uB6 (t, (y, z))) x)))))))
  (h4 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => u (t, (y, z))) x) = ((((lpFunDeri u v_uCE_uBE) (x, (y, z))) - ((lpFunDeri u v_uCE_uB7) (x, (y, z)))) - ((lpFunDeri u v_uCE_uB6) (x, (y, z))))))))
  (h5 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => u (x, (t, z))) y) = ((lpFunDeri u v_uCE_uB7) (x, (y, z)))))))
  (h6 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => u (x, (y, t))) z) = ((lpFunDeri u v_uCE_uB6) (x, (y, z)))))))
  : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → (((lpFunDeri u v_uCE_uBE) (x, (y, z))) = 0))) := by
  sorry

theorem proof_gap_exercise_3469_6
  (u : (ℝ × (ℝ × ℝ) -> ℝ))
  (v_uCE_uBE : (ℝ × (ℝ × ℝ) -> ℝ))
  (v_uCE_uB7 : (ℝ × (ℝ × ℝ) -> ℝ))
  (v_uCE_uB6 : (ℝ × (ℝ × ℝ) -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((((v_uCE_uBE (x, (y, z))) = x) ∧ ((v_uCE_uB7 (x, (y, z))) = (y - x))) ∧ ((v_uCE_uB6 (x, (y, z))) = (z - x))))))
  (h2 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((((iteratedDeriv 1 (fun t => u (t, (y, z))) x) + (iteratedDeriv 1 (fun t => u (x, (t, z))) y)) + (iteratedDeriv 1 (fun t => u (x, (y, t))) z)) = 0))))
  (h3 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => u (t, (y, z))) x) = (((((lpFunDeri u v_uCE_uBE) (x, (y, z))) * (iteratedDeriv 1 (fun t => v_uCE_uBE (t, (y, z))) x)) + (((lpFunDeri u v_uCE_uB7) (x, (y, z))) * (iteratedDeriv 1 (fun t => v_uCE_uB7 (t, (y, z))) x))) + (((lpFunDeri u v_uCE_uB6) (x, (y, z))) * (iteratedDeriv 1 (fun t => v_uCE_uB6 (t, (y, z))) x)))))))
  (h4 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => u (t, (y, z))) x) = ((((lpFunDeri u v_uCE_uBE) (x, (y, z))) - ((lpFunDeri u v_uCE_uB7) (x, (y, z)))) - ((lpFunDeri u v_uCE_uB6) (x, (y, z))))))))
  (h5 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => u (x, (t, z))) y) = ((lpFunDeri u v_uCE_uB7) (x, (y, z)))))))
  (h6 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => u (x, (y, t))) z) = ((lpFunDeri u v_uCE_uB6) (x, (y, z)))))))
  (h7 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → (((lpFunDeri u v_uCE_uBE) (x, (y, z))) = 0))))
  : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → (((lpFunDeri u v_uCE_uBE) (x, (y, z))) = 0))) := by
  sorry

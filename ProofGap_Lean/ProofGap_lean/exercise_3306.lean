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

-- exercise: exercise_3306

theorem proof_gap_exercise_3306_1
  (u : (ℝ × (ℝ × ℝ) -> ℝ))
  (v : (ℝ × (ℝ × ℝ) -> ℝ))
  (h1 : D ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h2 : ContDiffOn ℝ (2 : ℕ∞) u D)
  (h3 : ContDiffOn ℝ (2 : ℕ∞) v D)
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → (forall (z : ℝ), (((z ∈ (Set.univ : Set ℝ)) ∧ ((x, y, z) ∈ D)) → ((iteratedDeriv 2 (fun t => ((u (t, (y, z))) * (v (t, (y, z))))) x) = ((((u (x, (y, z))) * (iteratedDeriv 2 (fun t => v (t, (y, z))) x)) + ((v (x, (y, z))) * (iteratedDeriv 2 (fun t => u (t, (y, z))) x))) + ((2 * (iteratedDeriv 1 (fun t => u (t, (y, z))) x)) * (iteratedDeriv 1 (fun t => v (t, (y, z))) x)))))))))) := by
  sorry

theorem proof_gap_exercise_3306_2
  (u : (ℝ × (ℝ × ℝ) -> ℝ))
  (v : (ℝ × (ℝ × ℝ) -> ℝ))
  (h1 : D ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h2 : ContDiffOn ℝ (2 : ℕ∞) u D)
  (h3 : ContDiffOn ℝ (2 : ℕ∞) v D)
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → (forall (z : ℝ), (((z ∈ (Set.univ : Set ℝ)) ∧ ((x, y, z) ∈ D)) → ((iteratedDeriv 2 (fun t => ((u (t, (y, z))) * (v (t, (y, z))))) x) = ((((u (x, (y, z))) * (iteratedDeriv 2 (fun t => v (t, (y, z))) x)) + ((v (x, (y, z))) * (iteratedDeriv 2 (fun t => u (t, (y, z))) x))) + ((2 * (iteratedDeriv 1 (fun t => u (t, (y, z))) x)) * (iteratedDeriv 1 (fun t => v (t, (y, z))) x)))))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → (forall (z : ℝ), (((z ∈ (Set.univ : Set ℝ)) ∧ ((x, y, z) ∈ D)) → ((iteratedDeriv 2 (fun t => ((u (x, (t, z))) * (v (x, (t, z))))) y) = ((((u (x, (y, z))) * (iteratedDeriv 2 (fun t => v (x, (t, z))) y)) + ((v (x, (y, z))) * (iteratedDeriv 2 (fun t => u (x, (t, z))) y))) + ((2 * (iteratedDeriv 1 (fun t => u (x, (t, z))) y)) * (iteratedDeriv 1 (fun t => v (x, (t, z))) y)))))))))) := by
  sorry

theorem proof_gap_exercise_3306_3
  (u : (ℝ × (ℝ × ℝ) -> ℝ))
  (v : (ℝ × (ℝ × ℝ) -> ℝ))
  (h1 : D ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h2 : ContDiffOn ℝ (2 : ℕ∞) u D)
  (h3 : ContDiffOn ℝ (2 : ℕ∞) v D)
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → (forall (z : ℝ), (((z ∈ (Set.univ : Set ℝ)) ∧ ((x, y, z) ∈ D)) → ((iteratedDeriv 2 (fun t => ((u (t, (y, z))) * (v (t, (y, z))))) x) = ((((u (x, (y, z))) * (iteratedDeriv 2 (fun t => v (t, (y, z))) x)) + ((v (x, (y, z))) * (iteratedDeriv 2 (fun t => u (t, (y, z))) x))) + ((2 * (iteratedDeriv 1 (fun t => u (t, (y, z))) x)) * (iteratedDeriv 1 (fun t => v (t, (y, z))) x)))))))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → (forall (z : ℝ), (((z ∈ (Set.univ : Set ℝ)) ∧ ((x, y, z) ∈ D)) → ((iteratedDeriv 2 (fun t => ((u (x, (t, z))) * (v (x, (t, z))))) y) = ((((u (x, (y, z))) * (iteratedDeriv 2 (fun t => v (x, (t, z))) y)) + ((v (x, (y, z))) * (iteratedDeriv 2 (fun t => u (x, (t, z))) y))) + ((2 * (iteratedDeriv 1 (fun t => u (x, (t, z))) y)) * (iteratedDeriv 1 (fun t => v (x, (t, z))) y)))))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → (forall (z : ℝ), (((z ∈ (Set.univ : Set ℝ)) ∧ ((x, y, z) ∈ D)) → ((iteratedDeriv 2 (fun t => ((u (x, (y, t))) * (v (x, (y, t))))) z) = ((((u (x, (y, z))) * (iteratedDeriv 2 (fun t => v (x, (y, t))) z)) + ((v (x, (y, z))) * (iteratedDeriv 2 (fun t => u (x, (y, t))) z))) + ((2 * (iteratedDeriv 1 (fun t => u (x, (y, t))) z)) * (iteratedDeriv 1 (fun t => v (x, (y, t))) z)))))))))) := by
  sorry

theorem proof_gap_exercise_3306_4
  (u : (ℝ × (ℝ × ℝ) -> ℝ))
  (v : (ℝ × (ℝ × ℝ) -> ℝ))
  (h1 : D ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h2 : ContDiffOn ℝ (2 : ℕ∞) u D)
  (h3 : ContDiffOn ℝ (2 : ℕ∞) v D)
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → (forall (z : ℝ), (((z ∈ (Set.univ : Set ℝ)) ∧ ((x, y, z) ∈ D)) → ((iteratedDeriv 2 (fun t => ((u (t, (y, z))) * (v (t, (y, z))))) x) = ((((u (x, (y, z))) * (iteratedDeriv 2 (fun t => v (t, (y, z))) x)) + ((v (x, (y, z))) * (iteratedDeriv 2 (fun t => u (t, (y, z))) x))) + ((2 * (iteratedDeriv 1 (fun t => u (t, (y, z))) x)) * (iteratedDeriv 1 (fun t => v (t, (y, z))) x)))))))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → (forall (z : ℝ), (((z ∈ (Set.univ : Set ℝ)) ∧ ((x, y, z) ∈ D)) → ((iteratedDeriv 2 (fun t => ((u (x, (t, z))) * (v (x, (t, z))))) y) = ((((u (x, (y, z))) * (iteratedDeriv 2 (fun t => v (x, (t, z))) y)) + ((v (x, (y, z))) * (iteratedDeriv 2 (fun t => u (x, (t, z))) y))) + ((2 * (iteratedDeriv 1 (fun t => u (x, (t, z))) y)) * (iteratedDeriv 1 (fun t => v (x, (t, z))) y)))))))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → (forall (z : ℝ), (((z ∈ (Set.univ : Set ℝ)) ∧ ((x, y, z) ∈ D)) → ((iteratedDeriv 2 (fun t => ((u (x, (y, t))) * (v (x, (y, t))))) z) = ((((u (x, (y, z))) * (iteratedDeriv 2 (fun t => v (x, (y, t))) z)) + ((v (x, (y, z))) * (iteratedDeriv 2 (fun t => u (x, (y, t))) z))) + ((2 * (iteratedDeriv 1 (fun t => u (x, (y, t))) z)) * (iteratedDeriv 1 (fun t => v (x, (y, t))) z)))))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → (forall (z : ℝ), (((z ∈ (Set.univ : Set ℝ)) ∧ ((x, y, z) ∈ D)) → ((((iteratedDeriv 2 (fun t => ((u (t, (y, z))) * (v (t, (y, z))))) x) + (iteratedDeriv 2 (fun t => ((u (x, (t, z))) * (v (x, (t, z))))) y)) + (iteratedDeriv 2 (fun t => ((u (x, (y, t))) * (v (x, (y, t))))) z)) = ((((u (x, (y, z))) * (((iteratedDeriv 2 (fun t => v (t, (y, z))) x) + (iteratedDeriv 2 (fun t => v (x, (t, z))) y)) + (iteratedDeriv 2 (fun t => v (x, (y, t))) z))) + ((v (x, (y, z))) * (((iteratedDeriv 2 (fun t => u (t, (y, z))) x) + (iteratedDeriv 2 (fun t => u (x, (t, z))) y)) + (iteratedDeriv 2 (fun t => u (x, (y, t))) z)))) + (2 * ((((iteratedDeriv 1 (fun t => u (t, (y, z))) x) * (iteratedDeriv 1 (fun t => v (t, (y, z))) x)) + ((iteratedDeriv 1 (fun t => u (x, (t, z))) y) * (iteratedDeriv 1 (fun t => v (x, (t, z))) y))) + ((iteratedDeriv 1 (fun t => u (x, (y, t))) z) * (iteratedDeriv 1 (fun t => v (x, (y, t))) z)))))))))))) := by
  sorry

theorem proof_gap_exercise_3306_5
  (u : (ℝ × (ℝ × ℝ) -> ℝ))
  (v : (ℝ × (ℝ × ℝ) -> ℝ))
  (h1 : D ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h2 : ContDiffOn ℝ (2 : ℕ∞) u D)
  (h3 : ContDiffOn ℝ (2 : ℕ∞) v D)
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → (forall (z : ℝ), (((z ∈ (Set.univ : Set ℝ)) ∧ ((x, y, z) ∈ D)) → ((iteratedDeriv 2 (fun t => ((u (t, (y, z))) * (v (t, (y, z))))) x) = ((((u (x, (y, z))) * (iteratedDeriv 2 (fun t => v (t, (y, z))) x)) + ((v (x, (y, z))) * (iteratedDeriv 2 (fun t => u (t, (y, z))) x))) + ((2 * (iteratedDeriv 1 (fun t => u (t, (y, z))) x)) * (iteratedDeriv 1 (fun t => v (t, (y, z))) x)))))))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → (forall (z : ℝ), (((z ∈ (Set.univ : Set ℝ)) ∧ ((x, y, z) ∈ D)) → ((iteratedDeriv 2 (fun t => ((u (x, (t, z))) * (v (x, (t, z))))) y) = ((((u (x, (y, z))) * (iteratedDeriv 2 (fun t => v (x, (t, z))) y)) + ((v (x, (y, z))) * (iteratedDeriv 2 (fun t => u (x, (t, z))) y))) + ((2 * (iteratedDeriv 1 (fun t => u (x, (t, z))) y)) * (iteratedDeriv 1 (fun t => v (x, (t, z))) y)))))))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → (forall (z : ℝ), (((z ∈ (Set.univ : Set ℝ)) ∧ ((x, y, z) ∈ D)) → ((iteratedDeriv 2 (fun t => ((u (x, (y, t))) * (v (x, (y, t))))) z) = ((((u (x, (y, z))) * (iteratedDeriv 2 (fun t => v (x, (y, t))) z)) + ((v (x, (y, z))) * (iteratedDeriv 2 (fun t => u (x, (y, t))) z))) + ((2 * (iteratedDeriv 1 (fun t => u (x, (y, t))) z)) * (iteratedDeriv 1 (fun t => v (x, (y, t))) z)))))))))))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → (forall (z : ℝ), (((z ∈ (Set.univ : Set ℝ)) ∧ ((x, y, z) ∈ D)) → ((((iteratedDeriv 2 (fun t => ((u (t, (y, z))) * (v (t, (y, z))))) x) + (iteratedDeriv 2 (fun t => ((u (x, (t, z))) * (v (x, (t, z))))) y)) + (iteratedDeriv 2 (fun t => ((u (x, (y, t))) * (v (x, (y, t))))) z)) = ((((u (x, (y, z))) * (((iteratedDeriv 2 (fun t => v (t, (y, z))) x) + (iteratedDeriv 2 (fun t => v (x, (t, z))) y)) + (iteratedDeriv 2 (fun t => v (x, (y, t))) z))) + ((v (x, (y, z))) * (((iteratedDeriv 2 (fun t => u (t, (y, z))) x) + (iteratedDeriv 2 (fun t => u (x, (t, z))) y)) + (iteratedDeriv 2 (fun t => u (x, (y, t))) z)))) + (2 * ((((iteratedDeriv 1 (fun t => u (t, (y, z))) x) * (iteratedDeriv 1 (fun t => v (t, (y, z))) x)) + ((iteratedDeriv 1 (fun t => u (x, (t, z))) y) * (iteratedDeriv 1 (fun t => v (x, (t, z))) y))) + ((iteratedDeriv 1 (fun t => u (x, (y, t))) z) * (iteratedDeriv 1 (fun t => v (x, (y, t))) z)))))))))))))
  : (forall (x : ℝ) (y : ℝ) (z : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) ∧ ((x, y, z) ∈ D)) → ((((iteratedDeriv 2 (fun t => ((u (t, (y, z))) * (v (t, (y, z))))) x) + (iteratedDeriv 2 (fun t => ((u (x, (t, z))) * (v (x, (t, z))))) y)) + (iteratedDeriv 2 (fun t => ((u (x, (y, t))) * (v (x, (y, t))))) z)) = ((((u (x, (y, z))) * (((iteratedDeriv 2 (fun t => v (t, (y, z))) x) + (iteratedDeriv 2 (fun t => v (x, (t, z))) y)) + (iteratedDeriv 2 (fun t => v (x, (y, t))) z))) + ((v (x, (y, z))) * (((iteratedDeriv 2 (fun t => u (t, (y, z))) x) + (iteratedDeriv 2 (fun t => u (x, (t, z))) y)) + (iteratedDeriv 2 (fun t => u (x, (y, t))) z)))) + (2 * ((((iteratedDeriv 1 (fun t => u (t, (y, z))) x) * (iteratedDeriv 1 (fun t => v (t, (y, z))) x)) + ((iteratedDeriv 1 (fun t => u (x, (t, z))) y) * (iteratedDeriv 1 (fun t => v (x, (t, z))) y))) + ((iteratedDeriv 1 (fun t => u (x, (y, t))) z) * (iteratedDeriv 1 (fun t => v (x, (y, t))) z)))))))) := by
  sorry

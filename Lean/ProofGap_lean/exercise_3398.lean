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

-- exercise: exercise_3398

theorem proof_gap_exercise_3398_1
  (F : (ℝ × ℝ -> ℝ))
  (z : (ℝ × ℝ -> ℝ))
  (h1 : D ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h2 : ContDiff ℝ (2 : ℕ∞) F)
  (h3 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (((x * (z (x, y))), (y * (z (x, y)))) ∈ D))))
  (h4 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((F ((x * (z (x, y))), (y * (z (x, y))))) = 0))))
  : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((((iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => F (t, p.2)) p.1)) (t, (y * (z (x, y))))) (x * (z (x, y)))) * ((z (x, y)) + (x * (iteratedDeriv 1 (fun t => z (t, y)) x)))) + (((iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => F (p.1, t)) p.2)) ((x * (z (x, y))), t)) (y * (z (x, y)))) * y) * (iteratedDeriv 1 (fun t => z (t, y)) x))) = 0))) := by
  sorry

theorem proof_gap_exercise_3398_2
  (F : (ℝ × ℝ -> ℝ))
  (z : (ℝ × ℝ -> ℝ))
  (h1 : D ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h2 : ContDiff ℝ (2 : ℕ∞) F)
  (h3 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (((x * (z (x, y))), (y * (z (x, y)))) ∈ D))))
  (h4 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((F ((x * (z (x, y))), (y * (z (x, y))))) = 0))))
  (h5 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((((iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => F (t, p.2)) p.1)) (t, (y * (z (x, y))))) (x * (z (x, y)))) * ((z (x, y)) + (x * (iteratedDeriv 1 (fun t => z (t, y)) x)))) + (((iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => F (p.1, t)) p.2)) ((x * (z (x, y))), t)) (y * (z (x, y)))) * y) * (iteratedDeriv 1 (fun t => z (t, y)) x))) = 0))))
  : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (((x * (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => F (t, p.2)) p.1)) (t, (y * (z (x, y))))) (x * (z (x, y))))) + (y * (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => F (p.1, t)) p.2)) ((x * (z (x, y))), t)) (y * (z (x, y)))))) ≠ 0)) → ((iteratedDeriv 1 (fun t => z (t, y)) x) = (-(((z (x, y)) * (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => F (t, p.2)) p.1)) (t, (y * (z (x, y))))) (x * (z (x, y))))) /. ((x * (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => F (t, p.2)) p.1)) (t, (y * (z (x, y))))) (x * (z (x, y))))) + (y * (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => F (p.1, t)) p.2)) ((x * (z (x, y))), t)) (y * (z (x, y))))))))))) := by
  sorry

theorem proof_gap_exercise_3398_3
  (F : (ℝ × ℝ -> ℝ))
  (z : (ℝ × ℝ -> ℝ))
  (h1 : D ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h2 : ContDiff ℝ (2 : ℕ∞) F)
  (h3 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (((x * (z (x, y))), (y * (z (x, y)))) ∈ D))))
  (h4 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((F ((x * (z (x, y))), (y * (z (x, y))))) = 0))))
  (h5 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((((iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => F (t, p.2)) p.1)) (t, (y * (z (x, y))))) (x * (z (x, y)))) * ((z (x, y)) + (x * (iteratedDeriv 1 (fun t => z (t, y)) x)))) + (((iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => F (p.1, t)) p.2)) ((x * (z (x, y))), t)) (y * (z (x, y)))) * y) * (iteratedDeriv 1 (fun t => z (t, y)) x))) = 0))))
  (h6 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (((x * (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => F (t, p.2)) p.1)) (t, (y * (z (x, y))))) (x * (z (x, y))))) + (y * (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => F (p.1, t)) p.2)) ((x * (z (x, y))), t)) (y * (z (x, y)))))) ≠ 0)) → ((iteratedDeriv 1 (fun t => z (t, y)) x) = (-(((z (x, y)) * (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => F (t, p.2)) p.1)) (t, (y * (z (x, y))))) (x * (z (x, y))))) /. ((x * (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => F (t, p.2)) p.1)) (t, (y * (z (x, y))))) (x * (z (x, y))))) + (y * (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => F (p.1, t)) p.2)) ((x * (z (x, y))), t)) (y * (z (x, y))))))))))))
  : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 2 (fun t => z (t, y)) x) = ((-(1 /. (((x * (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => F (t, p.2)) p.1)) (t, (y * (z (x, y))))) (x * (z (x, y))))) + (y * (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => F (p.1, t)) p.2)) ((x * (z (x, y))), t)) (y * (z (x, y)))))) ^ (3 : ℕ)))) * ((((y ^ (2 : ℕ)) * ((z (x, y)) ^ (2 : ℕ))) * (((((iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => F (t, p.2)) p.1)) (t, (y * (z (x, y))))) (x * (z (x, y)))) ^ (2 : ℕ)) * (iteratedDeriv 2 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => F (p.1, t)) p.2)) (p.1, t)) p.2)) ((x * (z (x, y))), t)) (y * (z (x, y))))) - (((2 * (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => F (t, p.2)) p.1)) (t, (y * (z (x, y))))) (x * (z (x, y))))) * (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => F (p.1, t)) p.2)) ((x * (z (x, y))), t)) (y * (z (x, y))))) * (iteratedDeriv 2 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => F (t, p.2)) p.1)) (p.1, t)) p.2)) ((x * (z (x, y))), t)) (y * (z (x, y)))))) + (((iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => F (p.1, t)) p.2)) ((x * (z (x, y))), t)) (y * (z (x, y)))) ^ (2 : ℕ)) * (iteratedDeriv 2 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => F (t, p.2)) p.1)) (t, p.2)) p.1)) (t, (y * (z (x, y))))) (x * (z (x, y))))))) - (((2 * (z (x, y))) * ((iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => F (t, p.2)) p.1)) (t, (y * (z (x, y))))) (x * (z (x, y)))) ^ (2 : ℕ))) * ((x * (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => F (t, p.2)) p.1)) (t, (y * (z (x, y))))) (x * (z (x, y))))) + (y * (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => F (p.1, t)) p.2)) ((x * (z (x, y))), t)) (y * (z (x, y)))))))))))) := by
  sorry

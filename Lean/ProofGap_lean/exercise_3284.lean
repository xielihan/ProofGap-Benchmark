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

-- exercise: exercise_3284

theorem proof_gap_exercise_3284_1
  (u : (ℝ × ℝ -> ℝ))
  (f : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), ((((y ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (y ∈ ((Set.univ : Set ℝ) \ ({x | x = 0})))) → ((u (x, y)) = (f (x, (x /. y)))))))
  (h2 : Differentiable ℝ f)
  (h3 : Differentiable ℝ (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => f (t, p.2)) p.1)))
  : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (y ∈ ((Set.univ : Set ℝ) \ ({x | x = 0})))) → ((iteratedDeriv 1 (fun t => u (t, y)) x) = ((iteratedDeriv 1 (fun t => f (t, (x /. y))) x) + ((1 /. y) * (iteratedDeriv 1 (fun t => f (x, t)) (x /. y))))))) := by
  sorry

theorem proof_gap_exercise_3284_2
  (u : (ℝ × ℝ -> ℝ))
  (f : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), ((((y ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (y ∈ ((Set.univ : Set ℝ) \ ({x | x = 0})))) → ((u (x, y)) = (f (x, (x /. y)))))))
  (h2 : Differentiable ℝ f)
  (h3 : Differentiable ℝ (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => f (t, p.2)) p.1)))
  (h4 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (y ∈ ((Set.univ : Set ℝ) \ ({x | x = 0})))) → ((iteratedDeriv 1 (fun t => u (t, y)) x) = ((iteratedDeriv 1 (fun t => f (t, (x /. y))) x) + ((1 /. y) * (iteratedDeriv 1 (fun t => f (x, t)) (x /. y))))))))
  : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (y ∈ ((Set.univ : Set ℝ) \ ({x | x = 0})))) → ((iteratedDeriv 1 (fun t => u (x, t)) y) = ((-(x /. (y ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => f (x, t)) (x /. y)))))) := by
  sorry

theorem proof_gap_exercise_3284_3
  (u : (ℝ × ℝ -> ℝ))
  (f : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), ((((y ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (y ∈ ((Set.univ : Set ℝ) \ ({x | x = 0})))) → ((u (x, y)) = (f (x, (x /. y)))))))
  (h2 : Differentiable ℝ f)
  (h3 : Differentiable ℝ (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => f (t, p.2)) p.1)))
  (h4 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (y ∈ ((Set.univ : Set ℝ) \ ({x | x = 0})))) → ((iteratedDeriv 1 (fun t => u (t, y)) x) = ((iteratedDeriv 1 (fun t => f (t, (x /. y))) x) + ((1 /. y) * (iteratedDeriv 1 (fun t => f (x, t)) (x /. y))))))))
  (h5 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (y ∈ ((Set.univ : Set ℝ) \ ({x | x = 0})))) → ((iteratedDeriv 1 (fun t => u (x, t)) y) = ((-(x /. (y ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => f (x, t)) (x /. y)))))))
  : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (y ∈ ((Set.univ : Set ℝ) \ ({x | x = 0})))) → ((iteratedDeriv 2 (fun t => u (t, y)) x) = (((iteratedDeriv 2 (fun t => f (t, (x /. y))) x) + ((2 /. y) * (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => f (t, p.2)) p.1)) (x, t)) (x /. y)))) + ((1 /. (y ^ (2 : ℕ))) * (iteratedDeriv 2 (fun t => f (x, t)) (x /. y))))))) := by
  sorry

theorem proof_gap_exercise_3284_4
  (u : (ℝ × ℝ -> ℝ))
  (f : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), ((((y ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (y ∈ ((Set.univ : Set ℝ) \ ({x | x = 0})))) → ((u (x, y)) = (f (x, (x /. y)))))))
  (h2 : Differentiable ℝ f)
  (h3 : Differentiable ℝ (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => f (t, p.2)) p.1)))
  (h4 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (y ∈ ((Set.univ : Set ℝ) \ ({x | x = 0})))) → ((iteratedDeriv 1 (fun t => u (t, y)) x) = ((iteratedDeriv 1 (fun t => f (t, (x /. y))) x) + ((1 /. y) * (iteratedDeriv 1 (fun t => f (x, t)) (x /. y))))))))
  (h5 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (y ∈ ((Set.univ : Set ℝ) \ ({x | x = 0})))) → ((iteratedDeriv 1 (fun t => u (x, t)) y) = ((-(x /. (y ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => f (x, t)) (x /. y)))))))
  (h6 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (y ∈ ((Set.univ : Set ℝ) \ ({x | x = 0})))) → ((iteratedDeriv 2 (fun t => u (t, y)) x) = (((iteratedDeriv 2 (fun t => f (t, (x /. y))) x) + ((2 /. y) * (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => f (t, p.2)) p.1)) (x, t)) (x /. y)))) + ((1 /. (y ^ (2 : ℕ))) * (iteratedDeriv 2 (fun t => f (x, t)) (x /. y))))))))
  : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (y ∈ ((Set.univ : Set ℝ) \ ({x | x = 0})))) → ((iteratedDeriv 2 (fun t => u (x, t)) y) = ((((2 * x) /. (y ^ (3 : ℕ))) * (iteratedDeriv 1 (fun t => f (x, t)) (x /. y))) + (((x ^ (2 : ℕ)) /. (y ^ (4 : ℕ))) * (iteratedDeriv 2 (fun t => f (x, t)) (x /. y))))))) := by
  sorry

theorem proof_gap_exercise_3284_5
  (u : (ℝ × ℝ -> ℝ))
  (f : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), ((((y ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (y ∈ ((Set.univ : Set ℝ) \ ({x | x = 0})))) → ((u (x, y)) = (f (x, (x /. y)))))))
  (h2 : Differentiable ℝ f)
  (h3 : Differentiable ℝ (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => f (t, p.2)) p.1)))
  (h4 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (y ∈ ((Set.univ : Set ℝ) \ ({x | x = 0})))) → ((iteratedDeriv 1 (fun t => u (t, y)) x) = ((iteratedDeriv 1 (fun t => f (t, (x /. y))) x) + ((1 /. y) * (iteratedDeriv 1 (fun t => f (x, t)) (x /. y))))))))
  (h5 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (y ∈ ((Set.univ : Set ℝ) \ ({x | x = 0})))) → ((iteratedDeriv 1 (fun t => u (x, t)) y) = ((-(x /. (y ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => f (x, t)) (x /. y)))))))
  (h6 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (y ∈ ((Set.univ : Set ℝ) \ ({x | x = 0})))) → ((iteratedDeriv 2 (fun t => u (t, y)) x) = (((iteratedDeriv 2 (fun t => f (t, (x /. y))) x) + ((2 /. y) * (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => f (t, p.2)) p.1)) (x, t)) (x /. y)))) + ((1 /. (y ^ (2 : ℕ))) * (iteratedDeriv 2 (fun t => f (x, t)) (x /. y))))))))
  (h7 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (y ∈ ((Set.univ : Set ℝ) \ ({x | x = 0})))) → ((iteratedDeriv 2 (fun t => u (x, t)) y) = ((((2 * x) /. (y ^ (3 : ℕ))) * (iteratedDeriv 1 (fun t => f (x, t)) (x /. y))) + (((x ^ (2 : ℕ)) /. (y ^ (4 : ℕ))) * (iteratedDeriv 2 (fun t => f (x, t)) (x /. y))))))))
  : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (y ∈ ((Set.univ : Set ℝ) \ ({x | x = 0})))) → ((iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => u (t, p.2)) p.1)) (x, t)) y) = ((((-(x /. (y ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => f (t, p.2)) p.1)) (x, t)) (x /. y))) - ((1 /. (y ^ (2 : ℕ))) * (iteratedDeriv 1 (fun t => f (x, t)) (x /. y)))) - ((x /. (y ^ (3 : ℕ))) * (iteratedDeriv 2 (fun t => f (x, t)) (x /. y))))))) := by
  sorry

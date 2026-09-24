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

-- exercise: exercise_3319

theorem proof_gap_exercise_3319_1
  (u : (ℝ × (ℝ × ℝ) -> ℝ))
  (f : (ℝ × ℝ -> ℝ))
  (h1 : Differentiable ℝ f)
  (h2 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((u (x, (y, z))) = (((((1 /. 12) * (x ^ (4 : ℕ))) - (((1 /. 6) * (x ^ (3 : ℕ))) * (y + z))) + ((((1 /. 2) * (x ^ (2 : ℕ))) * y) * z)) + (f ((y - x), (z - x))))))))
  : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => u (t, (y, z))) x) = ((((((1 /. 3) * (x ^ (3 : ℕ))) - (((1 /. 2) * (x ^ (2 : ℕ))) * (y + z))) + ((x * y) * z)) - (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => f (t, p.2)) p.1)) (t, (z - x))) (y - x))) - (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => f (p.1, t)) p.2)) (t, (z - x))) (y - x)))))) := by
  sorry

theorem proof_gap_exercise_3319_2
  (u : (ℝ × (ℝ × ℝ) -> ℝ))
  (f : (ℝ × ℝ -> ℝ))
  (h1 : Differentiable ℝ f)
  (h2 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((u (x, (y, z))) = (((((1 /. 12) * (x ^ (4 : ℕ))) - (((1 /. 6) * (x ^ (3 : ℕ))) * (y + z))) + ((((1 /. 2) * (x ^ (2 : ℕ))) * y) * z)) + (f ((y - x), (z - x))))))))
  (h3 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => u (t, (y, z))) x) = ((((((1 /. 3) * (x ^ (3 : ℕ))) - (((1 /. 2) * (x ^ (2 : ℕ))) * (y + z))) + ((x * y) * z)) - (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => f (t, p.2)) p.1)) (t, (z - x))) (y - x))) - (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => f (p.1, t)) p.2)) (t, (z - x))) (y - x)))))))
  : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => u (x, (t, z))) y) = ((((-(1 /. 6)) * (x ^ (3 : ℕ))) + (((1 /. 2) * (x ^ (2 : ℕ))) * z)) + (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => f (t, p.2)) p.1)) (t, (z - x))) (y - x)))))) := by
  sorry

theorem proof_gap_exercise_3319_3
  (u : (ℝ × (ℝ × ℝ) -> ℝ))
  (f : (ℝ × ℝ -> ℝ))
  (h1 : Differentiable ℝ f)
  (h2 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((u (x, (y, z))) = (((((1 /. 12) * (x ^ (4 : ℕ))) - (((1 /. 6) * (x ^ (3 : ℕ))) * (y + z))) + ((((1 /. 2) * (x ^ (2 : ℕ))) * y) * z)) + (f ((y - x), (z - x))))))))
  (h3 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => u (t, (y, z))) x) = ((((((1 /. 3) * (x ^ (3 : ℕ))) - (((1 /. 2) * (x ^ (2 : ℕ))) * (y + z))) + ((x * y) * z)) - (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => f (t, p.2)) p.1)) (t, (z - x))) (y - x))) - (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => f (p.1, t)) p.2)) (t, (z - x))) (y - x)))))))
  (h4 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => u (x, (t, z))) y) = ((((-(1 /. 6)) * (x ^ (3 : ℕ))) + (((1 /. 2) * (x ^ (2 : ℕ))) * z)) + (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => f (t, p.2)) p.1)) (t, (z - x))) (y - x)))))))
  : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => u (x, (y, t))) z) = ((((-(1 /. 6)) * (x ^ (3 : ℕ))) + (((1 /. 2) * (x ^ (2 : ℕ))) * y)) + (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => f (p.1, t)) p.2)) (t, (z - x))) (y - x)))))) := by
  sorry

theorem proof_gap_exercise_3319_4
  (u : (ℝ × (ℝ × ℝ) -> ℝ))
  (f : (ℝ × ℝ -> ℝ))
  (h1 : Differentiable ℝ f)
  (h2 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((u (x, (y, z))) = (((((1 /. 12) * (x ^ (4 : ℕ))) - (((1 /. 6) * (x ^ (3 : ℕ))) * (y + z))) + ((((1 /. 2) * (x ^ (2 : ℕ))) * y) * z)) + (f ((y - x), (z - x))))))))
  (h3 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => u (t, (y, z))) x) = ((((((1 /. 3) * (x ^ (3 : ℕ))) - (((1 /. 2) * (x ^ (2 : ℕ))) * (y + z))) + ((x * y) * z)) - (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => f (t, p.2)) p.1)) (t, (z - x))) (y - x))) - (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => f (p.1, t)) p.2)) (t, (z - x))) (y - x)))))))
  (h4 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => u (x, (t, z))) y) = ((((-(1 /. 6)) * (x ^ (3 : ℕ))) + (((1 /. 2) * (x ^ (2 : ℕ))) * z)) + (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => f (t, p.2)) p.1)) (t, (z - x))) (y - x)))))))
  (h5 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => u (x, (y, t))) z) = ((((-(1 /. 6)) * (x ^ (3 : ℕ))) + (((1 /. 2) * (x ^ (2 : ℕ))) * y)) + (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => f (p.1, t)) p.2)) (t, (z - x))) (y - x)))))))
  : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((((iteratedDeriv 1 (fun t => u (t, (y, z))) x) + (iteratedDeriv 1 (fun t => u (x, (t, z))) y)) + (iteratedDeriv 1 (fun t => u (x, (y, t))) z)) = ((x * y) * z)))) := by
  sorry

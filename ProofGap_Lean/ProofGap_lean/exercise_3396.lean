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

-- exercise: exercise_3396

theorem proof_gap_exercise_3396_1
  (F : (ℝ × (ℝ × ℝ) -> ℝ))
  (z : (ℝ × ℝ -> ℝ))
  (h1 : Differentiable ℝ F)
  (h2 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((((iteratedDeriv 1 (fun t => (fun (p : ℝ × (ℝ × ℝ)) => (iteratedDeriv 1 (fun t => F (p.1, (t, p.2.2))) p.2.1)) ((x - y), (t, ((z (x, y)) - x)))) (y - (z (x, y)))) - (iteratedDeriv 1 (fun t => (fun (p : ℝ × (ℝ × ℝ)) => (iteratedDeriv 1 (fun t => F (p.1, (p.2.1, t))) p.2.2)) ((x - y), ((y - (z (x, y))), t))) ((z (x, y)) - x))) ≠ 0) ∧ ((F ((x - y), ((y - (z (x, y))), ((z (x, y)) - x)))) = 0)))))
  : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((((iteratedDeriv 1 (fun t => (fun (p : ℝ × (ℝ × ℝ)) => (iteratedDeriv 1 (fun t => F (t, (p.2.1, p.2.2))) p.1)) (t, ((y - (z (x, y))), ((z (x, y)) - x)))) (x - y)) + ((iteratedDeriv 1 (fun t => (fun (p : ℝ × (ℝ × ℝ)) => (iteratedDeriv 1 (fun t => F (p.1, (t, p.2.2))) p.2.1)) ((x - y), (t, ((z (x, y)) - x)))) (y - (z (x, y)))) * (-(iteratedDeriv 1 (fun t => z (t, y)) x)))) + ((iteratedDeriv 1 (fun t => (fun (p : ℝ × (ℝ × ℝ)) => (iteratedDeriv 1 (fun t => F (p.1, (p.2.1, t))) p.2.2)) ((x - y), ((y - (z (x, y))), t))) ((z (x, y)) - x)) * ((iteratedDeriv 1 (fun t => z (t, y)) x) - 1))) = 0))) := by
  sorry

theorem proof_gap_exercise_3396_2
  (F : (ℝ × (ℝ × ℝ) -> ℝ))
  (z : (ℝ × ℝ -> ℝ))
  (h1 : Differentiable ℝ F)
  (h2 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((((iteratedDeriv 1 (fun t => (fun (p : ℝ × (ℝ × ℝ)) => (iteratedDeriv 1 (fun t => F (p.1, (t, p.2.2))) p.2.1)) ((x - y), (t, ((z (x, y)) - x)))) (y - (z (x, y)))) - (iteratedDeriv 1 (fun t => (fun (p : ℝ × (ℝ × ℝ)) => (iteratedDeriv 1 (fun t => F (p.1, (p.2.1, t))) p.2.2)) ((x - y), ((y - (z (x, y))), t))) ((z (x, y)) - x))) ≠ 0) ∧ ((F ((x - y), ((y - (z (x, y))), ((z (x, y)) - x)))) = 0)))))
  (h3 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((((iteratedDeriv 1 (fun t => (fun (p : ℝ × (ℝ × ℝ)) => (iteratedDeriv 1 (fun t => F (t, (p.2.1, p.2.2))) p.1)) (t, ((y - (z (x, y))), ((z (x, y)) - x)))) (x - y)) + ((iteratedDeriv 1 (fun t => (fun (p : ℝ × (ℝ × ℝ)) => (iteratedDeriv 1 (fun t => F (p.1, (t, p.2.2))) p.2.1)) ((x - y), (t, ((z (x, y)) - x)))) (y - (z (x, y)))) * (-(iteratedDeriv 1 (fun t => z (t, y)) x)))) + ((iteratedDeriv 1 (fun t => (fun (p : ℝ × (ℝ × ℝ)) => (iteratedDeriv 1 (fun t => F (p.1, (p.2.1, t))) p.2.2)) ((x - y), ((y - (z (x, y))), t))) ((z (x, y)) - x)) * ((iteratedDeriv 1 (fun t => z (t, y)) x) - 1))) = 0))))
  : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => z (t, y)) x) = (((iteratedDeriv 1 (fun t => (fun (p : ℝ × (ℝ × ℝ)) => (iteratedDeriv 1 (fun t => F (t, (p.2.1, p.2.2))) p.1)) (t, ((y - (z (x, y))), ((z (x, y)) - x)))) (x - y)) - (iteratedDeriv 1 (fun t => (fun (p : ℝ × (ℝ × ℝ)) => (iteratedDeriv 1 (fun t => F (p.1, (p.2.1, t))) p.2.2)) ((x - y), ((y - (z (x, y))), t))) ((z (x, y)) - x))) /. ((iteratedDeriv 1 (fun t => (fun (p : ℝ × (ℝ × ℝ)) => (iteratedDeriv 1 (fun t => F (p.1, (t, p.2.2))) p.2.1)) ((x - y), (t, ((z (x, y)) - x)))) (y - (z (x, y)))) - (iteratedDeriv 1 (fun t => (fun (p : ℝ × (ℝ × ℝ)) => (iteratedDeriv 1 (fun t => F (p.1, (p.2.1, t))) p.2.2)) ((x - y), ((y - (z (x, y))), t))) ((z (x, y)) - x))))))) := by
  sorry

theorem proof_gap_exercise_3396_3
  (F : (ℝ × (ℝ × ℝ) -> ℝ))
  (z : (ℝ × ℝ -> ℝ))
  (h1 : Differentiable ℝ F)
  (h2 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((((iteratedDeriv 1 (fun t => (fun (p : ℝ × (ℝ × ℝ)) => (iteratedDeriv 1 (fun t => F (p.1, (t, p.2.2))) p.2.1)) ((x - y), (t, ((z (x, y)) - x)))) (y - (z (x, y)))) - (iteratedDeriv 1 (fun t => (fun (p : ℝ × (ℝ × ℝ)) => (iteratedDeriv 1 (fun t => F (p.1, (p.2.1, t))) p.2.2)) ((x - y), ((y - (z (x, y))), t))) ((z (x, y)) - x))) ≠ 0) ∧ ((F ((x - y), ((y - (z (x, y))), ((z (x, y)) - x)))) = 0)))))
  (h3 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((((iteratedDeriv 1 (fun t => (fun (p : ℝ × (ℝ × ℝ)) => (iteratedDeriv 1 (fun t => F (t, (p.2.1, p.2.2))) p.1)) (t, ((y - (z (x, y))), ((z (x, y)) - x)))) (x - y)) + ((iteratedDeriv 1 (fun t => (fun (p : ℝ × (ℝ × ℝ)) => (iteratedDeriv 1 (fun t => F (p.1, (t, p.2.2))) p.2.1)) ((x - y), (t, ((z (x, y)) - x)))) (y - (z (x, y)))) * (-(iteratedDeriv 1 (fun t => z (t, y)) x)))) + ((iteratedDeriv 1 (fun t => (fun (p : ℝ × (ℝ × ℝ)) => (iteratedDeriv 1 (fun t => F (p.1, (p.2.1, t))) p.2.2)) ((x - y), ((y - (z (x, y))), t))) ((z (x, y)) - x)) * ((iteratedDeriv 1 (fun t => z (t, y)) x) - 1))) = 0))))
  (h4 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => z (t, y)) x) = (((iteratedDeriv 1 (fun t => (fun (p : ℝ × (ℝ × ℝ)) => (iteratedDeriv 1 (fun t => F (t, (p.2.1, p.2.2))) p.1)) (t, ((y - (z (x, y))), ((z (x, y)) - x)))) (x - y)) - (iteratedDeriv 1 (fun t => (fun (p : ℝ × (ℝ × ℝ)) => (iteratedDeriv 1 (fun t => F (p.1, (p.2.1, t))) p.2.2)) ((x - y), ((y - (z (x, y))), t))) ((z (x, y)) - x))) /. ((iteratedDeriv 1 (fun t => (fun (p : ℝ × (ℝ × ℝ)) => (iteratedDeriv 1 (fun t => F (p.1, (t, p.2.2))) p.2.1)) ((x - y), (t, ((z (x, y)) - x)))) (y - (z (x, y)))) - (iteratedDeriv 1 (fun t => (fun (p : ℝ × (ℝ × ℝ)) => (iteratedDeriv 1 (fun t => F (p.1, (p.2.1, t))) p.2.2)) ((x - y), ((y - (z (x, y))), t))) ((z (x, y)) - x))))))))
  : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => z (x, t)) y) = (((iteratedDeriv 1 (fun t => (fun (p : ℝ × (ℝ × ℝ)) => (iteratedDeriv 1 (fun t => F (p.1, (t, p.2.2))) p.2.1)) ((x - y), (t, ((z (x, y)) - x)))) (y - (z (x, y)))) - (iteratedDeriv 1 (fun t => (fun (p : ℝ × (ℝ × ℝ)) => (iteratedDeriv 1 (fun t => F (t, (p.2.1, p.2.2))) p.1)) (t, ((y - (z (x, y))), ((z (x, y)) - x)))) (x - y))) /. ((iteratedDeriv 1 (fun t => (fun (p : ℝ × (ℝ × ℝ)) => (iteratedDeriv 1 (fun t => F (p.1, (t, p.2.2))) p.2.1)) ((x - y), (t, ((z (x, y)) - x)))) (y - (z (x, y)))) - (iteratedDeriv 1 (fun t => (fun (p : ℝ × (ℝ × ℝ)) => (iteratedDeriv 1 (fun t => F (p.1, (p.2.1, t))) p.2.2)) ((x - y), ((y - (z (x, y))), t))) ((z (x, y)) - x))))))) := by
  sorry

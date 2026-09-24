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

-- exercise: exercise_3352

theorem proof_gap_exercise_3352_1
  (u : (ℝ × ℝ -> ℝ))
  (h1 : Differentiable ℝ u)
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((u (x, (x ^ (2 : ℕ)))) = 1))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => u (t, (x ^ (2 : ℕ)))) x) = x))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => (u (t, (t ^ (2 : ℕ))))) x) = ((iteratedDeriv 1 (fun t => u (t, (x ^ (2 : ℕ)))) x) + ((iteratedDeriv 1 (fun t => u (x, t)) (x ^ (2 : ℕ))) * (iteratedDeriv 1 (fun t => (t ^ (2 : ℕ))) x)))))) := by
  sorry

theorem proof_gap_exercise_3352_2
  (u : (ℝ × ℝ -> ℝ))
  (h1 : Differentiable ℝ u)
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((u (x, (x ^ (2 : ℕ)))) = 1))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => u (t, (x ^ (2 : ℕ)))) x) = x))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => (u (t, (t ^ (2 : ℕ))))) x) = ((iteratedDeriv 1 (fun t => u (t, (x ^ (2 : ℕ)))) x) + ((iteratedDeriv 1 (fun t => u (x, t)) (x ^ (2 : ℕ))) * (iteratedDeriv 1 (fun t => (t ^ (2 : ℕ))) x)))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => (u (t, (t ^ (2 : ℕ))))) x) = 0))) := by
  sorry

theorem proof_gap_exercise_3352_3
  (u : (ℝ × ℝ -> ℝ))
  (h1 : Differentiable ℝ u)
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((u (x, (x ^ (2 : ℕ)))) = 1))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => u (t, (x ^ (2 : ℕ)))) x) = x))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => (u (t, (t ^ (2 : ℕ))))) x) = ((iteratedDeriv 1 (fun t => u (t, (x ^ (2 : ℕ)))) x) + ((iteratedDeriv 1 (fun t => u (x, t)) (x ^ (2 : ℕ))) * (iteratedDeriv 1 (fun t => (t ^ (2 : ℕ))) x)))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => (u (t, (t ^ (2 : ℕ))))) x) = 0))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => (t ^ (2 : ℕ))) x) = (2 * x)))) := by
  sorry

theorem proof_gap_exercise_3352_4
  (u : (ℝ × ℝ -> ℝ))
  (h1 : Differentiable ℝ u)
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((u (x, (x ^ (2 : ℕ)))) = 1))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => u (t, (x ^ (2 : ℕ)))) x) = x))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => (u (t, (t ^ (2 : ℕ))))) x) = ((iteratedDeriv 1 (fun t => u (t, (x ^ (2 : ℕ)))) x) + ((iteratedDeriv 1 (fun t => u (x, t)) (x ^ (2 : ℕ))) * (iteratedDeriv 1 (fun t => (t ^ (2 : ℕ))) x)))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => (u (t, (t ^ (2 : ℕ))))) x) = 0))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => (t ^ (2 : ℕ))) x) = (2 * x)))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((x + ((2 * x) * (iteratedDeriv 1 (fun t => u (x, t)) (x ^ (2 : ℕ))))) = 0))) := by
  sorry

theorem proof_gap_exercise_3352_5
  (u : (ℝ × ℝ -> ℝ))
  (h1 : Differentiable ℝ u)
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((u (x, (x ^ (2 : ℕ)))) = 1))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => u (t, (x ^ (2 : ℕ)))) x) = x))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => (u (t, (t ^ (2 : ℕ))))) x) = ((iteratedDeriv 1 (fun t => u (t, (x ^ (2 : ℕ)))) x) + ((iteratedDeriv 1 (fun t => u (x, t)) (x ^ (2 : ℕ))) * (iteratedDeriv 1 (fun t => (t ^ (2 : ℕ))) x)))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => (u (t, (t ^ (2 : ℕ))))) x) = 0))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => (t ^ (2 : ℕ))) x) = (2 * x)))))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((x + ((2 * x) * (iteratedDeriv 1 (fun t => u (x, t)) (x ^ (2 : ℕ))))) = 0))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => u (x, t)) (x ^ (2 : ℕ))) = (-(1 /. 2))))) := by
  sorry

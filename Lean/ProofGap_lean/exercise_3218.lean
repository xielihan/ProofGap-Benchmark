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

-- exercise: exercise_3218

theorem proof_gap_exercise_3218_1
  (u : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (y ≠ 0)) → ((u (x, y)) = ((Real.cos (x ^ (2 : ℕ))) /. y)))))
  : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (y ≠ 0)) → ((iteratedDeriv 1 (fun t => u (t, y)) x) = (-(((2 * x) * (Real.sin (x ^ (2 : ℕ)))) /. y))))) := by
  sorry

theorem proof_gap_exercise_3218_2
  (u : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (y ≠ 0)) → ((u (x, y)) = ((Real.cos (x ^ (2 : ℕ))) /. y)))))
  (h2 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (y ≠ 0)) → ((iteratedDeriv 1 (fun t => u (t, y)) x) = (-(((2 * x) * (Real.sin (x ^ (2 : ℕ)))) /. y))))))
  : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (y ≠ 0)) → ((iteratedDeriv 1 (fun t => u (x, t)) y) = (-((Real.cos (x ^ (2 : ℕ))) /. (y ^ (2 : ℕ))))))) := by
  sorry

theorem proof_gap_exercise_3218_3
  (u : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (y ≠ 0)) → ((u (x, y)) = ((Real.cos (x ^ (2 : ℕ))) /. y)))))
  (h2 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (y ≠ 0)) → ((iteratedDeriv 1 (fun t => u (t, y)) x) = (-(((2 * x) * (Real.sin (x ^ (2 : ℕ)))) /. y))))))
  (h3 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (y ≠ 0)) → ((iteratedDeriv 1 (fun t => u (x, t)) y) = (-((Real.cos (x ^ (2 : ℕ))) /. (y ^ (2 : ℕ))))))))
  : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (y ≠ 0)) → ((iteratedDeriv 2 (fun t => u (t, y)) x) = (-(((2 * (Real.sin (x ^ (2 : ℕ)))) + ((4 * (x ^ (2 : ℕ))) * (Real.cos (x ^ (2 : ℕ))))) /. y))))) := by
  sorry

theorem proof_gap_exercise_3218_4
  (u : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (y ≠ 0)) → ((u (x, y)) = ((Real.cos (x ^ (2 : ℕ))) /. y)))))
  (h2 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (y ≠ 0)) → ((iteratedDeriv 1 (fun t => u (t, y)) x) = (-(((2 * x) * (Real.sin (x ^ (2 : ℕ)))) /. y))))))
  (h3 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (y ≠ 0)) → ((iteratedDeriv 1 (fun t => u (x, t)) y) = (-((Real.cos (x ^ (2 : ℕ))) /. (y ^ (2 : ℕ))))))))
  (h4 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (y ≠ 0)) → ((iteratedDeriv 2 (fun t => u (t, y)) x) = (-(((2 * (Real.sin (x ^ (2 : ℕ)))) + ((4 * (x ^ (2 : ℕ))) * (Real.cos (x ^ (2 : ℕ))))) /. y))))))
  : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (y ≠ 0)) → ((iteratedDeriv 2 (fun t => u (x, t)) y) = ((2 * (Real.cos (x ^ (2 : ℕ)))) /. (y ^ (3 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_3218_5
  (u : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (y ≠ 0)) → ((u (x, y)) = ((Real.cos (x ^ (2 : ℕ))) /. y)))))
  (h2 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (y ≠ 0)) → ((iteratedDeriv 1 (fun t => u (t, y)) x) = (-(((2 * x) * (Real.sin (x ^ (2 : ℕ)))) /. y))))))
  (h3 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (y ≠ 0)) → ((iteratedDeriv 1 (fun t => u (x, t)) y) = (-((Real.cos (x ^ (2 : ℕ))) /. (y ^ (2 : ℕ))))))))
  (h4 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (y ≠ 0)) → ((iteratedDeriv 2 (fun t => u (t, y)) x) = (-(((2 * (Real.sin (x ^ (2 : ℕ)))) + ((4 * (x ^ (2 : ℕ))) * (Real.cos (x ^ (2 : ℕ))))) /. y))))))
  (h5 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (y ≠ 0)) → ((iteratedDeriv 2 (fun t => u (x, t)) y) = ((2 * (Real.cos (x ^ (2 : ℕ)))) /. (y ^ (3 : ℕ)))))))
  : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (y ≠ 0)) → ((iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => u (t, p.2)) p.1)) (x, t)) y) = (((2 * x) * (Real.sin (x ^ (2 : ℕ)))) /. (y ^ (2 : ℕ)))))) := by
  sorry

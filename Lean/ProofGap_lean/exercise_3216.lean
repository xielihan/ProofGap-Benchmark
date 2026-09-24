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

-- exercise: exercise_3216

theorem proof_gap_exercise_3216_1
  (u : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (0, 0))) → ((u (x, y)) = (x /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))))))
  : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (0, 0))) → (((iteratedDeriv 1 (fun t => u (t, y)) x) = ((1 /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) - (((2 * x) * x) /. (2 * (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (3 /. 2)))))) ∧ (((1 /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) - (((2 * x) * x) /. (2 * (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (3 /. 2))))) = ((y ^ (2 : ℕ)) /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (3 /. 2))))))) := by
  sorry

theorem proof_gap_exercise_3216_2
  (u : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (0, 0))) → ((u (x, y)) = (x /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))))))
  (h2 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (0, 0))) → (((iteratedDeriv 1 (fun t => u (t, y)) x) = ((1 /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) - (((2 * x) * x) /. (2 * (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (3 /. 2)))))) ∧ (((1 /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) - (((2 * x) * x) /. (2 * (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (3 /. 2))))) = ((y ^ (2 : ℕ)) /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (3 /. 2))))))))
  : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (0, 0))) → ((iteratedDeriv 1 (fun t => u (x, t)) y) = (-((x * y) /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (3 /. 2))))))) := by
  sorry

theorem proof_gap_exercise_3216_3
  (u : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (0, 0))) → ((u (x, y)) = (x /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))))))
  (h2 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (0, 0))) → (((iteratedDeriv 1 (fun t => u (t, y)) x) = ((1 /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) - (((2 * x) * x) /. (2 * (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (3 /. 2)))))) ∧ (((1 /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) - (((2 * x) * x) /. (2 * (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (3 /. 2))))) = ((y ^ (2 : ℕ)) /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (3 /. 2))))))))
  (h3 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (0, 0))) → ((iteratedDeriv 1 (fun t => u (x, t)) y) = (-((x * y) /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (3 /. 2))))))))
  : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (0, 0))) → (((iteratedDeriv 2 (fun t => u (t, y)) x) = (((-(3 /. 2)) * (y ^ (2 : ℕ))) * ((2 * x) /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (5 /. 2))))) ∧ ((((-(3 /. 2)) * (y ^ (2 : ℕ))) * ((2 * x) /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (5 /. 2)))) = (-(((3 * x) * (y ^ (2 : ℕ))) /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (5 /. 2)))))))) := by
  sorry

theorem proof_gap_exercise_3216_4
  (u : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (0, 0))) → ((u (x, y)) = (x /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))))))
  (h2 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (0, 0))) → (((iteratedDeriv 1 (fun t => u (t, y)) x) = ((1 /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) - (((2 * x) * x) /. (2 * (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (3 /. 2)))))) ∧ (((1 /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) - (((2 * x) * x) /. (2 * (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (3 /. 2))))) = ((y ^ (2 : ℕ)) /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (3 /. 2))))))))
  (h3 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (0, 0))) → ((iteratedDeriv 1 (fun t => u (x, t)) y) = (-((x * y) /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (3 /. 2))))))))
  (h4 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (0, 0))) → (((iteratedDeriv 2 (fun t => u (t, y)) x) = (((-(3 /. 2)) * (y ^ (2 : ℕ))) * ((2 * x) /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (5 /. 2))))) ∧ ((((-(3 /. 2)) * (y ^ (2 : ℕ))) * ((2 * x) /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (5 /. 2)))) = (-(((3 * x) * (y ^ (2 : ℕ))) /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (5 /. 2)))))))))
  : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (0, 0))) → (((iteratedDeriv 2 (fun t => u (x, t)) y) = ((-(x /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (3 /. 2)))) + ((((3 /. 2) * x) * y) * ((2 * y) /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (5 /. 2)))))) ∧ (((-(x /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (3 /. 2)))) + ((((3 /. 2) * x) * y) * ((2 * y) /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (5 /. 2))))) = ((x * ((2 * (y ^ (2 : ℕ))) - (x ^ (2 : ℕ)))) /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (5 /. 2))))))) := by
  sorry

theorem proof_gap_exercise_3216_5
  (u : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (0, 0))) → ((u (x, y)) = (x /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))))))
  (h2 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (0, 0))) → (((iteratedDeriv 1 (fun t => u (t, y)) x) = ((1 /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) - (((2 * x) * x) /. (2 * (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (3 /. 2)))))) ∧ (((1 /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) - (((2 * x) * x) /. (2 * (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (3 /. 2))))) = ((y ^ (2 : ℕ)) /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (3 /. 2))))))))
  (h3 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (0, 0))) → ((iteratedDeriv 1 (fun t => u (x, t)) y) = (-((x * y) /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (3 /. 2))))))))
  (h4 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (0, 0))) → (((iteratedDeriv 2 (fun t => u (t, y)) x) = (((-(3 /. 2)) * (y ^ (2 : ℕ))) * ((2 * x) /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (5 /. 2))))) ∧ ((((-(3 /. 2)) * (y ^ (2 : ℕ))) * ((2 * x) /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (5 /. 2)))) = (-(((3 * x) * (y ^ (2 : ℕ))) /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (5 /. 2)))))))))
  (h5 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (0, 0))) → (((iteratedDeriv 2 (fun t => u (x, t)) y) = ((-(x /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (3 /. 2)))) + ((((3 /. 2) * x) * y) * ((2 * y) /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (5 /. 2)))))) ∧ (((-(x /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (3 /. 2)))) + ((((3 /. 2) * x) * y) * ((2 * y) /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (5 /. 2))))) = ((x * ((2 * (y ^ (2 : ℕ))) - (x ^ (2 : ℕ)))) /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (5 /. 2))))))))
  : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (0, 0))) → (((iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => u (t, p.2)) p.1)) (x, t)) y) = (((2 * y) /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (3 /. 2))) - ((3 * (y ^ (3 : ℕ))) /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (5 /. 2))))) ∧ ((((2 * y) /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (3 /. 2))) - ((3 * (y ^ (3 : ℕ))) /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (5 /. 2)))) = ((y * ((2 * (x ^ (2 : ℕ))) - (y ^ (2 : ℕ)))) /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (5 /. 2))))))) := by
  sorry

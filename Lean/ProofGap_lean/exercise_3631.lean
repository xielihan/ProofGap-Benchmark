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

-- exercise: exercise_3631

theorem proof_gap_exercise_3631_1
  (z : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((z (x, y)) = (1 - (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))))))
  : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (0, 0))) → ((iteratedDeriv 1 (fun t => z (t, y)) x) = (-(x /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))) := by
  sorry

theorem proof_gap_exercise_3631_2
  (z : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((z (x, y)) = (1 - (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))))))
  (h2 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (0, 0))) → ((iteratedDeriv 1 (fun t => z (t, y)) x) = (-(x /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))))
  : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (0, 0))) → ((iteratedDeriv 1 (fun t => z (x, t)) y) = (-(y /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))) := by
  sorry

theorem proof_gap_exercise_3631_3
  (z : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((z (x, y)) = (1 - (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))))))
  (h2 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (0, 0))) → ((iteratedDeriv 1 (fun t => z (t, y)) x) = (-(x /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))))
  (h3 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (0, 0))) → ((iteratedDeriv 1 (fun t => z (x, t)) y) = (-(y /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))))
  : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (0, 0))) → ((z (x, y)) < 1))) := by
  sorry

theorem proof_gap_exercise_3631_4
  (z : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((z (x, y)) = (1 - (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))))))
  (h2 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (0, 0))) → ((iteratedDeriv 1 (fun t => z (t, y)) x) = (-(x /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))))
  (h3 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (0, 0))) → ((iteratedDeriv 1 (fun t => z (x, t)) y) = (-(y /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))))
  (h4 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (0, 0))) → ((z (x, y)) < 1))))
  : (z ((0 : ℝ), (0 : ℝ))) = 1 := by
  sorry

theorem proof_gap_exercise_3631_5
  (z : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((z (x, y)) = (1 - (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))))))
  (h2 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (0, 0))) → ((iteratedDeriv 1 (fun t => z (t, y)) x) = (-(x /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))))
  (h3 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (0, 0))) → ((iteratedDeriv 1 (fun t => z (x, t)) y) = (-(y /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))))
  (h4 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (0, 0))) → ((z (x, y)) < 1))))
  (h5 : (z ((0 : ℝ), (0 : ℝ))) = 1)
  : (lpMaximumPoints z) = ({x | x = (0, 0)}) := by
  sorry

theorem proof_gap_exercise_3631_6
  (z : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((z (x, y)) = (1 - (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))))))
  (h2 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (0, 0))) → ((iteratedDeriv 1 (fun t => z (t, y)) x) = (-(x /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))))
  (h3 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (0, 0))) → ((iteratedDeriv 1 (fun t => z (x, t)) y) = (-(y /. (Real.rpow ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))))
  (h4 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((x, y) ≠ (0, 0))) → ((z (x, y)) < 1))))
  (h5 : (z ((0 : ℝ), (0 : ℝ))) = 1)
  (h6 : (lpMaximumPoints z) = ({x | x = (0, 0)}))
  : (z ((0 : ℝ), (0 : ℝ))) = 1 := by
  sorry

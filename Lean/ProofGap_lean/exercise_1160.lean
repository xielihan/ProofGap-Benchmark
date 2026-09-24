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

-- exercise: exercise_1160

theorem proof_gap_exercise_1160_1
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x < 1)) → ((y x) = ((1 + x) /. (Real.rpow (1 - x) (((2 : ℝ))⁻¹)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x < 1)) → ((y x) = ((1 + x) * (Real.rpow (1 - x) (-(1 /. 2))))))) := by
  sorry

theorem proof_gap_exercise_1160_2
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x < 1)) → ((y x) = ((1 + x) /. (Real.rpow (1 - x) (((2 : ℝ))⁻¹)))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x < 1)) → ((y x) = ((1 + x) * (Real.rpow (1 - x) (-(1 /. 2))))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x < 1)) → ((iteratedDeriv 100 (fun t => y t) x) = (((1 + x) * (iteratedDeriv 100 (fun t => (Real.rpow (1 - t) (-(1 /. 2)))) x)) + ((Nat.choose (100 : ℕ) (1 : ℕ)) * (iteratedDeriv 99 (fun t => (Real.rpow (1 - t) (-(1 /. 2)))) x)))))) := by
  sorry

theorem proof_gap_exercise_1160_3
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x < 1)) → ((y x) = ((1 + x) /. (Real.rpow (1 - x) (((2 : ℝ))⁻¹)))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x < 1)) → ((y x) = ((1 + x) * (Real.rpow (1 - x) (-(1 /. 2))))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x < 1)) → ((iteratedDeriv 100 (fun t => y t) x) = (((1 + x) * (iteratedDeriv 100 (fun t => (Real.rpow (1 - t) (-(1 /. 2)))) x)) + ((Nat.choose (100 : ℕ) (1 : ℕ)) * (iteratedDeriv 99 (fun t => (Real.rpow (1 - t) (-(1 /. 2)))) x)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x < 1)) → ((iteratedDeriv 100 (fun t => y t) x) = ((((1 + x) * ((∏ k ∈ Finset.Icc (0 : ℕ) (99 : ℕ), ((2 * k) + 1)) /. ((2 : ℕ) ^ (100 : ℕ)))) * (Real.rpow (1 - x) (-(201 /. 2)))) + ((100 * ((∏ k ∈ Finset.Icc (0 : ℕ) (98 : ℕ), ((2 * k) + 1)) /. ((2 : ℕ) ^ (99 : ℕ)))) * (Real.rpow (1 - x) (-(199 /. 2)))))))) := by
  sorry

theorem proof_gap_exercise_1160_4
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x < 1)) → ((y x) = ((1 + x) /. (Real.rpow (1 - x) (((2 : ℝ))⁻¹)))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x < 1)) → ((y x) = ((1 + x) * (Real.rpow (1 - x) (-(1 /. 2))))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x < 1)) → ((iteratedDeriv 100 (fun t => y t) x) = (((1 + x) * (iteratedDeriv 100 (fun t => (Real.rpow (1 - t) (-(1 /. 2)))) x)) + ((Nat.choose (100 : ℕ) (1 : ℕ)) * (iteratedDeriv 99 (fun t => (Real.rpow (1 - t) (-(1 /. 2)))) x)))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x < 1)) → ((iteratedDeriv 100 (fun t => y t) x) = ((((1 + x) * ((∏ k ∈ Finset.Icc (0 : ℕ) (99 : ℕ), ((2 * k) + 1)) /. ((2 : ℕ) ^ (100 : ℕ)))) * (Real.rpow (1 - x) (-(201 /. 2)))) + ((100 * ((∏ k ∈ Finset.Icc (0 : ℕ) (98 : ℕ), ((2 * k) + 1)) /. ((2 : ℕ) ^ (99 : ℕ)))) * (Real.rpow (1 - x) (-(199 /. 2)))))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x < 1)) → ((iteratedDeriv 100 (fun t => y t) x) = (((∏ k ∈ Finset.Icc (0 : ℕ) (98 : ℕ), ((2 * k) + 1)) * (399 - x)) /. ((((2 : ℕ) ^ (100 : ℕ)) * ((1 - x) ^ (100 : ℕ))) * (Real.rpow (1 - x) (((2 : ℝ))⁻¹))))))) := by
  sorry

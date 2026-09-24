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

-- exercise: exercise_3123

theorem proof_gap_exercise_3123_1
  (y : (ℝ -> ℝ))
  (P : (ℝ -> ℝ))
  (h1 : (y (1 : ℝ)) = 1)
  (h2 : (y (25 : ℝ)) = 5)
  (h3 : (y (100 : ℝ)) = 10)
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (1 ≤ x)) ∧ (x ≤ 100)) → ((y x) = (Real.rpow x (((2 : ℝ))⁻¹))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((P x) = ((((((x - 25) * (x - 100)) /. ((-(24 : ℝ)) * (-(99 : ℝ)))) * 1) + ((((x - 1) * (x - 100)) /. (24 * (-(75 : ℝ)))) * 5)) + ((((x - 1) * (x - 25)) /. (99 * 75)) * 10))))) := by
  sorry

theorem proof_gap_exercise_3123_2
  (y : (ℝ -> ℝ))
  (P : (ℝ -> ℝ))
  (h1 : (y (1 : ℝ)) = 1)
  (h2 : (y (25 : ℝ)) = 5)
  (h3 : (y (100 : ℝ)) = 10)
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (1 ≤ x)) ∧ (x ≤ 100)) → ((y x) = (Real.rpow x (((2 : ℝ))⁻¹))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((P x) = ((((((x - 25) * (x - 100)) /. ((-(24 : ℝ)) * (-(99 : ℝ)))) * 1) + ((((x - 1) * (x - 100)) /. (24 * (-(75 : ℝ)))) * 5)) + ((((x - 1) * (x - 25)) /. (99 * 75)) * 10))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((P x) = (((((0808 : ℝ) /. (1000 : ℝ))) + ((((0193 : ℝ) /. (1000 : ℝ))) * x)) - ((((000101 : ℝ) /. (100000 : ℝ))) * (x ^ (2 : ℕ))))))) := by
  sorry

theorem proof_gap_exercise_3123_3
  (y : (ℝ -> ℝ))
  (P : (ℝ -> ℝ))
  (h1 : (y (1 : ℝ)) = 1)
  (h2 : (y (25 : ℝ)) = 5)
  (h3 : (y (100 : ℝ)) = 10)
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (1 ≤ x)) ∧ (x ≤ 100)) → ((y x) = (Real.rpow x (((2 : ℝ))⁻¹))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((P x) = ((((((x - 25) * (x - 100)) /. ((-(24 : ℝ)) * (-(99 : ℝ)))) * 1) + ((((x - 1) * (x - 100)) /. (24 * (-(75 : ℝ)))) * 5)) + ((((x - 1) * (x - 25)) /. (99 * 75)) * 10))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((P x) = (((((0808 : ℝ) /. (1000 : ℝ))) + ((((0193 : ℝ) /. (1000 : ℝ))) * x)) - ((((000101 : ℝ) /. (100000 : ℝ))) * (x ^ (2 : ℕ))))))))
  : (P (4 : ℝ)) = (((1564 : ℝ) /. (1000 : ℝ))) := by
  sorry

theorem proof_gap_exercise_3123_4
  (y : (ℝ -> ℝ))
  (P : (ℝ -> ℝ))
  (h1 : (y (1 : ℝ)) = 1)
  (h2 : (y (25 : ℝ)) = 5)
  (h3 : (y (100 : ℝ)) = 10)
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (1 ≤ x)) ∧ (x ≤ 100)) → ((y x) = (Real.rpow x (((2 : ℝ))⁻¹))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((P x) = ((((((x - 25) * (x - 100)) /. ((-(24 : ℝ)) * (-(99 : ℝ)))) * 1) + ((((x - 1) * (x - 100)) /. (24 * (-(75 : ℝ)))) * 5)) + ((((x - 1) * (x - 25)) /. (99 * 75)) * 10))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((P x) = (((((0808 : ℝ) /. (1000 : ℝ))) + ((((0193 : ℝ) /. (1000 : ℝ))) * x)) - ((((000101 : ℝ) /. (100000 : ℝ))) * (x ^ (2 : ℕ))))))))
  (h7 : (P (4 : ℝ)) = (((1564 : ℝ) /. (1000 : ℝ))))
  : (P (9 : ℝ)) = (((2463 : ℝ) /. (1000 : ℝ))) := by
  sorry

theorem proof_gap_exercise_3123_5
  (y : (ℝ -> ℝ))
  (P : (ℝ -> ℝ))
  (h1 : (y (1 : ℝ)) = 1)
  (h2 : (y (25 : ℝ)) = 5)
  (h3 : (y (100 : ℝ)) = 10)
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (1 ≤ x)) ∧ (x ≤ 100)) → ((y x) = (Real.rpow x (((2 : ℝ))⁻¹))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((P x) = ((((((x - 25) * (x - 100)) /. ((-(24 : ℝ)) * (-(99 : ℝ)))) * 1) + ((((x - 1) * (x - 100)) /. (24 * (-(75 : ℝ)))) * 5)) + ((((x - 1) * (x - 25)) /. (99 * 75)) * 10))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((P x) = (((((0808 : ℝ) /. (1000 : ℝ))) + ((((0193 : ℝ) /. (1000 : ℝ))) * x)) - ((((000101 : ℝ) /. (100000 : ℝ))) * (x ^ (2 : ℕ))))))))
  (h7 : (P (4 : ℝ)) = (((1564 : ℝ) /. (1000 : ℝ))))
  (h8 : (P (9 : ℝ)) = (((2463 : ℝ) /. (1000 : ℝ))))
  : (P (16 : ℝ)) = (((3637 : ℝ) /. (1000 : ℝ))) := by
  sorry

theorem proof_gap_exercise_3123_6
  (y : (ℝ -> ℝ))
  (P : (ℝ -> ℝ))
  (h1 : (y (1 : ℝ)) = 1)
  (h2 : (y (25 : ℝ)) = 5)
  (h3 : (y (100 : ℝ)) = 10)
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (1 ≤ x)) ∧ (x ≤ 100)) → ((y x) = (Real.rpow x (((2 : ℝ))⁻¹))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((P x) = ((((((x - 25) * (x - 100)) /. ((-(24 : ℝ)) * (-(99 : ℝ)))) * 1) + ((((x - 1) * (x - 100)) /. (24 * (-(75 : ℝ)))) * 5)) + ((((x - 1) * (x - 25)) /. (99 * 75)) * 10))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((P x) = (((((0808 : ℝ) /. (1000 : ℝ))) + ((((0193 : ℝ) /. (1000 : ℝ))) * x)) - ((((000101 : ℝ) /. (100000 : ℝ))) * (x ^ (2 : ℕ))))))))
  (h7 : (P (4 : ℝ)) = (((1564 : ℝ) /. (1000 : ℝ))))
  (h8 : (P (9 : ℝ)) = (((2463 : ℝ) /. (1000 : ℝ))))
  (h9 : (P (16 : ℝ)) = (((3637 : ℝ) /. (1000 : ℝ))))
  : (P (36 : ℝ)) = (((6447 : ℝ) /. (1000 : ℝ))) := by
  sorry

theorem proof_gap_exercise_3123_7
  (y : (ℝ -> ℝ))
  (P : (ℝ -> ℝ))
  (h1 : (y (1 : ℝ)) = 1)
  (h2 : (y (25 : ℝ)) = 5)
  (h3 : (y (100 : ℝ)) = 10)
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (1 ≤ x)) ∧ (x ≤ 100)) → ((y x) = (Real.rpow x (((2 : ℝ))⁻¹))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((P x) = ((((((x - 25) * (x - 100)) /. ((-(24 : ℝ)) * (-(99 : ℝ)))) * 1) + ((((x - 1) * (x - 100)) /. (24 * (-(75 : ℝ)))) * 5)) + ((((x - 1) * (x - 25)) /. (99 * 75)) * 10))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((P x) = (((((0808 : ℝ) /. (1000 : ℝ))) + ((((0193 : ℝ) /. (1000 : ℝ))) * x)) - ((((000101 : ℝ) /. (100000 : ℝ))) * (x ^ (2 : ℕ))))))))
  (h7 : (P (4 : ℝ)) = (((1564 : ℝ) /. (1000 : ℝ))))
  (h8 : (P (9 : ℝ)) = (((2463 : ℝ) /. (1000 : ℝ))))
  (h9 : (P (16 : ℝ)) = (((3637 : ℝ) /. (1000 : ℝ))))
  (h10 : (P (36 : ℝ)) = (((6447 : ℝ) /. (1000 : ℝ))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (1 ≤ x)) ∧ (x ≤ 100)) → (|((y x) - (P x))| ≤ |(((y x) - (P x)))|))) := by
  sorry

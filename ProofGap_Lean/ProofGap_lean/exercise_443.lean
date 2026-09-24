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

-- exercise: exercise_443

theorem proof_gap_exercise_443_1
  : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))) := by
  sorry

theorem proof_gap_exercise_443_2
  (h1 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((9 + (2 * x)) ≥ 0))) := by
  sorry

theorem proof_gap_exercise_443_3
  (h1 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((9 + (2 * x)) ≥ 0))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (x ≠ 8))) := by
  sorry

theorem proof_gap_exercise_443_4
  (h1 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((9 + (2 * x)) ≥ 0))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (x ≠ 8))))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => (((((Real.rpow (9 + (2 * x)) (((2 : ℝ))⁻¹)) - 5) * ((Real.rpow (9 + (2 * x)) (((2 : ℝ))⁻¹)) + 5)) * (((Real.rpow (x ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow x (((3 : ℝ))⁻¹)))) + 4)) /. ((((Real.rpow x (((3 : ℝ))⁻¹)) - 2) * (((Real.rpow (x ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow x (((3 : ℝ))⁻¹)))) + 4)) * ((Real.rpow (9 + (2 * x)) (((2 : ℝ))⁻¹)) + 5)))) (𝓝[≠] 8) (𝓝 L) ∧ (Tendsto (fun x : ℝ => (((Real.rpow (9 + (2 * x)) (((2 : ℝ))⁻¹)) - 5) /. ((Real.rpow x (((3 : ℝ))⁻¹)) - 2))) (𝓝[≠] 8) (𝓝 ((𝓝[≠] 8).limUnder (fun x : ℝ => (((((Real.rpow (9 + (2 * x)) (((2 : ℝ))⁻¹)) - 5) * ((Real.rpow (9 + (2 * x)) (((2 : ℝ))⁻¹)) + 5)) * (((Real.rpow (x ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow x (((3 : ℝ))⁻¹)))) + 4)) /. ((((Real.rpow x (((3 : ℝ))⁻¹)) - 2) * (((Real.rpow (x ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow x (((3 : ℝ))⁻¹)))) + 4)) * ((Real.rpow (9 + (2 * x)) (((2 : ℝ))⁻¹)) + 5)))))))) := by
  sorry

theorem proof_gap_exercise_443_5
  (h1 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ (-(9 /. 2)))) → ((9 + (2 * x)) ≥ 0))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 8)) → (x ≠ 8))))
  (h4 : Tendsto (fun x : ℝ => (((Real.rpow (9 + (2 * x)) (((2 : ℝ))⁻¹)) - 5) /. ((Real.rpow x (((3 : ℝ))⁻¹)) - 2))) (𝓝[≠] 8) (𝓝 ((𝓝[≠] 8).limUnder (fun x : ℝ => (((((Real.rpow (9 + (2 * x)) (((2 : ℝ))⁻¹)) - 5) * ((Real.rpow (9 + (2 * x)) (((2 : ℝ))⁻¹)) + 5)) * (((Real.rpow (x ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow x (((3 : ℝ))⁻¹)))) + 4)) /. ((((Real.rpow x (((3 : ℝ))⁻¹)) - 2) * (((Real.rpow (x ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow x (((3 : ℝ))⁻¹)))) + 4)) * ((Real.rpow (9 + (2 * x)) (((2 : ℝ))⁻¹)) + 5)))))))
  (h5 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((((Real.rpow (9 + (2 * x)) (((2 : ℝ))⁻¹)) - 5) * ((Real.rpow (9 + (2 * x)) (((2 : ℝ))⁻¹)) + 5)) * (((Real.rpow (x ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow x (((3 : ℝ))⁻¹)))) + 4)) /. ((((Real.rpow x (((3 : ℝ))⁻¹)) - 2) * (((Real.rpow (x ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow x (((3 : ℝ))⁻¹)))) + 4)) * ((Real.rpow (9 + (2 * x)) (((2 : ℝ))⁻¹)) + 5)))) (𝓝[≠] 8) (𝓝 L))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => ((((Real.rpow (x ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow x (((3 : ℝ))⁻¹)))) + 4) /. ((Real.rpow (9 + (2 * x)) (((2 : ℝ))⁻¹)) + 5))) (𝓝[≠] 8) (𝓝 L) ∧ (Tendsto (fun x : ℝ => (((Real.rpow (9 + (2 * x)) (((2 : ℝ))⁻¹)) - 5) /. ((Real.rpow x (((3 : ℝ))⁻¹)) - 2))) (𝓝[≠] 8) (𝓝 (2 * (𝓝[≠] 8).limUnder (fun x : ℝ => ((((Real.rpow (x ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow x (((3 : ℝ))⁻¹)))) + 4) /. ((Real.rpow (9 + (2 * x)) (((2 : ℝ))⁻¹)) + 5))))))) := by
  sorry

theorem proof_gap_exercise_443_6
  (h1 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ (-(9 /. 2)))) → ((9 + (2 * x)) ≥ 0))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 8)) → (x ≠ 8))))
  (h4 : Tendsto (fun x : ℝ => (((Real.rpow (9 + (2 * x)) (((2 : ℝ))⁻¹)) - 5) /. ((Real.rpow x (((3 : ℝ))⁻¹)) - 2))) (𝓝[≠] 8) (𝓝 ((𝓝[≠] 8).limUnder (fun x : ℝ => (((((Real.rpow (9 + (2 * x)) (((2 : ℝ))⁻¹)) - 5) * ((Real.rpow (9 + (2 * x)) (((2 : ℝ))⁻¹)) + 5)) * (((Real.rpow (x ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow x (((3 : ℝ))⁻¹)))) + 4)) /. ((((Real.rpow x (((3 : ℝ))⁻¹)) - 2) * (((Real.rpow (x ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow x (((3 : ℝ))⁻¹)))) + 4)) * ((Real.rpow (9 + (2 * x)) (((2 : ℝ))⁻¹)) + 5)))))))
  (h5 : Tendsto (fun x : ℝ => (((Real.rpow (9 + (2 * x)) (((2 : ℝ))⁻¹)) - 5) /. ((Real.rpow x (((3 : ℝ))⁻¹)) - 2))) (𝓝[≠] 8) (𝓝 (2 * (𝓝[≠] 8).limUnder (fun x : ℝ => ((((Real.rpow (x ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow x (((3 : ℝ))⁻¹)))) + 4) /. ((Real.rpow (9 + (2 * x)) (((2 : ℝ))⁻¹)) + 5))))))
  (h6 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((((Real.rpow (9 + (2 * x)) (((2 : ℝ))⁻¹)) - 5) * ((Real.rpow (9 + (2 * x)) (((2 : ℝ))⁻¹)) + 5)) * (((Real.rpow (x ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow x (((3 : ℝ))⁻¹)))) + 4)) /. ((((Real.rpow x (((3 : ℝ))⁻¹)) - 2) * (((Real.rpow (x ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow x (((3 : ℝ))⁻¹)))) + 4)) * ((Real.rpow (9 + (2 * x)) (((2 : ℝ))⁻¹)) + 5)))) (𝓝[≠] 8) (𝓝 L))
  (h7 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((((Real.rpow (x ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow x (((3 : ℝ))⁻¹)))) + 4) /. ((Real.rpow (9 + (2 * x)) (((2 : ℝ))⁻¹)) + 5))) (𝓝[≠] 8) (𝓝 L))
  : Tendsto (fun x : ℝ => (((Real.rpow (9 + (2 * x)) (((2 : ℝ))⁻¹)) - 5) /. ((Real.rpow x (((3 : ℝ))⁻¹)) - 2))) (𝓝[≠] 8) (𝓝 (12 /. 5)) := by
  sorry

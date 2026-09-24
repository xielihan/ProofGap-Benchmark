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

-- exercise: exercise_466

theorem proof_gap_exercise_466_1
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))) := by
  sorry

theorem proof_gap_exercise_466_2
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h3 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 1)) → (x ≠ 0))) := by
  sorry

theorem proof_gap_exercise_466_3
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h3 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 1)) → (x ≠ 0))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 1)) → (((x ^ (2 : ℕ)) - 1) ≥ 0))) := by
  sorry

theorem proof_gap_exercise_466_4
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h3 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 1)) → (x ≠ 0))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 1)) → (((x ^ (2 : ℕ)) - 1) ≥ 0))))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => (((1 - (Real.rpow (1 - (1 /. (x ^ (2 : ℕ)))) (((2 : ℝ))⁻¹))) ^ n) + ((1 + (Real.rpow (1 - (1 /. (x ^ (2 : ℕ)))) (((2 : ℝ))⁻¹))) ^ n))) atTop (𝓝 L) ∧ (Tendsto (fun x : ℝ => ((((x - (Real.rpow ((x ^ (2 : ℕ)) - 1) (((2 : ℝ))⁻¹))) ^ n) + ((x + (Real.rpow ((x ^ (2 : ℕ)) - 1) (((2 : ℝ))⁻¹))) ^ n)) /. (x ^ n))) atTop (𝓝 (atTop.limUnder (fun x : ℝ => (((1 - (Real.rpow (1 - (1 /. (x ^ (2 : ℕ)))) (((2 : ℝ))⁻¹))) ^ n) + ((1 + (Real.rpow (1 - (1 /. (x ^ (2 : ℕ)))) (((2 : ℝ))⁻¹))) ^ n))))))) := by
  sorry

theorem proof_gap_exercise_466_5
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h3 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 1)) → (x ≠ 0))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 1)) → (((x ^ (2 : ℕ)) - 1) ≥ 0))))
  (h6 : Tendsto (fun x : ℝ => ((((x - (Real.rpow ((x ^ (2 : ℕ)) - 1) (((2 : ℝ))⁻¹))) ^ n) + ((x + (Real.rpow ((x ^ (2 : ℕ)) - 1) (((2 : ℝ))⁻¹))) ^ n)) /. (x ^ n))) atTop (𝓝 (atTop.limUnder (fun x : ℝ => (((1 - (Real.rpow (1 - (1 /. (x ^ (2 : ℕ)))) (((2 : ℝ))⁻¹))) ^ n) + ((1 + (Real.rpow (1 - (1 /. (x ^ (2 : ℕ)))) (((2 : ℝ))⁻¹))) ^ n))))))
  (h7 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((1 - (Real.rpow (1 - (1 /. (x ^ (2 : ℕ)))) (((2 : ℝ))⁻¹))) ^ n) + ((1 + (Real.rpow (1 - (1 /. (x ^ (2 : ℕ)))) (((2 : ℝ))⁻¹))) ^ n))) atTop (𝓝 L))
  : Tendsto (fun x : ℝ => (((1 - (Real.rpow (1 - (1 /. (x ^ (2 : ℕ)))) (((2 : ℝ))⁻¹))) ^ n) + ((1 + (Real.rpow (1 - (1 /. (x ^ (2 : ℕ)))) (((2 : ℝ))⁻¹))) ^ n))) atTop (𝓝 ((2 : ℕ) ^ n)) := by
  sorry

theorem proof_gap_exercise_466_6
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h3 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 1)) → (x ≠ 0))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 1)) → (((x ^ (2 : ℕ)) - 1) ≥ 0))))
  (h6 : Tendsto (fun x : ℝ => ((((x - (Real.rpow ((x ^ (2 : ℕ)) - 1) (((2 : ℝ))⁻¹))) ^ n) + ((x + (Real.rpow ((x ^ (2 : ℕ)) - 1) (((2 : ℝ))⁻¹))) ^ n)) /. (x ^ n))) atTop (𝓝 (atTop.limUnder (fun x : ℝ => (((1 - (Real.rpow (1 - (1 /. (x ^ (2 : ℕ)))) (((2 : ℝ))⁻¹))) ^ n) + ((1 + (Real.rpow (1 - (1 /. (x ^ (2 : ℕ)))) (((2 : ℝ))⁻¹))) ^ n))))))
  (h7 : Tendsto (fun x : ℝ => (((1 - (Real.rpow (1 - (1 /. (x ^ (2 : ℕ)))) (((2 : ℝ))⁻¹))) ^ n) + ((1 + (Real.rpow (1 - (1 /. (x ^ (2 : ℕ)))) (((2 : ℝ))⁻¹))) ^ n))) atTop (𝓝 ((2 : ℕ) ^ n)))
  (h8 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((1 - (Real.rpow (1 - (1 /. (x ^ (2 : ℕ)))) (((2 : ℝ))⁻¹))) ^ n) + ((1 + (Real.rpow (1 - (1 /. (x ^ (2 : ℕ)))) (((2 : ℝ))⁻¹))) ^ n))) atTop (𝓝 L))
  : Tendsto (fun x : ℝ => ((((x - (Real.rpow ((x ^ (2 : ℕ)) - 1) (((2 : ℝ))⁻¹))) ^ n) + ((x + (Real.rpow ((x ^ (2 : ℕ)) - 1) (((2 : ℝ))⁻¹))) ^ n)) /. (x ^ n))) atTop (𝓝 ((2 : ℕ) ^ n)) := by
  sorry

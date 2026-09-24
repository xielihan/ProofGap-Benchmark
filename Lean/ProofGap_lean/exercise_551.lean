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

-- exercise: exercise_551

theorem proof_gap_exercise_551_1
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  : (forall (x : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) ∧ ((x + a) > 0)) ∧ ((x + b) > 0)) ∧ (((x + a) + b) > 0)) → ((((Real.rpow (x + a) (x + a)) * (Real.rpow (x + b) (x + b))) /. (Real.rpow ((x + a) + b) (((2 * x) + a) + b))) = (((Real.rpow (1 + (a /. x)) (x + a)) * (Real.rpow (1 + (b /. x)) (x + b))) /. (Real.rpow (1 + ((a + b) /. x)) (((2 * x) + a) + b)))))) := by
  sorry

theorem proof_gap_exercise_551_2
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) ∧ ((x + a) > 0)) ∧ ((x + b) > 0)) ∧ (((x + a) + b) > 0)) → ((((Real.rpow (x + a) (x + a)) * (Real.rpow (x + b) (x + b))) /. (Real.rpow ((x + a) + b) (((2 * x) + a) + b))) = (((Real.rpow (1 + (a /. x)) (x + a)) * (Real.rpow (1 + (b /. x)) (x + b))) /. (Real.rpow (1 + ((a + b) /. x)) (((2 * x) + a) + b)))))))
  : (forall (x : ℝ), (((((((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) ∧ ((x + a) > 0)) ∧ ((x + b) > 0)) ∧ (((x + a) + b) > 0)) ∧ (a ≠ 0)) ∧ (b ≠ 0)) ∧ ((a + b) ≠ 0)) → (Tendsto (fun x_1 : ℝ => (((Real.rpow (1 + (a /. x_1)) (x_1 + a)) * (Real.rpow (1 + (b /. x_1)) (x_1 + b))) /. (Real.rpow (1 + ((a + b) /. x_1)) (((2 * x_1) + a) + b)))) atTop (𝓝 (((Real.exp a) * (Real.exp b)) /. (Real.exp (2 * (a + b)))))))) := by
  sorry

theorem proof_gap_exercise_551_3
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) ∧ ((x + a) > 0)) ∧ ((x + b) > 0)) ∧ (((x + a) + b) > 0)) → ((((Real.rpow (x + a) (x + a)) * (Real.rpow (x + b) (x + b))) /. (Real.rpow ((x + a) + b) (((2 * x) + a) + b))) = (((Real.rpow (1 + (a /. x)) (x + a)) * (Real.rpow (1 + (b /. x)) (x + b))) /. (Real.rpow (1 + ((a + b) /. x)) (((2 * x) + a) + b)))))))
  (h4 : (forall (x : ℝ), (((((((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) ∧ ((x + a) > 0)) ∧ ((x + b) > 0)) ∧ (((x + a) + b) > 0)) ∧ (a ≠ 0)) ∧ (b ≠ 0)) ∧ ((a + b) ≠ 0)) → (Tendsto (fun x_1 : ℝ => (((Real.rpow (1 + (a /. x_1)) (x_1 + a)) * (Real.rpow (1 + (b /. x_1)) (x_1 + b))) /. (Real.rpow (1 + ((a + b) /. x_1)) (((2 * x_1) + a) + b)))) atTop (𝓝 (((Real.exp a) * (Real.exp b)) /. (Real.exp (2 * (a + b)))))))))
  : Tendsto (fun x : ℝ => (((Real.rpow (x + a) (x + a)) * (Real.rpow (x + b) (x + b))) /. (Real.rpow ((x + a) + b) (((2 * x) + a) + b)))) atTop (𝓝 (((Real.exp a) * (Real.exp b)) /. (Real.exp (2 * (a + b))))) := by
  sorry

theorem proof_gap_exercise_551_4
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) ∧ ((x + a) > 0)) ∧ ((x + b) > 0)) ∧ (((x + a) + b) > 0)) → ((((Real.rpow (x + a) (x + a)) * (Real.rpow (x + b) (x + b))) /. (Real.rpow ((x + a) + b) (((2 * x) + a) + b))) = (((Real.rpow (1 + (a /. x)) (x + a)) * (Real.rpow (1 + (b /. x)) (x + b))) /. (Real.rpow (1 + ((a + b) /. x)) (((2 * x) + a) + b)))))))
  (h4 : (forall (x : ℝ), (((((((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) ∧ ((x + a) > 0)) ∧ ((x + b) > 0)) ∧ (((x + a) + b) > 0)) ∧ (a ≠ 0)) ∧ (b ≠ 0)) ∧ ((a + b) ≠ 0)) → (Tendsto (fun x_1 : ℝ => (((Real.rpow (1 + (a /. x_1)) (x_1 + a)) * (Real.rpow (1 + (b /. x_1)) (x_1 + b))) /. (Real.rpow (1 + ((a + b) /. x_1)) (((2 * x_1) + a) + b)))) atTop (𝓝 (((Real.exp a) * (Real.exp b)) /. (Real.exp (2 * (a + b)))))))))
  (h5 : Tendsto (fun x : ℝ => (((Real.rpow (x + a) (x + a)) * (Real.rpow (x + b) (x + b))) /. (Real.rpow ((x + a) + b) (((2 * x) + a) + b)))) atTop (𝓝 (((Real.exp a) * (Real.exp b)) /. (Real.exp (2 * (a + b))))))
  : (((Real.exp a) * (Real.exp b)) /. (Real.exp (2 * (a + b)))) = (Real.exp (-(a + b))) := by
  sorry

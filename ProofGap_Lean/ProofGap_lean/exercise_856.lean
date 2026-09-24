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

-- exercise: exercise_856

theorem proof_gap_exercise_856_1
  (y : (ℝ -> ℝ))
  (m : ℕ)
  (n : ℕ)
  (h1 : (m ∈ (Set.univ : Set ℕ)) ∧ (m ∈ ({n_1 : ℕ | 0 < n_1})))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1})))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((y x) = (Real.rpow (((1 - x) ^ m) * ((1 + x) ^ n)) (((m + n))⁻¹))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → (((iteratedDeriv 1 (fun t => y t) x) = (((((-(m : ℝ)) * ((1 - x) ^ (m - 1))) * ((1 + x) ^ n)) + ((n * ((1 + x) ^ (n - 1))) * ((1 - x) ^ m))) /. ((m + n) * (Real.rpow ((((1 - x) ^ m) * ((1 + x) ^ n)) ^ ((m + n) - 1)) (((m + n))⁻¹))))) ∧ ((((((-(m : ℝ)) * ((1 - x) ^ (m - 1))) * ((1 + x) ^ n)) + ((n * ((1 + x) ^ (n - 1))) * ((1 - x) ^ m))) /. ((m + n) * (Real.rpow ((((1 - x) ^ m) * ((1 + x) ^ n)) ^ ((m + n) - 1)) (((m + n))⁻¹)))) = (((n - m) - ((n + m) * x)) /. ((m + n) * (Real.rpow (((1 - x) ^ m) * ((1 + x) ^ n)) (((m + n))⁻¹)))))))) := by
  sorry

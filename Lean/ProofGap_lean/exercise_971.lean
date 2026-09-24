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

-- exercise: exercise_971

theorem proof_gap_exercise_971_1
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : 0 ≤ |(b)|)
  (h4 : |(b)| < a)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (((b /. a) * x) + (((2 * (Real.rpow ((a ^ (2 : ℕ)) - (b ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. a) * (Real.arctan ((Real.rpow ((a - b) /. (a + b)) (((2 : ℝ))⁻¹)) * (Real.tanh (x /. 2))))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = ((b /. a) + (((((2 * (Real.rpow ((a ^ (2 : ℕ)) - (b ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. a) * (1 /. (1 + (((a - b) /. (a + b)) * ((Real.tanh (x /. 2)) ^ (2 : ℕ)))))) * (Real.rpow ((a - b) /. (a + b)) (((2 : ℝ))⁻¹))) * (1 /. (2 * ((Real.cosh (x /. 2)) ^ (2 : ℕ))))))))) := by
  sorry

theorem proof_gap_exercise_971_2
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : 0 ≤ |(b)|)
  (h4 : |(b)| < a)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (((b /. a) * x) + (((2 * (Real.rpow ((a ^ (2 : ℕ)) - (b ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. a) * (Real.arctan ((Real.rpow ((a - b) /. (a + b)) (((2 : ℝ))⁻¹)) * (Real.tanh (x /. 2))))))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = ((b /. a) + (((((2 * (Real.rpow ((a ^ (2 : ℕ)) - (b ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. a) * (1 /. (1 + (((a - b) /. (a + b)) * ((Real.tanh (x /. 2)) ^ (2 : ℕ)))))) * (Real.rpow ((a - b) /. (a + b)) (((2 : ℝ))⁻¹))) * (1 /. (2 * ((Real.cosh (x /. 2)) ^ (2 : ℕ))))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((b /. a) + (((((2 * (Real.rpow ((a ^ (2 : ℕ)) - (b ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. a) * (1 /. (1 + (((a - b) /. (a + b)) * ((Real.tanh (x /. 2)) ^ (2 : ℕ)))))) * (Real.rpow ((a - b) /. (a + b)) (((2 : ℝ))⁻¹))) * (1 /. (2 * ((Real.cosh (x /. 2)) ^ (2 : ℕ)))))) = ((b /. a) + (((a ^ (2 : ℕ)) - (b ^ (2 : ℕ))) /. (a * (b + (a * (Real.cosh x))))))))) := by
  sorry

theorem proof_gap_exercise_971_3
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : 0 ≤ |(b)|)
  (h4 : |(b)| < a)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (((b /. a) * x) + (((2 * (Real.rpow ((a ^ (2 : ℕ)) - (b ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. a) * (Real.arctan ((Real.rpow ((a - b) /. (a + b)) (((2 : ℝ))⁻¹)) * (Real.tanh (x /. 2))))))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = ((b /. a) + (((((2 * (Real.rpow ((a ^ (2 : ℕ)) - (b ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. a) * (1 /. (1 + (((a - b) /. (a + b)) * ((Real.tanh (x /. 2)) ^ (2 : ℕ)))))) * (Real.rpow ((a - b) /. (a + b)) (((2 : ℝ))⁻¹))) * (1 /. (2 * ((Real.cosh (x /. 2)) ^ (2 : ℕ))))))))))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((b /. a) + (((((2 * (Real.rpow ((a ^ (2 : ℕ)) - (b ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. a) * (1 /. (1 + (((a - b) /. (a + b)) * ((Real.tanh (x /. 2)) ^ (2 : ℕ)))))) * (Real.rpow ((a - b) /. (a + b)) (((2 : ℝ))⁻¹))) * (1 /. (2 * ((Real.cosh (x /. 2)) ^ (2 : ℕ)))))) = ((b /. a) + (((a ^ (2 : ℕ)) - (b ^ (2 : ℕ))) /. (a * (b + (a * (Real.cosh x))))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((b /. a) + (((a ^ (2 : ℕ)) - (b ^ (2 : ℕ))) /. (a * (b + (a * (Real.cosh x)))))) = ((a + (b * (Real.cosh x))) /. (b + (a * (Real.cosh x))))))) := by
  sorry

theorem proof_gap_exercise_971_4
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : 0 ≤ |(b)|)
  (h4 : |(b)| < a)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (((b /. a) * x) + (((2 * (Real.rpow ((a ^ (2 : ℕ)) - (b ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. a) * (Real.arctan ((Real.rpow ((a - b) /. (a + b)) (((2 : ℝ))⁻¹)) * (Real.tanh (x /. 2))))))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = ((b /. a) + (((((2 * (Real.rpow ((a ^ (2 : ℕ)) - (b ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. a) * (1 /. (1 + (((a - b) /. (a + b)) * ((Real.tanh (x /. 2)) ^ (2 : ℕ)))))) * (Real.rpow ((a - b) /. (a + b)) (((2 : ℝ))⁻¹))) * (1 /. (2 * ((Real.cosh (x /. 2)) ^ (2 : ℕ))))))))))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((b /. a) + (((((2 * (Real.rpow ((a ^ (2 : ℕ)) - (b ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. a) * (1 /. (1 + (((a - b) /. (a + b)) * ((Real.tanh (x /. 2)) ^ (2 : ℕ)))))) * (Real.rpow ((a - b) /. (a + b)) (((2 : ℝ))⁻¹))) * (1 /. (2 * ((Real.cosh (x /. 2)) ^ (2 : ℕ)))))) = ((b /. a) + (((a ^ (2 : ℕ)) - (b ^ (2 : ℕ))) /. (a * (b + (a * (Real.cosh x))))))))))
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((b /. a) + (((a ^ (2 : ℕ)) - (b ^ (2 : ℕ))) /. (a * (b + (a * (Real.cosh x)))))) = ((a + (b * (Real.cosh x))) /. (b + (a * (Real.cosh x))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = ((a + (b * (Real.cosh x))) /. (b + (a * (Real.cosh x))))))) := by
  sorry

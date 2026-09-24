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

-- exercise: exercise_882

theorem proof_gap_exercise_882_1
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : ((a ^ (2 : ℕ)) + (b ^ (2 : ℕ))) > 0)
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((Real.exp (a * x)) * (((a * (Real.sin (b * x))) - (b * (Real.cos (b * x)))) /. (Real.rpow ((a ^ (2 : ℕ)) + (b ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (((1 /. (Real.rpow ((a ^ (2 : ℕ)) + (b ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (Real.exp (a * x))) * (((a * ((a * (Real.sin (b * x))) - (b * (Real.cos (b * x))))) + ((a * b) * (Real.cos (b * x)))) + ((b ^ (2 : ℕ)) * (Real.sin (b * x)))))))) := by
  sorry

theorem proof_gap_exercise_882_2
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : ((a ^ (2 : ℕ)) + (b ^ (2 : ℕ))) > 0)
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((Real.exp (a * x)) * (((a * (Real.sin (b * x))) - (b * (Real.cos (b * x)))) /. (Real.rpow ((a ^ (2 : ℕ)) + (b ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (((1 /. (Real.rpow ((a ^ (2 : ℕ)) + (b ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (Real.exp (a * x))) * (((a * ((a * (Real.sin (b * x))) - (b * (Real.cos (b * x))))) + ((a * b) * (Real.cos (b * x)))) + ((b ^ (2 : ℕ)) * (Real.sin (b * x)))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((1 /. (Real.rpow ((a ^ (2 : ℕ)) + (b ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (Real.exp (a * x))) * (((a * ((a * (Real.sin (b * x))) - (b * (Real.cos (b * x))))) + ((a * b) * (Real.cos (b * x)))) + ((b ^ (2 : ℕ)) * (Real.sin (b * x))))) = (((Real.rpow ((a ^ (2 : ℕ)) + (b ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) * (Real.exp (a * x))) * (Real.sin (b * x)))))) := by
  sorry

theorem proof_gap_exercise_882_3
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : ((a ^ (2 : ℕ)) + (b ^ (2 : ℕ))) > 0)
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((Real.exp (a * x)) * (((a * (Real.sin (b * x))) - (b * (Real.cos (b * x)))) /. (Real.rpow ((a ^ (2 : ℕ)) + (b ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (((1 /. (Real.rpow ((a ^ (2 : ℕ)) + (b ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (Real.exp (a * x))) * (((a * ((a * (Real.sin (b * x))) - (b * (Real.cos (b * x))))) + ((a * b) * (Real.cos (b * x)))) + ((b ^ (2 : ℕ)) * (Real.sin (b * x)))))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((1 /. (Real.rpow ((a ^ (2 : ℕ)) + (b ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (Real.exp (a * x))) * (((a * ((a * (Real.sin (b * x))) - (b * (Real.cos (b * x))))) + ((a * b) * (Real.cos (b * x)))) + ((b ^ (2 : ℕ)) * (Real.sin (b * x))))) = (((Real.rpow ((a ^ (2 : ℕ)) + (b ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) * (Real.exp (a * x))) * (Real.sin (b * x)))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (((Real.rpow ((a ^ (2 : ℕ)) + (b ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) * (Real.exp (a * x))) * (Real.sin (b * x)))))) := by
  sorry

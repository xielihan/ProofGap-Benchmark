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

-- exercise: exercise_953

theorem proof_gap_exercise_953_1
  (y : (ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((1 - ((Real.cos v_uCE_uB1) * (Real.cos x))) ≠ 0)) → ((y x) = (Real.arcsin (((Real.sin v_uCE_uB1) * (Real.sin x)) /. (1 - ((Real.cos v_uCE_uB1) * (Real.cos x)))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = ((1 /. (Real.rpow (1 - ((((Real.sin v_uCE_uB1) * (Real.sin x)) /. (1 - ((Real.cos v_uCE_uB1) * (Real.cos x)))) ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (((((Real.sin v_uCE_uB1) * (Real.cos x)) * (1 - ((Real.cos v_uCE_uB1) * (Real.cos x)))) - (((Real.sin v_uCE_uB1) * (Real.cos v_uCE_uB1)) * ((Real.sin x) ^ (2 : ℕ)))) /. ((1 - ((Real.cos v_uCE_uB1) * (Real.cos x))) ^ (2 : ℕ))))))) := by
  sorry

theorem proof_gap_exercise_953_2
  (y : (ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((1 - ((Real.cos v_uCE_uB1) * (Real.cos x))) ≠ 0)) → ((y x) = (Real.arcsin (((Real.sin v_uCE_uB1) * (Real.sin x)) /. (1 - ((Real.cos v_uCE_uB1) * (Real.cos x)))))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = ((1 /. (Real.rpow (1 - ((((Real.sin v_uCE_uB1) * (Real.sin x)) /. (1 - ((Real.cos v_uCE_uB1) * (Real.cos x)))) ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (((((Real.sin v_uCE_uB1) * (Real.cos x)) * (1 - ((Real.cos v_uCE_uB1) * (Real.cos x)))) - (((Real.sin v_uCE_uB1) * (Real.cos v_uCE_uB1)) * ((Real.sin x) ^ (2 : ℕ)))) /. ((1 - ((Real.cos v_uCE_uB1) * (Real.cos x))) ^ (2 : ℕ))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (((1 - ((Real.cos v_uCE_uB1) * (Real.cos x))) /. (Real.rpow (((Real.cos x) - (Real.cos v_uCE_uB1)) ^ (2 : ℕ)) (((2 : ℝ))⁻¹))) * (((Real.sin v_uCE_uB1) * ((Real.cos x) - (Real.cos v_uCE_uB1))) /. ((1 - ((Real.cos v_uCE_uB1) * (Real.cos x))) ^ (2 : ℕ))))))) := by
  sorry

theorem proof_gap_exercise_953_3
  (y : (ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((1 - ((Real.cos v_uCE_uB1) * (Real.cos x))) ≠ 0)) → ((y x) = (Real.arcsin (((Real.sin v_uCE_uB1) * (Real.sin x)) /. (1 - ((Real.cos v_uCE_uB1) * (Real.cos x)))))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = ((1 /. (Real.rpow (1 - ((((Real.sin v_uCE_uB1) * (Real.sin x)) /. (1 - ((Real.cos v_uCE_uB1) * (Real.cos x)))) ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (((((Real.sin v_uCE_uB1) * (Real.cos x)) * (1 - ((Real.cos v_uCE_uB1) * (Real.cos x)))) - (((Real.sin v_uCE_uB1) * (Real.cos v_uCE_uB1)) * ((Real.sin x) ^ (2 : ℕ)))) /. ((1 - ((Real.cos v_uCE_uB1) * (Real.cos x))) ^ (2 : ℕ))))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (((1 - ((Real.cos v_uCE_uB1) * (Real.cos x))) /. (Real.rpow (((Real.cos x) - (Real.cos v_uCE_uB1)) ^ (2 : ℕ)) (((2 : ℝ))⁻¹))) * (((Real.sin v_uCE_uB1) * ((Real.cos x) - (Real.cos v_uCE_uB1))) /. ((1 - ((Real.cos v_uCE_uB1) * (Real.cos x))) ^ (2 : ℕ))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (((Real.sin v_uCE_uB1) * (SignType.sign ((Real.cos x) - (Real.cos v_uCE_uB1)) : ℝ)) /. (1 - ((Real.cos v_uCE_uB1) * (Real.cos x))))))) := by
  sorry

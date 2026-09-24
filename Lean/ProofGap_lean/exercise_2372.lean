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

-- exercise: exercise_2372

theorem proof_gap_exercise_2372_1
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < (1 /. 2))) → (((1 - (x ^ (2 : ℕ))) ≠ 0) ∧ ((Real.log x) ∈ (Set.univ : Set ℝ))))) := by
  sorry

theorem proof_gap_exercise_2372_2
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < (1 /. 2))) → (((1 - (x ^ (2 : ℕ))) ≠ 0) ∧ ((Real.log x) ∈ (Set.univ : Set ℝ))))))
  : Tendsto (fun x : ℝ => ((Real.rpow x (((2 : ℝ))⁻¹)) * ((Real.log x) /. (1 - (x ^ (2 : ℕ)))))) (𝓝[>] 0) (𝓝 0) := by
  sorry

theorem proof_gap_exercise_2372_3
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < (1 /. 2))) → (((1 - (x ^ (2 : ℕ))) ≠ 0) ∧ ((Real.log x) ∈ (Set.univ : Set ℝ))))))
  (h2 : Tendsto (fun x : ℝ => ((Real.rpow x (((2 : ℝ))⁻¹)) * ((Real.log x) /. (1 - (x ^ (2 : ℕ)))))) (𝓝[>] 0) (𝓝 0))
  : (exists (I_1 : ℝ), ((I_1 ∈ (Set.univ : Set ℝ)) ∧ ((∫ x in (0 : ℝ)..(1 /. 2), (((Real.log x) /. ((1 : ℝ) - (x ^ (2 : ℕ)))) * (1 : ℝ))) = I_1))) := by
  sorry

theorem proof_gap_exercise_2372_4
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < (1 /. 2))) → (((1 - (x ^ (2 : ℕ))) ≠ 0) ∧ ((Real.log x) ∈ (Set.univ : Set ℝ))))))
  (h2 : Tendsto (fun x : ℝ => ((Real.rpow x (((2 : ℝ))⁻¹)) * ((Real.log x) /. (1 - (x ^ (2 : ℕ)))))) (𝓝[>] 0) (𝓝 0))
  (h3 : (exists (I_1 : ℝ), ((I_1 ∈ (Set.univ : Set ℝ)) ∧ ((∫ x in (0 : ℝ)..(1 /. 2), (((Real.log x) /. ((1 : ℝ) - (x ^ (2 : ℕ)))) * (1 : ℝ))) = I_1))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((1 /. 2) < x)) ∧ (x < 1)) → (((1 - (x ^ (2 : ℕ))) ≠ 0) ∧ ((Real.log x) ∈ (Set.univ : Set ℝ))))) := by
  sorry

theorem proof_gap_exercise_2372_5
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < (1 /. 2))) → (((1 - (x ^ (2 : ℕ))) ≠ 0) ∧ ((Real.log x) ∈ (Set.univ : Set ℝ))))))
  (h2 : Tendsto (fun x : ℝ => ((Real.rpow x (((2 : ℝ))⁻¹)) * ((Real.log x) /. (1 - (x ^ (2 : ℕ)))))) (𝓝[>] 0) (𝓝 0))
  (h3 : (exists (I_1 : ℝ), ((I_1 ∈ (Set.univ : Set ℝ)) ∧ ((∫ x in (0 : ℝ)..(1 /. 2), (((Real.log x) /. ((1 : ℝ) - (x ^ (2 : ℕ)))) * (1 : ℝ))) = I_1))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((1 /. 2) < x)) ∧ (x < 1)) → (((1 - (x ^ (2 : ℕ))) ≠ 0) ∧ ((Real.log x) ∈ (Set.univ : Set ℝ))))))
  : Tendsto (fun x : ℝ => ((Real.rpow (1 - x) (((2 : ℝ))⁻¹)) * ((Real.log x) /. (1 - (x ^ (2 : ℕ)))))) (𝓝[<] 1) (𝓝 0) := by
  sorry

theorem proof_gap_exercise_2372_6
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < (1 /. 2))) → (((1 - (x ^ (2 : ℕ))) ≠ 0) ∧ ((Real.log x) ∈ (Set.univ : Set ℝ))))))
  (h2 : Tendsto (fun x : ℝ => ((Real.rpow x (((2 : ℝ))⁻¹)) * ((Real.log x) /. (1 - (x ^ (2 : ℕ)))))) (𝓝[>] 0) (𝓝 0))
  (h3 : (exists (I_1 : ℝ), ((I_1 ∈ (Set.univ : Set ℝ)) ∧ ((∫ x in (0 : ℝ)..(1 /. 2), (((Real.log x) /. ((1 : ℝ) - (x ^ (2 : ℕ)))) * (1 : ℝ))) = I_1))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((1 /. 2) < x)) ∧ (x < 1)) → (((1 - (x ^ (2 : ℕ))) ≠ 0) ∧ ((Real.log x) ∈ (Set.univ : Set ℝ))))))
  (h5 : Tendsto (fun x : ℝ => ((Real.rpow (1 - x) (((2 : ℝ))⁻¹)) * ((Real.log x) /. (1 - (x ^ (2 : ℕ)))))) (𝓝[<] 1) (𝓝 0))
  : (exists (I_2 : ℝ), ((I_2 ∈ (Set.univ : Set ℝ)) ∧ ((∫ x in (1 /. 2)..(1 : ℝ), (((Real.log x) /. ((1 : ℝ) - (x ^ (2 : ℕ)))) * (1 : ℝ))) = I_2))) := by
  sorry

theorem proof_gap_exercise_2372_7
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < (1 /. 2))) → (((1 - (x ^ (2 : ℕ))) ≠ 0) ∧ ((Real.log x) ∈ (Set.univ : Set ℝ))))))
  (h2 : Tendsto (fun x : ℝ => ((Real.rpow x (((2 : ℝ))⁻¹)) * ((Real.log x) /. (1 - (x ^ (2 : ℕ)))))) (𝓝[>] 0) (𝓝 0))
  (h3 : (exists (I_1 : ℝ), ((I_1 ∈ (Set.univ : Set ℝ)) ∧ ((∫ x in (0 : ℝ)..(1 /. 2), (((Real.log x) /. ((1 : ℝ) - (x ^ (2 : ℕ)))) * (1 : ℝ))) = I_1))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((1 /. 2) < x)) ∧ (x < 1)) → (((1 - (x ^ (2 : ℕ))) ≠ 0) ∧ ((Real.log x) ∈ (Set.univ : Set ℝ))))))
  (h5 : Tendsto (fun x : ℝ => ((Real.rpow (1 - x) (((2 : ℝ))⁻¹)) * ((Real.log x) /. (1 - (x ^ (2 : ℕ)))))) (𝓝[<] 1) (𝓝 0))
  (h6 : (exists (I_2 : ℝ), ((I_2 ∈ (Set.univ : Set ℝ)) ∧ ((∫ x in (1 /. 2)..(1 : ℝ), (((Real.log x) /. ((1 : ℝ) - (x ^ (2 : ℕ)))) * (1 : ℝ))) = I_2))))
  : (exists (I : ℝ), ((I ∈ (Set.univ : Set ℝ)) ∧ ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.log x) /. ((1 : ℝ) - (x ^ (2 : ℕ)))) * (1 : ℝ))) = I))) := by
  sorry

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

-- exercise: exercise_2370

theorem proof_gap_exercise_2370_1
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  : Tendsto (fun x : ℝ => ((Real.rpow x (-n)) * ((Real.rpow x n) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))) (𝓝[>] 0) (𝓝 1) := by
  sorry

theorem proof_gap_exercise_2370_2
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : Tendsto (fun x : ℝ => ((Real.rpow x (-n)) * ((Real.rpow x n) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))) (𝓝[>] 0) (𝓝 1))
  (h3 : (n ∈ (Set.univ : Set ℝ)) ∧ (n > (-(1 : ℝ))))
  : (exists (I_1 : ℝ), ((I_1 ∈ (Set.univ : Set ℝ)) ∧ (((∫ x in (0 : ℝ)..(1 /. 2), (((Real.rpow x n) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = I_1) ↔ ((-n) < 1)))) := by
  sorry

theorem proof_gap_exercise_2370_3
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : Tendsto (fun x : ℝ => ((Real.rpow x (-n)) * ((Real.rpow x n) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))) (𝓝[>] 0) (𝓝 1))
  (h3 : (exists (I_1 : ℝ), ((I_1 ∈ (Set.univ : Set ℝ)) ∧ (((∫ x in (0 : ℝ)..(1 /. 2), (((Real.rpow x n) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = I_1) ↔ ((-n) < 1)))))
  : ((-n) < 1) ↔ (n > (-(1 : ℝ))) := by
  sorry

theorem proof_gap_exercise_2370_4
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : Tendsto (fun x : ℝ => ((Real.rpow x (-n)) * ((Real.rpow x n) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))) (𝓝[>] 0) (𝓝 1))
  (h3 : (exists (I_1 : ℝ), ((I_1 ∈ (Set.univ : Set ℝ)) ∧ (((∫ x in (0 : ℝ)..(1 /. 2), (((Real.rpow x n) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = I_1) ↔ ((-n) < 1)))))
  (h4 : ((-n) < 1) ↔ (n > (-(1 : ℝ))))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => ((Real.rpow x n) /. (Real.rpow (1 + x) (((2 : ℝ))⁻¹)))) (𝓝[<] 1) (𝓝 L) ∧ (Tendsto (fun x : ℝ => ((Real.rpow (1 - x) (((2 : ℝ))⁻¹)) * ((Real.rpow x n) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))) (𝓝[<] 1) (𝓝 ((𝓝[<] 1).limUnder (fun x : ℝ => ((Real.rpow x n) /. (Real.rpow (1 + x) (((2 : ℝ))⁻¹)))))))) := by
  sorry

theorem proof_gap_exercise_2370_5
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : Tendsto (fun x : ℝ => ((Real.rpow x (-n)) * ((Real.rpow x n) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))) (𝓝[>] 0) (𝓝 1))
  (h3 : (exists (I_1 : ℝ), ((I_1 ∈ (Set.univ : Set ℝ)) ∧ (((∫ x in (0 : ℝ)..(1 /. 2), (((Real.rpow x n) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = I_1) ↔ ((-n) < 1)))))
  (h4 : ((-n) < 1) ↔ (n > (-(1 : ℝ))))
  (h5 : Tendsto (fun x : ℝ => ((Real.rpow (1 - x) (((2 : ℝ))⁻¹)) * ((Real.rpow x n) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))) (𝓝[<] 1) (𝓝 ((𝓝[<] 1).limUnder (fun x : ℝ => ((Real.rpow x n) /. (Real.rpow (1 + x) (((2 : ℝ))⁻¹)))))))
  (h6 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((Real.rpow x n) /. (Real.rpow (1 + x) (((2 : ℝ))⁻¹)))) (𝓝[<] 1) (𝓝 L))
  : Tendsto (fun x : ℝ => ((Real.rpow x n) /. (Real.rpow (1 + x) (((2 : ℝ))⁻¹)))) (𝓝[<] 1) (𝓝 (1 /. (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)))) := by
  sorry

theorem proof_gap_exercise_2370_6
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : Tendsto (fun x : ℝ => ((Real.rpow x (-n)) * ((Real.rpow x n) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))) (𝓝[>] 0) (𝓝 1))
  (h3 : (exists (I_1 : ℝ), ((I_1 ∈ (Set.univ : Set ℝ)) ∧ (((∫ x in (0 : ℝ)..(1 /. 2), (((Real.rpow x n) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = I_1) ↔ ((-n) < 1)))))
  (h4 : ((-n) < 1) ↔ (n > (-(1 : ℝ))))
  (h5 : Tendsto (fun x : ℝ => ((Real.rpow (1 - x) (((2 : ℝ))⁻¹)) * ((Real.rpow x n) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))) (𝓝[<] 1) (𝓝 ((𝓝[<] 1).limUnder (fun x : ℝ => ((Real.rpow x n) /. (Real.rpow (1 + x) (((2 : ℝ))⁻¹)))))))
  (h6 : Tendsto (fun x : ℝ => ((Real.rpow x n) /. (Real.rpow (1 + x) (((2 : ℝ))⁻¹)))) (𝓝[<] 1) (𝓝 (1 /. (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)))))
  (h7 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((Real.rpow x n) /. (Real.rpow (1 + x) (((2 : ℝ))⁻¹)))) (𝓝[<] 1) (𝓝 L))
  : Tendsto (fun x : ℝ => ((Real.rpow (1 - x) (((2 : ℝ))⁻¹)) * ((Real.rpow x n) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))) (𝓝[<] 1) (𝓝 (1 /. (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)))) := by
  sorry

theorem proof_gap_exercise_2370_7
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : Tendsto (fun x : ℝ => ((Real.rpow x (-n)) * ((Real.rpow x n) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))) (𝓝[>] 0) (𝓝 1))
  (h3 : (exists (I_1 : ℝ), ((I_1 ∈ (Set.univ : Set ℝ)) ∧ (((∫ x in (0 : ℝ)..(1 /. 2), (((Real.rpow x n) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = I_1) ↔ ((-n) < 1)))))
  (h4 : ((-n) < 1) ↔ (n > (-(1 : ℝ))))
  (h5 : Tendsto (fun x : ℝ => ((Real.rpow (1 - x) (((2 : ℝ))⁻¹)) * ((Real.rpow x n) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))) (𝓝[<] 1) (𝓝 ((𝓝[<] 1).limUnder (fun x : ℝ => ((Real.rpow x n) /. (Real.rpow (1 + x) (((2 : ℝ))⁻¹)))))))
  (h6 : Tendsto (fun x : ℝ => ((Real.rpow x n) /. (Real.rpow (1 + x) (((2 : ℝ))⁻¹)))) (𝓝[<] 1) (𝓝 (1 /. (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)))))
  (h7 : Tendsto (fun x : ℝ => ((Real.rpow (1 - x) (((2 : ℝ))⁻¹)) * ((Real.rpow x n) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))) (𝓝[<] 1) (𝓝 (1 /. (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)))))
  (h8 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((Real.rpow x n) /. (Real.rpow (1 + x) (((2 : ℝ))⁻¹)))) (𝓝[<] 1) (𝓝 L))
  : (forall (n_1 : ℝ), ((n_1 ∈ (Set.univ : Set ℝ)) → (exists (I_2 : ℝ), ((I_2 ∈ (Set.univ : Set ℝ)) ∧ ((∫ x in (1 /. 2)..(1 : ℝ), (((Real.rpow x n_1) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = I_2))))) := by
  sorry

theorem proof_gap_exercise_2370_8
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : Tendsto (fun x : ℝ => ((Real.rpow x (-n)) * ((Real.rpow x n) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))) (𝓝[>] 0) (𝓝 1))
  (h3 : (exists (I_1 : ℝ), ((I_1 ∈ (Set.univ : Set ℝ)) ∧ (((∫ x in (0 : ℝ)..(1 /. 2), (((Real.rpow x n) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = I_1) ↔ ((-n) < 1)))))
  (h4 : ((-n) < 1) ↔ (n > (-(1 : ℝ))))
  (h5 : Tendsto (fun x : ℝ => ((Real.rpow (1 - x) (((2 : ℝ))⁻¹)) * ((Real.rpow x n) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))) (𝓝[<] 1) (𝓝 ((𝓝[<] 1).limUnder (fun x : ℝ => ((Real.rpow x n) /. (Real.rpow (1 + x) (((2 : ℝ))⁻¹)))))))
  (h6 : Tendsto (fun x : ℝ => ((Real.rpow x n) /. (Real.rpow (1 + x) (((2 : ℝ))⁻¹)))) (𝓝[<] 1) (𝓝 (1 /. (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)))))
  (h7 : Tendsto (fun x : ℝ => ((Real.rpow (1 - x) (((2 : ℝ))⁻¹)) * ((Real.rpow x n) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))) (𝓝[<] 1) (𝓝 (1 /. (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)))))
  (h8 : (forall (n_1 : ℝ), ((n_1 ∈ (Set.univ : Set ℝ)) → (exists (I_2 : ℝ), ((I_2 ∈ (Set.univ : Set ℝ)) ∧ ((∫ x in (1 /. 2)..(1 : ℝ), (((Real.rpow x n_1) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = I_2))))))
  (h9 : (n ∈ (Set.univ : Set ℝ)) ∧ (n > (-(1 : ℝ))))
  (h10 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((Real.rpow x n) /. (Real.rpow (1 + x) (((2 : ℝ))⁻¹)))) (𝓝[<] 1) (𝓝 L))
  : (n ∈ ({n_1 | (n_1 > (-(1 : ℝ)))})) ↔ (exists (I : ℝ), ((I ∈ (Set.univ : Set ℝ)) ∧ ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.rpow x n) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = I))) := by
  sorry

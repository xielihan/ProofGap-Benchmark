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

-- exercise: exercise_2601

theorem proof_gap_exercise_2601_1
  (u : (ℕ -> ℝ))
  (k : ℕ)
  (h1 : k ∈ (Set.univ : Set ℕ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((Real.rpow ((n)! : ℝ) (((2 : ℝ))⁻¹)) /. (∏ k_1 ∈ Finset.Icc (1 : ℕ) n, (2 + (Real.rpow (k_1 : ℝ) (((2 : ℝ))⁻¹)))))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((u n) /. (u (n + 1))) = ((2 + (Real.rpow (n + 1) (((2 : ℝ))⁻¹))) /. (Real.rpow (n + 1) (((2 : ℝ))⁻¹)))))) := by
  sorry

theorem proof_gap_exercise_2601_2
  (u : (ℕ -> ℝ))
  (k : ℕ)
  (h1 : k ∈ (Set.univ : Set ℕ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((Real.rpow ((n)! : ℝ) (((2 : ℝ))⁻¹)) /. (∏ k_1 ∈ Finset.Icc (1 : ℕ) n, (2 + (Real.rpow (k_1 : ℝ) (((2 : ℝ))⁻¹)))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((u n) /. (u (n + 1))) = ((2 + (Real.rpow (n + 1) (((2 : ℝ))⁻¹))) /. (Real.rpow (n + 1) (((2 : ℝ))⁻¹)))))))
  : (∃ L : ℝ, Tendsto (fun n : ℕ => (n * (((2 + (Real.rpow (n + 1) (((2 : ℝ))⁻¹))) /. (Real.rpow (n + 1) (((2 : ℝ))⁻¹))) - 1))) atTop (𝓝 L) ∧ (Tendsto (fun n : ℕ => (n * (((u n) /. (u (n + 1))) - 1))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (n * (((2 + (Real.rpow (n + 1) (((2 : ℝ))⁻¹))) /. (Real.rpow (n + 1) (((2 : ℝ))⁻¹))) - 1))))))) := by
  sorry

theorem proof_gap_exercise_2601_3
  (u : (ℕ -> ℝ))
  (k : ℕ)
  (h1 : k ∈ (Set.univ : Set ℕ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((Real.rpow ((n)! : ℝ) (((2 : ℝ))⁻¹)) /. (∏ k_1 ∈ Finset.Icc (1 : ℕ) n, (2 + (Real.rpow (k_1 : ℝ) (((2 : ℝ))⁻¹)))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((u n) /. (u (n + 1))) = ((2 + (Real.rpow (n + 1) (((2 : ℝ))⁻¹))) /. (Real.rpow (n + 1) (((2 : ℝ))⁻¹)))))))
  (h4 : Tendsto (fun n : ℕ => (n * (((u n) /. (u (n + 1))) - 1))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (n * (((2 + (Real.rpow (n + 1) (((2 : ℝ))⁻¹))) /. (Real.rpow (n + 1) (((2 : ℝ))⁻¹))) - 1))))))
  (h5 : ∃ L : ℝ, Tendsto (fun n : ℕ => (n * (((2 + (Real.rpow (n + 1) (((2 : ℝ))⁻¹))) /. (Real.rpow (n + 1) (((2 : ℝ))⁻¹))) - 1))) atTop (𝓝 L))
  : (∃ L : ℝ, Tendsto (fun n : ℕ => ((2 * n) /. (Real.rpow (n + 1) (((2 : ℝ))⁻¹)))) atTop (𝓝 L) ∧ (Tendsto (fun n : ℕ => (n * (((2 + (Real.rpow (n + 1) (((2 : ℝ))⁻¹))) /. (Real.rpow (n + 1) (((2 : ℝ))⁻¹))) - 1))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => ((2 * n) /. (Real.rpow (n + 1) (((2 : ℝ))⁻¹)))))))) := by
  sorry

theorem proof_gap_exercise_2601_4
  (u : (ℕ -> ℝ))
  (k : ℕ)
  (h1 : k ∈ (Set.univ : Set ℕ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((Real.rpow ((n)! : ℝ) (((2 : ℝ))⁻¹)) /. (∏ k_1 ∈ Finset.Icc (1 : ℕ) n, (2 + (Real.rpow (k_1 : ℝ) (((2 : ℝ))⁻¹)))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((u n) /. (u (n + 1))) = ((2 + (Real.rpow (n + 1) (((2 : ℝ))⁻¹))) /. (Real.rpow (n + 1) (((2 : ℝ))⁻¹)))))))
  (h4 : Tendsto (fun n : ℕ => (n * (((u n) /. (u (n + 1))) - 1))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (n * (((2 + (Real.rpow (n + 1) (((2 : ℝ))⁻¹))) /. (Real.rpow (n + 1) (((2 : ℝ))⁻¹))) - 1))))))
  (h5 : Tendsto (fun n : ℕ => (n * (((2 + (Real.rpow (n + 1) (((2 : ℝ))⁻¹))) /. (Real.rpow (n + 1) (((2 : ℝ))⁻¹))) - 1))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => ((2 * n) /. (Real.rpow (n + 1) (((2 : ℝ))⁻¹)))))))
  (h6 : ∃ L : ℝ, Tendsto (fun n : ℕ => (n * (((2 + (Real.rpow (n + 1) (((2 : ℝ))⁻¹))) /. (Real.rpow (n + 1) (((2 : ℝ))⁻¹))) - 1))) atTop (𝓝 L))
  (h7 : ∃ L : ℝ, Tendsto (fun n : ℕ => ((2 * n) /. (Real.rpow (n + 1) (((2 : ℝ))⁻¹)))) atTop (𝓝 L))
  : Tendsto (fun n : ℕ => (((2 * n) /. (Real.rpow (n + 1) (((2 : ℝ))⁻¹))) : EReal)) atTop (𝓝 ⊤) := by
  sorry

theorem proof_gap_exercise_2601_5
  (u : (ℕ -> ℝ))
  (k : ℕ)
  (h1 : k ∈ (Set.univ : Set ℕ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((Real.rpow ((n)! : ℝ) (((2 : ℝ))⁻¹)) /. (∏ k_1 ∈ Finset.Icc (1 : ℕ) n, (2 + (Real.rpow (k_1 : ℝ) (((2 : ℝ))⁻¹)))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((u n) /. (u (n + 1))) = ((2 + (Real.rpow (n + 1) (((2 : ℝ))⁻¹))) /. (Real.rpow (n + 1) (((2 : ℝ))⁻¹)))))))
  (h4 : Tendsto (fun n : ℕ => (n * (((u n) /. (u (n + 1))) - 1))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (n * (((2 + (Real.rpow (n + 1) (((2 : ℝ))⁻¹))) /. (Real.rpow (n + 1) (((2 : ℝ))⁻¹))) - 1))))))
  (h5 : Tendsto (fun n : ℕ => (n * (((2 + (Real.rpow (n + 1) (((2 : ℝ))⁻¹))) /. (Real.rpow (n + 1) (((2 : ℝ))⁻¹))) - 1))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => ((2 * n) /. (Real.rpow (n + 1) (((2 : ℝ))⁻¹)))))))
  (h6 : Tendsto (fun n : ℕ => (((2 * n) /. (Real.rpow (n + 1) (((2 : ℝ))⁻¹))) : EReal)) atTop (𝓝 ⊤))
  (h7 : ∃ L : ℝ, Tendsto (fun n : ℕ => (n * (((2 + (Real.rpow (n + 1) (((2 : ℝ))⁻¹))) /. (Real.rpow (n + 1) (((2 : ℝ))⁻¹))) - 1))) atTop (𝓝 L))
  (h8 : ∃ L : ℝ, Tendsto (fun n : ℕ => ((2 * n) /. (Real.rpow (n + 1) (((2 : ℝ))⁻¹)))) atTop (𝓝 L))
  : Tendsto (fun n : ℕ => ((n * (((u n) /. (u (n + 1))) - 1)) : EReal)) atTop (𝓝 ⊤) := by
  sorry

theorem proof_gap_exercise_2601_6
  (u : (ℕ -> ℝ))
  (k : ℕ)
  (h1 : k ∈ (Set.univ : Set ℕ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((Real.rpow ((n)! : ℝ) (((2 : ℝ))⁻¹)) /. (∏ k_1 ∈ Finset.Icc (1 : ℕ) n, (2 + (Real.rpow (k_1 : ℝ) (((2 : ℝ))⁻¹)))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((u n) /. (u (n + 1))) = ((2 + (Real.rpow (n + 1) (((2 : ℝ))⁻¹))) /. (Real.rpow (n + 1) (((2 : ℝ))⁻¹)))))))
  (h4 : Tendsto (fun n : ℕ => (n * (((u n) /. (u (n + 1))) - 1))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (n * (((2 + (Real.rpow (n + 1) (((2 : ℝ))⁻¹))) /. (Real.rpow (n + 1) (((2 : ℝ))⁻¹))) - 1))))))
  (h5 : Tendsto (fun n : ℕ => (n * (((2 + (Real.rpow (n + 1) (((2 : ℝ))⁻¹))) /. (Real.rpow (n + 1) (((2 : ℝ))⁻¹))) - 1))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => ((2 * n) /. (Real.rpow (n + 1) (((2 : ℝ))⁻¹)))))))
  (h6 : Tendsto (fun n : ℕ => (((2 * n) /. (Real.rpow (n + 1) (((2 : ℝ))⁻¹))) : EReal)) atTop (𝓝 ⊤))
  (h7 : Tendsto (fun n : ℕ => ((n * (((u n) /. (u (n + 1))) - 1)) : EReal)) atTop (𝓝 ⊤))
  (h8 : ∃ L : ℝ, Tendsto (fun n : ℕ => (n * (((2 + (Real.rpow (n + 1) (((2 : ℝ))⁻¹))) /. (Real.rpow (n + 1) (((2 : ℝ))⁻¹))) - 1))) atTop (𝓝 L))
  (h9 : ∃ L : ℝ, Tendsto (fun n : ℕ => ((2 * n) /. (Real.rpow (n + 1) (((2 : ℝ))⁻¹)))) atTop (𝓝 L))
  : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (u n) else 0) := by
  sorry

theorem proof_gap_exercise_2601_7
  (u : (ℕ -> ℝ))
  (k : ℕ)
  (h1 : k ∈ (Set.univ : Set ℕ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((Real.rpow ((n)! : ℝ) (((2 : ℝ))⁻¹)) /. (∏ k_1 ∈ Finset.Icc (1 : ℕ) n, (2 + (Real.rpow (k_1 : ℝ) (((2 : ℝ))⁻¹)))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((u n) /. (u (n + 1))) = ((2 + (Real.rpow (n + 1) (((2 : ℝ))⁻¹))) /. (Real.rpow (n + 1) (((2 : ℝ))⁻¹)))))))
  (h4 : Tendsto (fun n : ℕ => (n * (((u n) /. (u (n + 1))) - 1))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (n * (((2 + (Real.rpow (n + 1) (((2 : ℝ))⁻¹))) /. (Real.rpow (n + 1) (((2 : ℝ))⁻¹))) - 1))))))
  (h5 : Tendsto (fun n : ℕ => (n * (((2 + (Real.rpow (n + 1) (((2 : ℝ))⁻¹))) /. (Real.rpow (n + 1) (((2 : ℝ))⁻¹))) - 1))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => ((2 * n) /. (Real.rpow (n + 1) (((2 : ℝ))⁻¹)))))))
  (h6 : Tendsto (fun n : ℕ => (((2 * n) /. (Real.rpow (n + 1) (((2 : ℝ))⁻¹))) : EReal)) atTop (𝓝 ⊤))
  (h7 : Tendsto (fun n : ℕ => ((n * (((u n) /. (u (n + 1))) - 1)) : EReal)) atTop (𝓝 ⊤))
  (h8 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (u n) else 0))
  (h9 : ∃ L : ℝ, Tendsto (fun n : ℕ => (n * (((2 + (Real.rpow (n + 1) (((2 : ℝ))⁻¹))) /. (Real.rpow (n + 1) (((2 : ℝ))⁻¹))) - 1))) atTop (𝓝 L))
  (h10 : ∃ L : ℝ, Tendsto (fun n : ℕ => ((2 * n) /. (Real.rpow (n + 1) (((2 : ℝ))⁻¹)))) atTop (𝓝 L))
  : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (u n) else 0) := by
  sorry

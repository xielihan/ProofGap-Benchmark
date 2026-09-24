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

-- exercise: exercise_1003

theorem proof_gap_exercise_1003_1
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((Real.sin (x ^ (2 : ℕ))) ≥ 0)) → ((f x) = (Real.rpow (Real.sin (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (exists (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ ((Real.rpow ((2 * k) * Real.pi) (((2 : ℝ))⁻¹)) < |(x)|)) ∧ (|(x)| < (Real.rpow (((2 * k) + 1) * Real.pi) (((2 : ℝ))⁻¹)))))) → ((iteratedDeriv 1 (fun t => f t) x) = ((x * (Real.cos (x ^ (2 : ℕ)))) /. (Real.rpow (Real.sin (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))))) := by
  sorry

theorem proof_gap_exercise_1003_2
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((Real.sin (x ^ (2 : ℕ))) ≥ 0)) → ((f x) = (Real.rpow (Real.sin (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (exists (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ ((Real.rpow ((2 * k) * Real.pi) (((2 : ℝ))⁻¹)) < |(x)|)) ∧ (|(x)| < (Real.rpow (((2 * k) + 1) * Real.pi) (((2 : ℝ))⁻¹)))))) → ((iteratedDeriv 1 (fun t_1 => f t_1) x) = ((x * (Real.cos (x ^ (2 : ℕ)))) /. (Real.rpow (Real.sin (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 0)) → (Tendsto (fun t : ℝ => (((f t) - (f (0 : ℝ))) /. (t - 0))) (𝓝[>] 0) (𝓝 1)))) := by
  sorry

theorem proof_gap_exercise_1003_3
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((Real.sin (x ^ (2 : ℕ))) ≥ 0)) → ((f x) = (Real.rpow (Real.sin (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (exists (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ ((Real.rpow ((2 * k) * Real.pi) (((2 : ℝ))⁻¹)) < |(x)|)) ∧ (|(x)| < (Real.rpow (((2 * k) + 1) * Real.pi) (((2 : ℝ))⁻¹)))))) → ((iteratedDeriv 1 (fun t_1 => f t_1) x) = ((x * (Real.cos (x ^ (2 : ℕ)))) /. (Real.rpow (Real.sin (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 0)) → (Tendsto (fun t : ℝ => (((f t) - (f (0 : ℝ))) /. (t - 0))) (𝓝[>] 0) (𝓝 1)))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 0)) → (Tendsto (fun t : ℝ => (((f t) - (f (0 : ℝ))) /. (t - 0))) (𝓝[<] 0) (𝓝 (-(1 : ℝ)))))) := by
  sorry

theorem proof_gap_exercise_1003_4
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((Real.sin (x ^ (2 : ℕ))) ≥ 0)) → ((f x) = (Real.rpow (Real.sin (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (exists (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ ((Real.rpow ((2 * k) * Real.pi) (((2 : ℝ))⁻¹)) < |(x)|)) ∧ (|(x)| < (Real.rpow (((2 * k) + 1) * Real.pi) (((2 : ℝ))⁻¹)))))) → ((iteratedDeriv 1 (fun t_1 => f t_1) x) = ((x * (Real.cos (x ^ (2 : ℕ)))) /. (Real.rpow (Real.sin (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 0)) → (Tendsto (fun t : ℝ => (((f t) - (f (0 : ℝ))) /. (t - 0))) (𝓝[>] 0) (𝓝 1)))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 0)) → (Tendsto (fun t : ℝ => (((f t) - (f (0 : ℝ))) /. (t - 0))) (𝓝[<] 0) (𝓝 (-(1 : ℝ)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (exists (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n : ℕ | 0 < n}))) ∧ (x = (Real.rpow ((2 * k) * Real.pi) (((2 : ℝ))⁻¹)))))) → (Tendsto (fun t : ℝ => ((((f t) - (f x)) /. (t - x)) : EReal)) (𝓝[>] x) (𝓝 ⊤)))) := by
  sorry

theorem proof_gap_exercise_1003_5
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (Real.rpow |((Real.sin (x ^ (2 : ℕ))))| (((2 : ℝ))⁻¹))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (exists (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ ((Real.rpow ((2 * k) * Real.pi) (((2 : ℝ))⁻¹)) < |(x)|)) ∧ (|(x)| < (Real.rpow (((2 * k) + 1) * Real.pi) (((2 : ℝ))⁻¹)))))) → ((iteratedDeriv 1 (fun t_1 => f t_1) x) = ((x * (Real.cos (x ^ (2 : ℕ)))) /. (Real.rpow (Real.sin (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 0)) → (Tendsto (fun t : ℝ => (((f t) - (f (0 : ℝ))) /. (t - 0))) (𝓝[>] 0) (𝓝 1)))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 0)) → (Tendsto (fun t : ℝ => (((f t) - (f (0 : ℝ))) /. (t - 0))) (𝓝[<] 0) (𝓝 (-(1 : ℝ)))))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (exists (k : ℕ), ((k ∈ ({n : ℕ | 0 < n})) ∧ (x = (Real.rpow ((2 * k) * Real.pi) (((2 : ℝ))⁻¹)))))) → (Tendsto (fun t : ℝ => ((((f t) - (f x)) /. (t - x)) : EReal)) (𝓝[>] x) (𝓝 ⊤)))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (exists (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n : ℕ | 0 < n}))) ∧ (x = (Real.rpow ((2 * k) * Real.pi) (((2 : ℝ))⁻¹)))))) → (Tendsto (fun t : ℝ => ((((f t) - (f x)) /. (t - x)) : EReal)) (𝓝[<] x) (𝓝 ⊥)))) := by
  sorry

theorem proof_gap_exercise_1003_6
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((Real.sin (x ^ (2 : ℕ))) ≥ 0)) → ((f x) = (Real.rpow (Real.sin (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (exists (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ ((Real.rpow ((2 * k) * Real.pi) (((2 : ℝ))⁻¹)) < |(x)|)) ∧ (|(x)| < (Real.rpow (((2 * k) + 1) * Real.pi) (((2 : ℝ))⁻¹)))))) → ((iteratedDeriv 1 (fun t_1 => f t_1) x) = ((x * (Real.cos (x ^ (2 : ℕ)))) /. (Real.rpow (Real.sin (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 0)) → (Tendsto (fun t : ℝ => (((f t) - (f (0 : ℝ))) /. (t - 0))) (𝓝[>] 0) (𝓝 1)))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 0)) → (Tendsto (fun t : ℝ => (((f t) - (f (0 : ℝ))) /. (t - 0))) (𝓝[<] 0) (𝓝 (-(1 : ℝ)))))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (exists (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n : ℕ | 0 < n}))) ∧ (x = (Real.rpow ((2 * k) * Real.pi) (((2 : ℝ))⁻¹)))))) → (Tendsto (fun t : ℝ => ((((f t) - (f x)) /. (t - x)) : EReal)) (𝓝[>] x) (𝓝 ⊤)))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (exists (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n : ℕ | 0 < n}))) ∧ (x = (Real.rpow ((2 * k) * Real.pi) (((2 : ℝ))⁻¹)))))) → (Tendsto (fun t : ℝ => ((((f t) - (f x)) /. (t - x)) : EReal)) (𝓝[<] x) (𝓝 ⊥)))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (exists (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n : ℕ | 0 < n}))) ∧ (x = (Real.rpow (((2 * k) + 1) * Real.pi) (((2 : ℝ))⁻¹)))))) → (Tendsto (fun t : ℝ => ((((f t) - (f x)) /. (t - x)) : EReal)) (𝓝[<] x) (𝓝 ⊤)))) := by
  sorry

theorem proof_gap_exercise_1003_7
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((Real.sin (x ^ (2 : ℕ))) ≥ 0)) → ((f x) = (Real.rpow (Real.sin (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (exists (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ ((Real.rpow ((2 * k) * Real.pi) (((2 : ℝ))⁻¹)) < |(x)|)) ∧ (|(x)| < (Real.rpow (((2 * k) + 1) * Real.pi) (((2 : ℝ))⁻¹)))))) → ((iteratedDeriv 1 (fun t_1 => f t_1) x) = ((x * (Real.cos (x ^ (2 : ℕ)))) /. (Real.rpow (Real.sin (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 0)) → (Tendsto (fun t : ℝ => (((f t) - (f (0 : ℝ))) /. (t - 0))) (𝓝[>] 0) (𝓝 1)))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 0)) → (Tendsto (fun t : ℝ => (((f t) - (f (0 : ℝ))) /. (t - 0))) (𝓝[<] 0) (𝓝 (-(1 : ℝ)))))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (exists (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n : ℕ | 0 < n}))) ∧ (x = (Real.rpow ((2 * k) * Real.pi) (((2 : ℝ))⁻¹)))))) → (Tendsto (fun t : ℝ => ((((f t) - (f x)) /. (t - x)) : EReal)) (𝓝[>] x) (𝓝 ⊤)))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (exists (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n : ℕ | 0 < n}))) ∧ (x = (Real.rpow ((2 * k) * Real.pi) (((2 : ℝ))⁻¹)))))) → (Tendsto (fun t : ℝ => ((((f t) - (f x)) /. (t - x)) : EReal)) (𝓝[<] x) (𝓝 ⊥)))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (exists (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n : ℕ | 0 < n}))) ∧ (x = (Real.rpow (((2 * k) + 1) * Real.pi) (((2 : ℝ))⁻¹)))))) → (Tendsto (fun t : ℝ => ((((f t) - (f x)) /. (t - x)) : EReal)) (𝓝[<] x) (𝓝 ⊤)))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (exists (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n : ℕ | 0 < n}))) ∧ (x = (Real.rpow (((2 * k) + 1) * Real.pi) (((2 : ℝ))⁻¹)))))) → (Tendsto (fun t : ℝ => ((((f t) - (f x)) /. (t - x)) : EReal)) (𝓝[>] x) (𝓝 ⊥)))) := by
  sorry

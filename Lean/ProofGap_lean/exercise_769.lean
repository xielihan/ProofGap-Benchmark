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

-- exercise: exercise_769

theorem proof_gap_exercise_769_1
  (y : (ℝ -> ℝ))
  (g_1 : (ℝ -> ℝ))
  (g_2 : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((2 * x) /. (1 + (x ^ (2 : ℕ))))))))
  : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Icc (-(1 : ℝ)) 1))) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((y x) = t)) → (((((x ^ (2 : ℕ)) * t) - (2 * x)) + t) = 0))))) := by
  sorry

theorem proof_gap_exercise_769_2
  (y : (ℝ -> ℝ))
  (g_1 : (ℝ -> ℝ))
  (g_2 : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((2 * x) /. (1 + (x ^ (2 : ℕ))))))))
  (h2 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Icc (-(1 : ℝ)) 1))) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((y x) = t)) → (((((x ^ (2 : ℕ)) * t) - (2 * x)) + t) = 0))))))
  : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (t ≠ 0)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((((x ^ (2 : ℕ)) * t) - (2 * x)) + t) = 0)) → ((x = ((1 - (Real.rpow (1 - (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. t)) ∨ (x = ((1 + (Real.rpow (1 - (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. t))))))) := by
  sorry

theorem proof_gap_exercise_769_3
  (y : (ℝ -> ℝ))
  (g_1 : (ℝ -> ℝ))
  (g_2 : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((2 * x) /. (1 + (x ^ (2 : ℕ))))))))
  (h2 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Icc (-(1 : ℝ)) 1))) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((y x) = t)) → (((((x ^ (2 : ℕ)) * t) - (2 * x)) + t) = 0))))))
  (h3 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (t ≠ 0)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((((x ^ (2 : ℕ)) * t) - (2 * x)) + t) = 0)) → ((x = ((1 - (Real.rpow (1 - (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. t)) ∨ (x = ((1 + (Real.rpow (1 - (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. t))))))))
  : Tendsto (fun t : ℝ => ((1 - (Real.rpow (1 - (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. t)) (𝓝[≠] 0) (𝓝 0) := by
  sorry

theorem proof_gap_exercise_769_4
  (y : (ℝ -> ℝ))
  (g_1 : (ℝ -> ℝ))
  (g_2 : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((2 * x) /. (1 + (x ^ (2 : ℕ))))))))
  (h2 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Icc (-(1 : ℝ)) 1))) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((y x) = t)) → (((((x ^ (2 : ℕ)) * t) - (2 * x)) + t) = 0))))))
  (h3 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (t ≠ 0)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((((x ^ (2 : ℕ)) * t) - (2 * x)) + t) = 0)) → ((x = ((1 - (Real.rpow (1 - (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. t)) ∨ (x = ((1 + (Real.rpow (1 - (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. t))))))))
  (h4 : Tendsto (fun t : ℝ => ((1 - (Real.rpow (1 - (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. t)) (𝓝[≠] 0) (𝓝 0))
  : Tendsto (fun t : ℝ => (((1 + (Real.rpow (1 - (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. t) : EReal)) (𝓝[≠] 0) (𝓝 ⊤) := by
  sorry

theorem proof_gap_exercise_769_5
  (y : (ℝ -> ℝ))
  (g_1 : (ℝ -> ℝ))
  (g_2 : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((2 * x) /. (1 + (x ^ (2 : ℕ))))))))
  (h2 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Icc (-(1 : ℝ)) 1))) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((y x) = t)) → (((((x ^ (2 : ℕ)) * t) - (2 * x)) + t) = 0))))))
  (h3 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (t ≠ 0)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((((x ^ (2 : ℕ)) * t) - (2 * x)) + t) = 0)) → ((x = ((1 - (Real.rpow (1 - (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. t)) ∨ (x = ((1 + (Real.rpow (1 - (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. t))))))))
  (h4 : Tendsto (fun t : ℝ => ((1 - (Real.rpow (1 - (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. t)) (𝓝[≠] 0) (𝓝 0))
  (h5 : (Tendsto (fun t : ℝ => (((1 + (Real.rpow (1 - (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. t) : EReal)) (𝓝[<] 0) (𝓝 ⊥)) ∧ (Tendsto (fun t : ℝ => (((1 + (Real.rpow (1 - (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. t) : EReal)) (𝓝[>] 0) (𝓝 ⊤)))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((g_1 (y x)) = x))))
  : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((g_1 t) = (if (t ≠ 0) then ((1 - (Real.rpow (1 - (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. t) else (if (t = 0) then 0 else 0))))) := by
  sorry

theorem proof_gap_exercise_769_6
  (y : (ℝ -> ℝ))
  (g_1 : (ℝ -> ℝ))
  (g_2 : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((2 * x) /. (1 + (x ^ (2 : ℕ))))))))
  (h2 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Icc (-(1 : ℝ)) 1))) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((y x) = t)) → (((((x ^ (2 : ℕ)) * t) - (2 * x)) + t) = 0))))))
  (h3 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (t ≠ 0)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((((x ^ (2 : ℕ)) * t) - (2 * x)) + t) = 0)) → ((x = ((1 - (Real.rpow (1 - (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. t)) ∨ (x = ((1 + (Real.rpow (1 - (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. t))))))))
  (h4 : Tendsto (fun t : ℝ => ((1 - (Real.rpow (1 - (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. t)) (𝓝[≠] 0) (𝓝 0))
  (h5 : (Tendsto (fun t : ℝ => (((1 + (Real.rpow (1 - (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. t) : EReal)) (𝓝[<] 0) (𝓝 ⊥)) ∧ (Tendsto (fun t : ℝ => (((1 + (Real.rpow (1 - (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. t) : EReal)) (𝓝[>] 0) (𝓝 ⊤)))
  (h6 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((g_1 t) = (if (t ≠ 0) then ((1 - (Real.rpow (1 - (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. t) else (if (t = 0) then 0 else 0))))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ((Set.Iic (-(1 : ℝ))) ∪ (Set.Ici 1)))) → ((g_2 (y x)) = x))))
  : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ ((Set.Ico (-(1 : ℝ)) 0) ∪ (Set.Ioc 0 1)))) → ((g_2 t) = ((1 + (Real.rpow (1 - (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. t)))) := by
  sorry

theorem proof_gap_exercise_769_7
  (y : (ℝ -> ℝ))
  (g_1 : (ℝ -> ℝ))
  (g_2 : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((2 * x) /. (1 + (x ^ (2 : ℕ))))))))
  (h2 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Icc (-(1 : ℝ)) 1))) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((y x) = t)) → (((((x ^ (2 : ℕ)) * t) - (2 * x)) + t) = 0))))))
  (h3 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (t ≠ 0)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((((x ^ (2 : ℕ)) * t) - (2 * x)) + t) = 0)) → ((x = ((1 - (Real.rpow (1 - (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. t)) ∨ (x = ((1 + (Real.rpow (1 - (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. t))))))))
  (h4 : Tendsto (fun t : ℝ => ((1 - (Real.rpow (1 - (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. t)) (𝓝[≠] 0) (𝓝 0))
  (h5 : (Tendsto (fun t : ℝ => (((1 + (Real.rpow (1 - (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. t) : EReal)) (𝓝[<] 0) (𝓝 ⊥)) ∧ (Tendsto (fun t : ℝ => (((1 + (Real.rpow (1 - (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. t) : EReal)) (𝓝[>] 0) (𝓝 ⊤)))
  (h6 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((g_1 t) = (if (t ≠ 0) then ((1 - (Real.rpow (1 - (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. t) else (if (t = 0) then 0 else 0))))))
  (h7 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ ((Set.Ico (-(1 : ℝ)) 0) ∪ (Set.Ioc 0 1)))) → ((g_2 t) = ((1 + (Real.rpow (1 - (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. t)))))
  : ContinuousOn g_1 (Set.Icc (-(1 : ℝ)) 1) := by
  sorry

theorem proof_gap_exercise_769_8
  (y : (ℝ -> ℝ))
  (g_1 : (ℝ -> ℝ))
  (g_2 : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((2 * x) /. (1 + (x ^ (2 : ℕ))))))))
  (h2 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Icc (-(1 : ℝ)) 1))) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((y x) = t)) → (((((x ^ (2 : ℕ)) * t) - (2 * x)) + t) = 0))))))
  (h3 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (t ≠ 0)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((((x ^ (2 : ℕ)) * t) - (2 * x)) + t) = 0)) → ((x = ((1 - (Real.rpow (1 - (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. t)) ∨ (x = ((1 + (Real.rpow (1 - (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. t))))))))
  (h4 : Tendsto (fun t : ℝ => ((1 - (Real.rpow (1 - (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. t)) (𝓝[≠] 0) (𝓝 0))
  (h5 : (Tendsto (fun t : ℝ => (((1 + (Real.rpow (1 - (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. t) : EReal)) (𝓝[<] 0) (𝓝 ⊥)) ∧ (Tendsto (fun t : ℝ => (((1 + (Real.rpow (1 - (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. t) : EReal)) (𝓝[>] 0) (𝓝 ⊤)))
  (h6 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((g_1 t) = (if (t ≠ 0) then ((1 - (Real.rpow (1 - (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. t) else (if (t = 0) then 0 else 0))))))
  (h7 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ ((Set.Ico (-(1 : ℝ)) 0) ∪ (Set.Ioc 0 1)))) → ((g_2 t) = ((1 + (Real.rpow (1 - (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. t)))))
  (h8 : ContinuousOn g_1 (Set.Icc (-(1 : ℝ)) 1))
  : ContinuousOn g_2 ((Set.Ico (-(1 : ℝ)) 0) ∪ (Set.Ioc 0 1)) := by
  sorry

theorem proof_gap_exercise_769_9
  (y : (ℝ -> ℝ))
  (g_1 : (ℝ -> ℝ))
  (g_2 : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((2 * x) /. (1 + (x ^ (2 : ℕ))))))))
  (h2 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Icc (-(1 : ℝ)) 1))) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((y x) = t)) → (((((x ^ (2 : ℕ)) * t) - (2 * x)) + t) = 0))))))
  (h3 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (t ≠ 0)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((((x ^ (2 : ℕ)) * t) - (2 * x)) + t) = 0)) → ((x = ((1 - (Real.rpow (1 - (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. t)) ∨ (x = ((1 + (Real.rpow (1 - (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. t))))))))
  (h4 : Tendsto (fun t : ℝ => ((1 - (Real.rpow (1 - (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. t)) (𝓝[≠] 0) (𝓝 0))
  (h5 : (Tendsto (fun t : ℝ => (((1 + (Real.rpow (1 - (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. t) : EReal)) (𝓝[<] 0) (𝓝 ⊥)) ∧ (Tendsto (fun t : ℝ => (((1 + (Real.rpow (1 - (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. t) : EReal)) (𝓝[>] 0) (𝓝 ⊤)))
  (h6 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((g_1 t) = (if (t ≠ 0) then ((1 - (Real.rpow (1 - (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. t) else (if (t = 0) then 0 else 0))))))
  (h7 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ ((Set.Ico (-(1 : ℝ)) 0) ∪ (Set.Ioc 0 1)))) → ((g_2 t) = ((1 + (Real.rpow (1 - (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. t)))))
  (h8 : ContinuousOn g_1 (Set.Icc (-(1 : ℝ)) 1))
  (h9 : ContinuousOn g_2 ((Set.Ico (-(1 : ℝ)) 0) ∪ (Set.Ioc 0 1)))
  : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Icc (-(1 : ℝ)) 1))) → (((g_1 t) = (if (t ≠ 0) then ((1 - (Real.rpow (1 - (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. t) else (if (t = 0) then 0 else 0))) ∧ (forall (t_1 : ℝ), (((t_1 ∈ (Set.univ : Set ℝ)) ∧ (t_1 ∈ ((Set.Ico (-(1 : ℝ)) 0) ∪ (Set.Ioc 0 1)))) → ((g_2 t_1) = ((1 + (Real.rpow (1 - (t_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. t_1))))))) → ((((ContinuousOn g_1 (Set.Icc (-(1 : ℝ)) 1)) ∧ (ContinuousOn g_2 ((Set.Ico (-(1 : ℝ)) 0) ∪ (Set.Ioc 0 1)))) ∧ (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((y (g_1 t)) = t)))) ∧ (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ ((Set.Ico (-(1 : ℝ)) 0) ∪ (Set.Ioc 0 1)))) → ((y (g_2 t)) = t)))) := by
  sorry

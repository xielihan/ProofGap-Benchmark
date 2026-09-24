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

-- exercise: exercise_992_2

theorem proof_gap_exercise_992_2_1
  (f : (ℝ -> ℝ))
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((f x) = ((Real.rpow x n) * (Real.sin (1 /. x)))))))
  (h3 : (f (0 : ℝ)) = 0)
  (h4 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  : (n > 1) → (∃ L : ℝ, Tendsto (fun v_uCE_u94_x : ℝ => ((Real.rpow v_uCE_u94_x (n - 1)) * (Real.sin (1 /. v_uCE_u94_x)))) (𝓝[≠] 0) (𝓝 L) ∧ (Tendsto (fun v_uCE_u94_x : ℝ => (((f (0 + v_uCE_u94_x)) - (f (0 : ℝ))) /. v_uCE_u94_x)) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun v_uCE_u94_x : ℝ => ((Real.rpow v_uCE_u94_x (n - 1)) * (Real.sin (1 /. v_uCE_u94_x)))))))) := by
  sorry

theorem proof_gap_exercise_992_2_2
  (f : (ℝ -> ℝ))
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((f x) = ((Real.rpow x n) * (Real.sin (1 /. x)))))))
  (h3 : (f (0 : ℝ)) = 0)
  (h4 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h5 : (n > 1) → (Tendsto (fun v_uCE_u94_x : ℝ => (((f (0 + v_uCE_u94_x)) - (f (0 : ℝ))) /. v_uCE_u94_x)) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun v_uCE_u94_x : ℝ => ((Real.rpow v_uCE_u94_x (n - 1)) * (Real.sin (1 /. v_uCE_u94_x))))))))
  (h6 : ∃ L : ℝ, Tendsto (fun v_uCE_u94_x : ℝ => ((Real.rpow v_uCE_u94_x (n - 1)) * (Real.sin (1 /. v_uCE_u94_x)))) (𝓝[≠] 0) (𝓝 L))
  : (n > 1) → (Tendsto (fun v_uCE_u94_x : ℝ => ((Real.rpow v_uCE_u94_x (n - 1)) * (Real.sin (1 /. v_uCE_u94_x)))) (𝓝[≠] 0) (𝓝 0)) := by
  sorry

theorem proof_gap_exercise_992_2_3
  (f : (ℝ -> ℝ))
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((f x) = ((Real.rpow x n) * (Real.sin (1 /. x)))))))
  (h3 : (f (0 : ℝ)) = 0)
  (h4 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h5 : (n > 1) → (Tendsto (fun v_uCE_u94_x : ℝ => (((f (0 + v_uCE_u94_x)) - (f (0 : ℝ))) /. v_uCE_u94_x)) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun v_uCE_u94_x : ℝ => ((Real.rpow v_uCE_u94_x (n - 1)) * (Real.sin (1 /. v_uCE_u94_x))))))))
  (h6 : (n > 1) → (Tendsto (fun v_uCE_u94_x : ℝ => ((Real.rpow v_uCE_u94_x (n - 1)) * (Real.sin (1 /. v_uCE_u94_x)))) (𝓝[≠] 0) (𝓝 0)))
  (h7 : ∃ L : ℝ, Tendsto (fun v_uCE_u94_x : ℝ => ((Real.rpow v_uCE_u94_x (n - 1)) * (Real.sin (1 /. v_uCE_u94_x)))) (𝓝[≠] 0) (𝓝 L))
  : (n > 1) → (Tendsto (fun v_uCE_u94_x : ℝ => (((f (0 + v_uCE_u94_x)) - (f (0 : ℝ))) /. v_uCE_u94_x)) (𝓝[≠] 0) (𝓝 0)) := by
  sorry

theorem proof_gap_exercise_992_2_4
  (f : (ℝ -> ℝ))
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((f x) = ((Real.rpow x n) * (Real.sin (1 /. x)))))))
  (h3 : (f (0 : ℝ)) = 0)
  (h4 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h5 : (n > 1) → (Tendsto (fun v_uCE_u94_x : ℝ => (((f (0 + v_uCE_u94_x)) - (f (0 : ℝ))) /. v_uCE_u94_x)) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun v_uCE_u94_x : ℝ => ((Real.rpow v_uCE_u94_x (n - 1)) * (Real.sin (1 /. v_uCE_u94_x))))))))
  (h6 : (n > 1) → (Tendsto (fun v_uCE_u94_x : ℝ => ((Real.rpow v_uCE_u94_x (n - 1)) * (Real.sin (1 /. v_uCE_u94_x)))) (𝓝[≠] 0) (𝓝 0)))
  (h7 : (n > 1) → (Tendsto (fun v_uCE_u94_x : ℝ => (((f (0 + v_uCE_u94_x)) - (f (0 : ℝ))) /. v_uCE_u94_x)) (𝓝[≠] 0) (𝓝 0)))
  (h8 : ∃ L : ℝ, Tendsto (fun v_uCE_u94_x : ℝ => ((Real.rpow v_uCE_u94_x (n - 1)) * (Real.sin (1 /. v_uCE_u94_x)))) (𝓝[≠] 0) (𝓝 L))
  : (n > 1) → ((iteratedDeriv 1 (fun t => f t) 0) = 0) := by
  sorry

theorem proof_gap_exercise_992_2_5
  (f : (ℝ -> ℝ))
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((f x) = ((Real.rpow x n) * (Real.sin (1 /. x)))))))
  (h3 : (f (0 : ℝ)) = 0)
  (h4 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h5 : (n > 1) → (Tendsto (fun v_uCE_u94_x : ℝ => (((f (0 + v_uCE_u94_x)) - (f (0 : ℝ))) /. v_uCE_u94_x)) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun v_uCE_u94_x : ℝ => ((Real.rpow v_uCE_u94_x (n - 1)) * (Real.sin (1 /. v_uCE_u94_x))))))))
  (h6 : (n > 1) → (Tendsto (fun v_uCE_u94_x : ℝ => ((Real.rpow v_uCE_u94_x (n - 1)) * (Real.sin (1 /. v_uCE_u94_x)))) (𝓝[≠] 0) (𝓝 0)))
  (h7 : (n > 1) → (Tendsto (fun v_uCE_u94_x : ℝ => (((f (0 + v_uCE_u94_x)) - (f (0 : ℝ))) /. v_uCE_u94_x)) (𝓝[≠] 0) (𝓝 0)))
  (h8 : (n > 1) → ((iteratedDeriv 1 (fun t => f t) 0) = 0))
  (h9 : ∃ L : ℝ, Tendsto (fun v_uCE_u94_x : ℝ => ((Real.rpow v_uCE_u94_x (n - 1)) * (Real.sin (1 /. v_uCE_u94_x)))) (𝓝[≠] 0) (𝓝 L))
  : (n > 1) → (DifferentiableAt ℝ f 0) := by
  sorry

theorem proof_gap_exercise_992_2_6
  (f : (ℝ -> ℝ))
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((f x) = ((Real.rpow x n) * (Real.sin (1 /. x)))))))
  (h3 : (f (0 : ℝ)) = 0)
  (h4 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h5 : (n > 1) → (Tendsto (fun v_uCE_u94_x : ℝ => (((f (0 + v_uCE_u94_x)) - (f (0 : ℝ))) /. v_uCE_u94_x)) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun v_uCE_u94_x : ℝ => ((Real.rpow v_uCE_u94_x (n - 1)) * (Real.sin (1 /. v_uCE_u94_x))))))))
  (h6 : (n > 1) → (Tendsto (fun v_uCE_u94_x : ℝ => ((Real.rpow v_uCE_u94_x (n - 1)) * (Real.sin (1 /. v_uCE_u94_x)))) (𝓝[≠] 0) (𝓝 0)))
  (h7 : (n > 1) → (Tendsto (fun v_uCE_u94_x : ℝ => (((f (0 + v_uCE_u94_x)) - (f (0 : ℝ))) /. v_uCE_u94_x)) (𝓝[≠] 0) (𝓝 0)))
  (h8 : (n > 1) → ((iteratedDeriv 1 (fun t => f t) 0) = 0))
  (h9 : (n > 1) → (DifferentiableAt ℝ f 0))
  (h10 : ∃ L : ℝ, Tendsto (fun v_uCE_u94_x : ℝ => ((Real.rpow v_uCE_u94_x (n - 1)) * (Real.sin (1 /. v_uCE_u94_x)))) (𝓝[≠] 0) (𝓝 L))
  : (n ∈ ({n_1 | (n_1 ∈ (Set.univ : Set ℝ)) ∧ (n_1 > 1)})) ↔ (DifferentiableAt ℝ f 0) := by
  sorry

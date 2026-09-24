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

-- exercise: exercise_1000

theorem proof_gap_exercise_1000_1
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = |(x)|))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => f t) x) = (|(x)| /. x)))) := by
  sorry

theorem proof_gap_exercise_1000_2
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = |(x)|))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => f t) x) = (|(x)| /. x)))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((|(x)| /. x) = (SignType.sign x : ℝ)))) := by
  sorry

theorem proof_gap_exercise_1000_3
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = |(x)|))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => f t) x) = (|(x)| /. x)))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((|(x)| /. x) = (SignType.sign x : ℝ)))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => f t) x) = (SignType.sign x : ℝ)))) := by
  sorry

theorem proof_gap_exercise_1000_4
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = |(x)|))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => f t) x) = (|(x)| /. x)))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((|(x)| /. x) = (SignType.sign x : ℝ)))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => f t) x) = (SignType.sign x : ℝ)))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 0)) → (forall (v_uCE_u94_x : ℝ), (((v_uCE_u94_x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_u94_x ≠ 0)) → ((((f (0 + v_uCE_u94_x)) - (f (0 : ℝ))) /. v_uCE_u94_x) = (if (v_uCE_u94_x < 0) then (-(1 : ℝ)) else (if (v_uCE_u94_x > 0) then 1 else 1))))))) := by
  sorry

theorem proof_gap_exercise_1000_5
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = |(x)|))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => f t) x) = (|(x)| /. x)))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((|(x)| /. x) = (SignType.sign x : ℝ)))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => f t) x) = (SignType.sign x : ℝ)))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 0)) → (forall (v_uCE_u94_x : ℝ), (((v_uCE_u94_x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_u94_x ≠ 0)) → ((((f (0 + v_uCE_u94_x)) - (f (0 : ℝ))) /. v_uCE_u94_x) = (if (v_uCE_u94_x < 0) then (-(1 : ℝ)) else (if (v_uCE_u94_x > 0) then 1 else 1))))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 0)) → (Tendsto (fun v_uCE_u94_x : ℝ => (((f (0 + v_uCE_u94_x)) - (f (0 : ℝ))) /. v_uCE_u94_x)) (𝓝[>] 0) (𝓝 1)))) := by
  sorry

theorem proof_gap_exercise_1000_6
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = |(x)|))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => f t) x) = (|(x)| /. x)))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((|(x)| /. x) = (SignType.sign x : ℝ)))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => f t) x) = (SignType.sign x : ℝ)))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 0)) → (forall (v_uCE_u94_x : ℝ), (((v_uCE_u94_x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_u94_x ≠ 0)) → ((((f (0 + v_uCE_u94_x)) - (f (0 : ℝ))) /. v_uCE_u94_x) = (if (v_uCE_u94_x < 0) then (-(1 : ℝ)) else (if (v_uCE_u94_x > 0) then 1 else 1))))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 0)) → (Tendsto (fun v_uCE_u94_x : ℝ => (((f (0 + v_uCE_u94_x)) - (f (0 : ℝ))) /. v_uCE_u94_x)) (𝓝[>] 0) (𝓝 1)))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 0)) → (Tendsto (fun v_uCE_u94_x : ℝ => (((f (0 + v_uCE_u94_x)) - (f (0 : ℝ))) /. v_uCE_u94_x)) (𝓝[<] 0) (𝓝 (-(1 : ℝ)))))) := by
  sorry

theorem proof_gap_exercise_1000_7
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = |(x)|))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => f t) x) = (|(x)| /. x)))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((|(x)| /. x) = (SignType.sign x : ℝ)))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => f t) x) = (SignType.sign x : ℝ)))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 0)) → (forall (v_uCE_u94_x : ℝ), (((v_uCE_u94_x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_u94_x ≠ 0)) → ((((f (0 + v_uCE_u94_x)) - (f (0 : ℝ))) /. v_uCE_u94_x) = (if (v_uCE_u94_x < 0) then (-(1 : ℝ)) else (if (v_uCE_u94_x > 0) then 1 else 1))))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 0)) → (Tendsto (fun v_uCE_u94_x : ℝ => (((f (0 + v_uCE_u94_x)) - (f (0 : ℝ))) /. v_uCE_u94_x)) (𝓝[>] 0) (𝓝 1)))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 0)) → (Tendsto (fun v_uCE_u94_x : ℝ => (((f (0 + v_uCE_u94_x)) - (f (0 : ℝ))) /. v_uCE_u94_x)) (𝓝[<] 0) (𝓝 (-(1 : ℝ)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 0)) → (Not (DifferentiableAt ℝ f 0)))) := by
  sorry

theorem proof_gap_exercise_1000_8
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = |(x)|))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => f t) x) = (|(x)| /. x)))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((|(x)| /. x) = (SignType.sign x : ℝ)))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => f t) x) = (SignType.sign x : ℝ)))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 0)) → (forall (v_uCE_u94_x : ℝ), (((v_uCE_u94_x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_u94_x ≠ 0)) → ((((f (0 + v_uCE_u94_x)) - (f (0 : ℝ))) /. v_uCE_u94_x) = (if (v_uCE_u94_x < 0) then (-(1 : ℝ)) else (if (v_uCE_u94_x > 0) then 1 else 1))))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 0)) → (Tendsto (fun v_uCE_u94_x : ℝ => (((f (0 + v_uCE_u94_x)) - (f (0 : ℝ))) /. v_uCE_u94_x)) (𝓝[>] 0) (𝓝 1)))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 0)) → (Tendsto (fun v_uCE_u94_x : ℝ => (((f (0 + v_uCE_u94_x)) - (f (0 : ℝ))) /. v_uCE_u94_x)) (𝓝[<] 0) (𝓝 (-(1 : ℝ)))))))
  (h8 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 0)) → (Not (DifferentiableAt ℝ f 0)))))
  : (fun (x1 : ℝ) => (iteratedDeriv 1 (fun t => f t) x1)) = (fun (x : ℝ) => (if (x ≠ 0) then (SignType.sign x : ℝ) else (SignType.sign x : ℝ))) := by
  sorry

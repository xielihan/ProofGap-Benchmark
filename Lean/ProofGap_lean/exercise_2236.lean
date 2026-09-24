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

-- exercise: exercise_2236

theorem proof_gap_exercise_2236_1
  (f : (ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (h1 : ContinuousOn f (Set.Ici 0))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ici 0))) → ((f x) > 0))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((v_uCF_u86 x) = ((∫ t in (0 : ℝ)..x, ((t * (f t)) * (1 : ℝ))) /. (∫ t in (0 : ℝ)..x, ((f t) * (1 : ℝ))))))))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => ((x * (f x)) /. (f x))) (𝓝[>] 0) (𝓝 L) ∧ (Tendsto (fun x : ℝ => (v_uCF_u86 x)) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x : ℝ => ((x * (f x)) /. (f x))))))) := by
  sorry

theorem proof_gap_exercise_2236_2
  (f : (ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (h1 : ContinuousOn f (Set.Ici 0))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ici 0))) → ((f x) > 0))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((v_uCF_u86 x) = ((∫ t in (0 : ℝ)..x, ((t * (f t)) * (1 : ℝ))) /. (∫ t in (0 : ℝ)..x, ((f t) * (1 : ℝ))))))))
  (h4 : Tendsto (fun x : ℝ => (v_uCF_u86 x)) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x : ℝ => ((x * (f x)) /. (f x))))))
  (h5 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((x * (f x)) /. (f x))) (𝓝[>] 0) (𝓝 L))
  : Tendsto (fun x : ℝ => ((x * (f x)) /. (f x))) (𝓝[>] 0) (𝓝 0) := by
  sorry

theorem proof_gap_exercise_2236_3
  (f : (ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (h1 : ContinuousOn f (Set.Ici 0))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ici 0))) → ((f x) > 0))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((v_uCF_u86 x) = ((∫ t in (0 : ℝ)..x, ((t * (f t)) * (1 : ℝ))) /. (∫ t in (0 : ℝ)..x, ((f t) * (1 : ℝ))))))))
  (h4 : Tendsto (fun x : ℝ => (v_uCF_u86 x)) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x : ℝ => ((x * (f x)) /. (f x))))))
  (h5 : Tendsto (fun x : ℝ => ((x * (f x)) /. (f x))) (𝓝[>] 0) (𝓝 0))
  (h6 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((x * (f x)) /. (f x))) (𝓝[>] 0) (𝓝 L))
  : Tendsto (fun x : ℝ => (v_uCF_u86 x)) (𝓝[>] 0) (𝓝 0) := by
  sorry

theorem proof_gap_exercise_2236_4
  (f : (ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (h1 : ContinuousOn f (Set.Ici 0))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ici 0))) → ((f x) > 0))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((v_uCF_u86 x) = ((∫ t in (0 : ℝ)..x, ((t * (f t)) * (1 : ℝ))) /. (∫ t in (0 : ℝ)..x, ((f t) * (1 : ℝ))))))))
  (h4 : Tendsto (fun x : ℝ => (v_uCF_u86 x)) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x : ℝ => ((x * (f x)) /. (f x))))))
  (h5 : Tendsto (fun x : ℝ => ((x * (f x)) /. (f x))) (𝓝[>] 0) (𝓝 0))
  (h6 : Tendsto (fun x : ℝ => (v_uCF_u86 x)) (𝓝[>] 0) (𝓝 0))
  (h7 : (v_uCF_u86 (0 : ℝ)) = 0)
  (h8 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((x * (f x)) /. (f x))) (𝓝[>] 0) (𝓝 L))
  : ContinuousOn v_uCF_u86 (Set.Ici 0) := by
  sorry

theorem proof_gap_exercise_2236_5
  (f : (ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (h1 : ContinuousOn f (Set.Ici 0))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ici 0))) → ((f x) > 0))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((v_uCF_u86 x) = ((∫ t in (0 : ℝ)..x, ((t * (f t)) * (1 : ℝ))) /. (∫ t in (0 : ℝ)..x, ((f t) * (1 : ℝ))))))))
  (h4 : Tendsto (fun x : ℝ => (v_uCF_u86 x)) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x : ℝ => ((x * (f x)) /. (f x))))))
  (h5 : Tendsto (fun x : ℝ => ((x * (f x)) /. (f x))) (𝓝[>] 0) (𝓝 0))
  (h6 : Tendsto (fun x : ℝ => (v_uCF_u86 x)) (𝓝[>] 0) (𝓝 0))
  (h7 : (v_uCF_u86 (0 : ℝ)) = 0)
  (h8 : ContinuousOn v_uCF_u86 (Set.Ici 0))
  (h9 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((x * (f x)) /. (f x))) (𝓝[>] 0) (𝓝 L))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 1 (fun t_1 => v_uCF_u86 t_1) x) = ((1 /. ((∫ t in (0 : ℝ)..x, ((f t) * (1 : ℝ))) ^ (2 : ℕ))) * (((x * (f x)) * (∫ t in (0 : ℝ)..x, ((f t) * (1 : ℝ)))) - ((f x) * (∫ t in (0 : ℝ)..x, ((t * (f t)) * (1 : ℝ))))))))) := by
  sorry

theorem proof_gap_exercise_2236_6
  (f : (ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (h1 : ContinuousOn f (Set.Ici 0))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ici 0))) → ((f x) > 0))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((v_uCF_u86 x) = ((∫ t in (0 : ℝ)..x, ((t * (f t)) * (1 : ℝ))) /. (∫ t in (0 : ℝ)..x, ((f t) * (1 : ℝ))))))))
  (h4 : Tendsto (fun x : ℝ => (v_uCF_u86 x)) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x : ℝ => ((x * (f x)) /. (f x))))))
  (h5 : Tendsto (fun x : ℝ => ((x * (f x)) /. (f x))) (𝓝[>] 0) (𝓝 0))
  (h6 : Tendsto (fun x : ℝ => (v_uCF_u86 x)) (𝓝[>] 0) (𝓝 0))
  (h7 : (v_uCF_u86 (0 : ℝ)) = 0)
  (h8 : ContinuousOn v_uCF_u86 (Set.Ici 0))
  (h9 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 1 (fun t_1 => v_uCF_u86 t_1) x) = ((1 /. ((∫ t in (0 : ℝ)..x, ((f t) * (1 : ℝ))) ^ (2 : ℕ))) * (((x * (f x)) * (∫ t in (0 : ℝ)..x, ((f t) * (1 : ℝ)))) - ((f x) * (∫ t in (0 : ℝ)..x, ((t * (f t)) * (1 : ℝ))))))))))
  (h10 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((x * (f x)) /. (f x))) (𝓝[>] 0) (𝓝 L))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 1 (fun t_1 => v_uCF_u86 t_1) x) = (((f x) /. ((∫ t in (0 : ℝ)..x, ((f t) * (1 : ℝ))) ^ (2 : ℕ))) * (∫ t in (0 : ℝ)..x, (((x - t) * (f t)) * (1 : ℝ))))))) := by
  sorry

theorem proof_gap_exercise_2236_7
  (f : (ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (h1 : ContinuousOn f (Set.Ici 0))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ici 0))) → ((f x) > 0))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((v_uCF_u86 x) = ((∫ t in (0 : ℝ)..x, ((t * (f t)) * (1 : ℝ))) /. (∫ t in (0 : ℝ)..x, ((f t) * (1 : ℝ))))))))
  (h4 : Tendsto (fun x : ℝ => (v_uCF_u86 x)) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x : ℝ => ((x * (f x)) /. (f x))))))
  (h5 : Tendsto (fun x : ℝ => ((x * (f x)) /. (f x))) (𝓝[>] 0) (𝓝 0))
  (h6 : Tendsto (fun x : ℝ => (v_uCF_u86 x)) (𝓝[>] 0) (𝓝 0))
  (h7 : (v_uCF_u86 (0 : ℝ)) = 0)
  (h8 : ContinuousOn v_uCF_u86 (Set.Ici 0))
  (h9 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 1 (fun t_1 => v_uCF_u86 t_1) x) = ((1 /. ((∫ t in (0 : ℝ)..x, ((f t) * (1 : ℝ))) ^ (2 : ℕ))) * (((x * (f x)) * (∫ t in (0 : ℝ)..x, ((f t) * (1 : ℝ)))) - ((f x) * (∫ t in (0 : ℝ)..x, ((t * (f t)) * (1 : ℝ))))))))))
  (h10 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 1 (fun t_1 => v_uCF_u86 t_1) x) = (((f x) /. ((∫ t in (0 : ℝ)..x, ((f t) * (1 : ℝ))) ^ (2 : ℕ))) * (∫ t in (0 : ℝ)..x, (((x - t) * (f t)) * (1 : ℝ))))))))
  (h11 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((x * (f x)) /. (f x))) (𝓝[>] 0) (𝓝 L))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((∫ t in (0 : ℝ)..x, (((x - t) * (f t)) * (1 : ℝ))) > 0))) := by
  sorry

theorem proof_gap_exercise_2236_8
  (f : (ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (h1 : ContinuousOn f (Set.Ici 0))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ici 0))) → ((f x) > 0))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((v_uCF_u86 x) = ((∫ t in (0 : ℝ)..x, ((t * (f t)) * (1 : ℝ))) /. (∫ t in (0 : ℝ)..x, ((f t) * (1 : ℝ))))))))
  (h4 : Tendsto (fun x : ℝ => (v_uCF_u86 x)) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x : ℝ => ((x * (f x)) /. (f x))))))
  (h5 : Tendsto (fun x : ℝ => ((x * (f x)) /. (f x))) (𝓝[>] 0) (𝓝 0))
  (h6 : Tendsto (fun x : ℝ => (v_uCF_u86 x)) (𝓝[>] 0) (𝓝 0))
  (h7 : (v_uCF_u86 (0 : ℝ)) = 0)
  (h8 : ContinuousOn v_uCF_u86 (Set.Ici 0))
  (h9 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 1 (fun t_1 => v_uCF_u86 t_1) x) = ((1 /. ((∫ t in (0 : ℝ)..x, ((f t) * (1 : ℝ))) ^ (2 : ℕ))) * (((x * (f x)) * (∫ t in (0 : ℝ)..x, ((f t) * (1 : ℝ)))) - ((f x) * (∫ t in (0 : ℝ)..x, ((t * (f t)) * (1 : ℝ))))))))))
  (h10 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 1 (fun t_1 => v_uCF_u86 t_1) x) = (((f x) /. ((∫ t in (0 : ℝ)..x, ((f t) * (1 : ℝ))) ^ (2 : ℕ))) * (∫ t in (0 : ℝ)..x, (((x - t) * (f t)) * (1 : ℝ))))))))
  (h11 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((∫ t in (0 : ℝ)..x, (((x - t) * (f t)) * (1 : ℝ))) > 0))))
  (h12 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((x * (f x)) /. (f x))) (𝓝[>] 0) (𝓝 L))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 1 (fun t_1 => v_uCF_u86 t_1) x) > 0))) := by
  sorry

theorem proof_gap_exercise_2236_9
  (f : (ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (h1 : ContinuousOn f (Set.Ici 0))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ici 0))) → ((f x) > 0))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((v_uCF_u86 x) = ((∫ t in (0 : ℝ)..x, ((t * (f t)) * (1 : ℝ))) /. (∫ t in (0 : ℝ)..x, ((f t) * (1 : ℝ))))))))
  (h4 : Tendsto (fun x : ℝ => (v_uCF_u86 x)) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x : ℝ => ((x * (f x)) /. (f x))))))
  (h5 : Tendsto (fun x : ℝ => ((x * (f x)) /. (f x))) (𝓝[>] 0) (𝓝 0))
  (h6 : Tendsto (fun x : ℝ => (v_uCF_u86 x)) (𝓝[>] 0) (𝓝 0))
  (h7 : (v_uCF_u86 (0 : ℝ)) = 0)
  (h8 : ContinuousOn v_uCF_u86 (Set.Ici 0))
  (h9 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 1 (fun t_1 => v_uCF_u86 t_1) x) = ((1 /. ((∫ t in (0 : ℝ)..x, ((f t) * (1 : ℝ))) ^ (2 : ℕ))) * (((x * (f x)) * (∫ t in (0 : ℝ)..x, ((f t) * (1 : ℝ)))) - ((f x) * (∫ t in (0 : ℝ)..x, ((t * (f t)) * (1 : ℝ))))))))))
  (h10 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 1 (fun t_1 => v_uCF_u86 t_1) x) = (((f x) /. ((∫ t in (0 : ℝ)..x, ((f t) * (1 : ℝ))) ^ (2 : ℕ))) * (∫ t in (0 : ℝ)..x, (((x - t) * (f t)) * (1 : ℝ))))))))
  (h11 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((∫ t in (0 : ℝ)..x, (((x - t) * (f t)) * (1 : ℝ))) > 0))))
  (h12 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 1 (fun t_1 => v_uCF_u86 t_1) x) > 0))))
  (h13 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((x * (f x)) /. (f x))) (𝓝[>] 0) (𝓝 L))
  : MonotoneOn v_uCF_u86 (Set.Ici 0) := by
  sorry

theorem proof_gap_exercise_2236_10
  (f : (ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (h1 : ContinuousOn f (Set.Ici 0))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ici 0))) → ((f x) > 0))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((v_uCF_u86 x) = ((∫ t in (0 : ℝ)..x, ((t * (f t)) * (1 : ℝ))) /. (∫ t in (0 : ℝ)..x, ((f t) * (1 : ℝ))))))))
  (h4 : Tendsto (fun x : ℝ => (v_uCF_u86 x)) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x : ℝ => ((x * (f x)) /. (f x))))))
  (h5 : Tendsto (fun x : ℝ => ((x * (f x)) /. (f x))) (𝓝[>] 0) (𝓝 0))
  (h6 : Tendsto (fun x : ℝ => (v_uCF_u86 x)) (𝓝[>] 0) (𝓝 0))
  (h7 : (v_uCF_u86 (0 : ℝ)) = 0)
  (h8 : ContinuousOn v_uCF_u86 (Set.Ici 0))
  (h9 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 1 (fun t_1 => v_uCF_u86 t_1) x) = ((1 /. ((∫ t in (0 : ℝ)..x, ((f t) * (1 : ℝ))) ^ (2 : ℕ))) * (((x * (f x)) * (∫ t in (0 : ℝ)..x, ((f t) * (1 : ℝ)))) - ((f x) * (∫ t in (0 : ℝ)..x, ((t * (f t)) * (1 : ℝ))))))))))
  (h10 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 1 (fun t_1 => v_uCF_u86 t_1) x) = (((f x) /. ((∫ t in (0 : ℝ)..x, ((f t) * (1 : ℝ))) ^ (2 : ℕ))) * (∫ t in (0 : ℝ)..x, (((x - t) * (f t)) * (1 : ℝ))))))))
  (h11 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((∫ t in (0 : ℝ)..x, (((x - t) * (f t)) * (1 : ℝ))) > 0))))
  (h12 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 1 (fun t_1 => v_uCF_u86 t_1) x) > 0))))
  (h13 : MonotoneOn v_uCF_u86 (Set.Ici 0))
  (h14 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((x * (f x)) /. (f x))) (𝓝[>] 0) (𝓝 L))
  : MonotoneOn v_uCF_u86 (Set.Ici 0) := by
  sorry

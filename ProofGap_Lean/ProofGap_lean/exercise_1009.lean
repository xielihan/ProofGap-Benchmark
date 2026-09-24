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

-- exercise: exercise_1009

theorem proof_gap_exercise_1009_1
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (if (x ≠ 0) then (x * (Real.sin (1 /. x))) else (if (x = 0) then 0 else 0))))))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => (x * (Real.sin (1 /. x)))) (𝓝[≠] 0) (𝓝 L) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (x * (Real.sin (1 /. x)))))))) := by
  sorry

theorem proof_gap_exercise_1009_2
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (if (x ≠ 0) then (x * (Real.sin (1 /. x))) else (if (x = 0) then 0 else 0))))))
  (h2 : Tendsto (fun x : ℝ => (f x)) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (x * (Real.sin (1 /. x)))))))
  (h3 : ∃ L : ℝ, Tendsto (fun x : ℝ => (x * (Real.sin (1 /. x)))) (𝓝[≠] 0) (𝓝 L))
  : Tendsto (fun x : ℝ => (x * (Real.sin (1 /. x)))) (𝓝[≠] 0) (𝓝 0) := by
  sorry

theorem proof_gap_exercise_1009_3
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (if (x ≠ 0) then (x * (Real.sin (1 /. x))) else (if (x = 0) then 0 else 0))))))
  (h2 : Tendsto (fun x : ℝ => (f x)) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (x * (Real.sin (1 /. x)))))))
  (h3 : Tendsto (fun x : ℝ => (x * (Real.sin (1 /. x)))) (𝓝[≠] 0) (𝓝 0))
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => (x * (Real.sin (1 /. x)))) (𝓝[≠] 0) (𝓝 L))
  : 0 = (f (0 : ℝ)) := by
  sorry

theorem proof_gap_exercise_1009_4
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (if (x ≠ 0) then (x * (Real.sin (1 /. x))) else (if (x = 0) then 0 else 0))))))
  (h2 : Tendsto (fun x : ℝ => (f x)) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (x * (Real.sin (1 /. x)))))))
  (h3 : Tendsto (fun x : ℝ => (x * (Real.sin (1 /. x)))) (𝓝[≠] 0) (𝓝 0))
  (h4 : 0 = (f (0 : ℝ)))
  (h5 : ∃ L : ℝ, Tendsto (fun x : ℝ => (x * (Real.sin (1 /. x)))) (𝓝[≠] 0) (𝓝 L))
  : Tendsto (fun x : ℝ => (f x)) (𝓝[≠] 0) (𝓝 (f (0 : ℝ))) := by
  sorry

theorem proof_gap_exercise_1009_5
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (if (x ≠ 0) then (x * (Real.sin (1 /. x))) else (if (x = 0) then 0 else 0))))))
  (h2 : Tendsto (fun x : ℝ => (f x)) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (x * (Real.sin (1 /. x)))))))
  (h3 : Tendsto (fun x : ℝ => (x * (Real.sin (1 /. x)))) (𝓝[≠] 0) (𝓝 0))
  (h4 : 0 = (f (0 : ℝ)))
  (h5 : Tendsto (fun x : ℝ => (f x)) (𝓝[≠] 0) (𝓝 (f (0 : ℝ))))
  (h6 : ∃ L : ℝ, Tendsto (fun x : ℝ => (x * (Real.sin (1 /. x)))) (𝓝[≠] 0) (𝓝 L))
  : ContinuousAt f 0 := by
  sorry

theorem proof_gap_exercise_1009_6
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (if (x ≠ 0) then (x * (Real.sin (1 /. x))) else (if (x = 0) then 0 else 0))))))
  (h2 : Tendsto (fun x : ℝ => (f x)) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (x * (Real.sin (1 /. x)))))))
  (h3 : Tendsto (fun x : ℝ => (x * (Real.sin (1 /. x)))) (𝓝[≠] 0) (𝓝 0))
  (h4 : 0 = (f (0 : ℝ)))
  (h5 : Tendsto (fun x : ℝ => (f x)) (𝓝[≠] 0) (𝓝 (f (0 : ℝ))))
  (h6 : ContinuousAt f 0)
  (h7 : ∃ L : ℝ, Tendsto (fun x : ℝ => (x * (Real.sin (1 /. x)))) (𝓝[≠] 0) (𝓝 L))
  : (forall (v_uCE_u94_x : ℝ), (((v_uCE_u94_x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_u94_x ≠ 0)) → ((((f (0 + v_uCE_u94_x)) - (f (0 : ℝ))) /. v_uCE_u94_x) = (Real.sin (1 /. v_uCE_u94_x))))) := by
  sorry

theorem proof_gap_exercise_1009_7
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (if (x ≠ 0) then (x * (Real.sin (1 /. x))) else (if (x = 0) then 0 else 0))))))
  (h2 : Tendsto (fun x : ℝ => (f x)) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (x * (Real.sin (1 /. x)))))))
  (h3 : Tendsto (fun x : ℝ => (x * (Real.sin (1 /. x)))) (𝓝[≠] 0) (𝓝 0))
  (h4 : 0 = (f (0 : ℝ)))
  (h5 : Tendsto (fun x : ℝ => (f x)) (𝓝[≠] 0) (𝓝 (f (0 : ℝ))))
  (h6 : ContinuousAt f 0)
  (h7 : (forall (v_uCE_u94_x : ℝ), (((v_uCE_u94_x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_u94_x ≠ 0)) → ((((f (0 + v_uCE_u94_x)) - (f (0 : ℝ))) /. v_uCE_u94_x) = (Real.sin (1 /. v_uCE_u94_x))))))
  (h8 : ∃ L_1 : ℝ, Tendsto (fun x : ℝ => (x * (Real.sin (1 /. x)))) (𝓝[≠] 0) (𝓝 L_1))
  : Not (exists (L : ℝ), ((L ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun v_uCE_u94_x : ℝ => (Real.sin (1 /. v_uCE_u94_x))) (𝓝[<] 0) (𝓝 L)))) := by
  sorry

theorem proof_gap_exercise_1009_8
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (if (x ≠ 0) then (x * (Real.sin (1 /. x))) else (if (x = 0) then 0 else 0))))))
  (h2 : Tendsto (fun x : ℝ => (f x)) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (x * (Real.sin (1 /. x)))))))
  (h3 : Tendsto (fun x : ℝ => (x * (Real.sin (1 /. x)))) (𝓝[≠] 0) (𝓝 0))
  (h4 : 0 = (f (0 : ℝ)))
  (h5 : Tendsto (fun x : ℝ => (f x)) (𝓝[≠] 0) (𝓝 (f (0 : ℝ))))
  (h6 : ContinuousAt f 0)
  (h7 : (forall (v_uCE_u94_x : ℝ), (((v_uCE_u94_x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_u94_x ≠ 0)) → ((((f (0 + v_uCE_u94_x)) - (f (0 : ℝ))) /. v_uCE_u94_x) = (Real.sin (1 /. v_uCE_u94_x))))))
  (h8 : Not (exists (L : ℝ), ((L ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun v_uCE_u94_x : ℝ => (Real.sin (1 /. v_uCE_u94_x))) (𝓝[<] 0) (𝓝 L)))))
  (h9 : ∃ L_1 : ℝ, Tendsto (fun x : ℝ => (x * (Real.sin (1 /. x)))) (𝓝[≠] 0) (𝓝 L_1))
  : Not (exists (L : ℝ), ((L ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun v_uCE_u94_x : ℝ => (Real.sin (1 /. v_uCE_u94_x))) (𝓝[>] 0) (𝓝 L)))) := by
  sorry

theorem proof_gap_exercise_1009_9
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (if (x ≠ 0) then (x * (Real.sin (1 /. x))) else (if (x = 0) then 0 else 0))))))
  (h2 : Tendsto (fun x : ℝ => (f x)) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (x * (Real.sin (1 /. x)))))))
  (h3 : Tendsto (fun x : ℝ => (x * (Real.sin (1 /. x)))) (𝓝[≠] 0) (𝓝 0))
  (h4 : 0 = (f (0 : ℝ)))
  (h5 : Tendsto (fun x : ℝ => (f x)) (𝓝[≠] 0) (𝓝 (f (0 : ℝ))))
  (h6 : ContinuousAt f 0)
  (h7 : (forall (v_uCE_u94_x : ℝ), (((v_uCE_u94_x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_u94_x ≠ 0)) → ((((f (0 + v_uCE_u94_x)) - (f (0 : ℝ))) /. v_uCE_u94_x) = (Real.sin (1 /. v_uCE_u94_x))))))
  (h8 : Not (exists (L : ℝ), ((L ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun v_uCE_u94_x : ℝ => (Real.sin (1 /. v_uCE_u94_x))) (𝓝[<] 0) (𝓝 L)))))
  (h9 : Not (exists (L : ℝ), ((L ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun v_uCE_u94_x : ℝ => (Real.sin (1 /. v_uCE_u94_x))) (𝓝[>] 0) (𝓝 L)))))
  (h10 : ∃ L_1 : ℝ, Tendsto (fun x : ℝ => (x * (Real.sin (1 /. x)))) (𝓝[≠] 0) (𝓝 L_1))
  : Not (DifferentiableWithinAt ℝ f (Set.Iio 0) 0) := by
  sorry

theorem proof_gap_exercise_1009_10
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (if (x ≠ 0) then (x * (Real.sin (1 /. x))) else (if (x = 0) then 0 else 0))))))
  (h2 : Tendsto (fun x : ℝ => (f x)) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (x * (Real.sin (1 /. x)))))))
  (h3 : Tendsto (fun x : ℝ => (x * (Real.sin (1 /. x)))) (𝓝[≠] 0) (𝓝 0))
  (h4 : 0 = (f (0 : ℝ)))
  (h5 : Tendsto (fun x : ℝ => (f x)) (𝓝[≠] 0) (𝓝 (f (0 : ℝ))))
  (h6 : ContinuousAt f 0)
  (h7 : (forall (v_uCE_u94_x : ℝ), (((v_uCE_u94_x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_u94_x ≠ 0)) → ((((f (0 + v_uCE_u94_x)) - (f (0 : ℝ))) /. v_uCE_u94_x) = (Real.sin (1 /. v_uCE_u94_x))))))
  (h8 : Not (exists (L : ℝ), ((L ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun v_uCE_u94_x : ℝ => (Real.sin (1 /. v_uCE_u94_x))) (𝓝[<] 0) (𝓝 L)))))
  (h9 : Not (exists (L : ℝ), ((L ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun v_uCE_u94_x : ℝ => (Real.sin (1 /. v_uCE_u94_x))) (𝓝[>] 0) (𝓝 L)))))
  (h10 : Not (DifferentiableWithinAt ℝ f (Set.Iio 0) 0))
  (h11 : ∃ L_1 : ℝ, Tendsto (fun x : ℝ => (x * (Real.sin (1 /. x)))) (𝓝[≠] 0) (𝓝 L_1))
  : Not (DifferentiableWithinAt ℝ f (Set.Ioi 0) 0) := by
  sorry

theorem proof_gap_exercise_1009_11
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (if (x ≠ 0) then (x * (Real.sin (1 /. x))) else (if (x = 0) then 0 else 0))))))
  (h2 : Tendsto (fun x : ℝ => (f x)) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (x * (Real.sin (1 /. x)))))))
  (h3 : Tendsto (fun x : ℝ => (x * (Real.sin (1 /. x)))) (𝓝[≠] 0) (𝓝 0))
  (h4 : 0 = (f (0 : ℝ)))
  (h5 : Tendsto (fun x : ℝ => (f x)) (𝓝[≠] 0) (𝓝 (f (0 : ℝ))))
  (h6 : ContinuousAt f 0)
  (h7 : (forall (v_uCE_u94_x : ℝ), (((v_uCE_u94_x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_u94_x ≠ 0)) → ((((f (0 + v_uCE_u94_x)) - (f (0 : ℝ))) /. v_uCE_u94_x) = (Real.sin (1 /. v_uCE_u94_x))))))
  (h8 : Not (exists (L : ℝ), ((L ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun v_uCE_u94_x : ℝ => (Real.sin (1 /. v_uCE_u94_x))) (𝓝[<] 0) (𝓝 L)))))
  (h9 : Not (exists (L : ℝ), ((L ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun v_uCE_u94_x : ℝ => (Real.sin (1 /. v_uCE_u94_x))) (𝓝[>] 0) (𝓝 L)))))
  (h10 : Not (DifferentiableWithinAt ℝ f (Set.Iio 0) 0))
  (h11 : Not (DifferentiableWithinAt ℝ f (Set.Ioi 0) 0))
  (h12 : ∃ L_1 : ℝ, Tendsto (fun x : ℝ => (x * (Real.sin (1 /. x)))) (𝓝[≠] 0) (𝓝 L_1))
  : ((ContinuousAt f 0) ∧ (Not (DifferentiableWithinAt ℝ f (Set.Iio 0) 0))) ∧ (Not (DifferentiableWithinAt ℝ f (Set.Ioi 0) 0)) := by
  sorry

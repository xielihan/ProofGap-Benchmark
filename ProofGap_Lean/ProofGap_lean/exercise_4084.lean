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

-- exercise: exercise_4084

theorem proof_gap_exercise_4084_1
  (f : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : x ≥ 0)
  (h3 : ContinuousOn f (Set.Icc 0 x))
  : (forall (v_uCE_uBE : ℝ), ((v_uCE_uBE ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB7 : ℝ), ((v_uCE_uB7 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB6 : ℝ), ((v_uCE_uB6 ∈ (Set.univ : Set ℝ)) → ((∫ v_uCE_uBE_1 in (0 : ℝ)..x, ((∫ v_uCE_uB7_1 in (0 : ℝ)..v_uCE_uBE_1, ((∫ v_uCE_uB6_1 in (0 : ℝ)..v_uCE_uB7_1, ((f v_uCE_uB6_1) * (1 : ℝ))) * (1 : ℝ))) * (1 : ℝ))) = (∫ v_uCE_uBE_1 in (0 : ℝ)..x, ((∫ v_uCE_uB6_1 in (0 : ℝ)..v_uCE_uBE_1, ((∫ v_uCE_uB7_1 in v_uCE_uB6_1..v_uCE_uBE_1, ((f v_uCE_uB6_1) * (1 : ℝ))) * (1 : ℝ))) * (1 : ℝ)))))))))) := by
  sorry

theorem proof_gap_exercise_4084_2
  (f : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : x ≥ 0)
  (h3 : ContinuousOn f (Set.Icc 0 x))
  (h4 : (forall (v_uCE_uBE : ℝ), ((v_uCE_uBE ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB7 : ℝ), ((v_uCE_uB7 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB6 : ℝ), ((v_uCE_uB6 ∈ (Set.univ : Set ℝ)) → ((∫ v_uCE_uBE_1 in (0 : ℝ)..x, ((∫ v_uCE_uB7_1 in (0 : ℝ)..v_uCE_uBE_1, ((∫ v_uCE_uB6_1 in (0 : ℝ)..v_uCE_uB7_1, ((f v_uCE_uB6_1) * (1 : ℝ))) * (1 : ℝ))) * (1 : ℝ))) = (∫ v_uCE_uBE_1 in (0 : ℝ)..x, ((∫ v_uCE_uB6_1 in (0 : ℝ)..v_uCE_uBE_1, ((∫ v_uCE_uB7_1 in v_uCE_uB6_1..v_uCE_uBE_1, ((f v_uCE_uB6_1) * (1 : ℝ))) * (1 : ℝ))) * (1 : ℝ)))))))))))
  : (forall (v_uCE_uBE : ℝ), ((v_uCE_uBE ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB6 : ℝ), ((v_uCE_uB6 ∈ (Set.univ : Set ℝ)) → ((∫ v_uCE_uBE_1 in (0 : ℝ)..x, ((∫ v_uCE_uB6_1 in (0 : ℝ)..v_uCE_uBE_1, ((∫ v_uCE_uB7 in v_uCE_uB6_1..v_uCE_uBE_1, ((f v_uCE_uB6_1) * (1 : ℝ))) * (1 : ℝ))) * (1 : ℝ))) = (∫ v_uCE_uBE_1 in (0 : ℝ)..x, ((∫ v_uCE_uB6_1 in (0 : ℝ)..v_uCE_uBE_1, (((f v_uCE_uB6_1) * (v_uCE_uBE_1 - v_uCE_uB6_1)) * (1 : ℝ))) * (1 : ℝ)))))))) := by
  sorry

theorem proof_gap_exercise_4084_3
  (f : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : x ≥ 0)
  (h3 : ContinuousOn f (Set.Icc 0 x))
  (h4 : (forall (v_uCE_uBE : ℝ), ((v_uCE_uBE ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB7 : ℝ), ((v_uCE_uB7 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB6 : ℝ), ((v_uCE_uB6 ∈ (Set.univ : Set ℝ)) → ((∫ v_uCE_uBE_1 in (0 : ℝ)..x, ((∫ v_uCE_uB7_1 in (0 : ℝ)..v_uCE_uBE_1, ((∫ v_uCE_uB6_1 in (0 : ℝ)..v_uCE_uB7_1, ((f v_uCE_uB6_1) * (1 : ℝ))) * (1 : ℝ))) * (1 : ℝ))) = (∫ v_uCE_uBE_1 in (0 : ℝ)..x, ((∫ v_uCE_uB6_1 in (0 : ℝ)..v_uCE_uBE_1, ((∫ v_uCE_uB7_1 in v_uCE_uB6_1..v_uCE_uBE_1, ((f v_uCE_uB6_1) * (1 : ℝ))) * (1 : ℝ))) * (1 : ℝ)))))))))))
  (h5 : (forall (v_uCE_uBE : ℝ), ((v_uCE_uBE ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB6 : ℝ), ((v_uCE_uB6 ∈ (Set.univ : Set ℝ)) → ((∫ v_uCE_uBE_1 in (0 : ℝ)..x, ((∫ v_uCE_uB6_1 in (0 : ℝ)..v_uCE_uBE_1, ((∫ v_uCE_uB7 in v_uCE_uB6_1..v_uCE_uBE_1, ((f v_uCE_uB6_1) * (1 : ℝ))) * (1 : ℝ))) * (1 : ℝ))) = (∫ v_uCE_uBE_1 in (0 : ℝ)..x, ((∫ v_uCE_uB6_1 in (0 : ℝ)..v_uCE_uBE_1, (((f v_uCE_uB6_1) * (v_uCE_uBE_1 - v_uCE_uB6_1)) * (1 : ℝ))) * (1 : ℝ)))))))))
  : (forall (v_uCE_uBE : ℝ), ((v_uCE_uBE ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB6 : ℝ), ((v_uCE_uB6 ∈ (Set.univ : Set ℝ)) → ((∫ v_uCE_uBE_1 in (0 : ℝ)..x, ((∫ v_uCE_uB6_1 in (0 : ℝ)..v_uCE_uBE_1, (((f v_uCE_uB6_1) * (v_uCE_uBE_1 - v_uCE_uB6_1)) * (1 : ℝ))) * (1 : ℝ))) = (∫ v_uCE_uB6_1 in (0 : ℝ)..x, ((∫ v_uCE_uBE_1 in v_uCE_uB6_1..x, (((f v_uCE_uB6_1) * (v_uCE_uBE_1 - v_uCE_uB6_1)) * (1 : ℝ))) * (1 : ℝ)))))))) := by
  sorry

theorem proof_gap_exercise_4084_4
  (f : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : x ≥ 0)
  (h3 : ContinuousOn f (Set.Icc 0 x))
  (h4 : (forall (v_uCE_uBE : ℝ), ((v_uCE_uBE ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB7 : ℝ), ((v_uCE_uB7 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB6 : ℝ), ((v_uCE_uB6 ∈ (Set.univ : Set ℝ)) → ((∫ v_uCE_uBE_1 in (0 : ℝ)..x, ((∫ v_uCE_uB7_1 in (0 : ℝ)..v_uCE_uBE_1, ((∫ v_uCE_uB6_1 in (0 : ℝ)..v_uCE_uB7_1, ((f v_uCE_uB6_1) * (1 : ℝ))) * (1 : ℝ))) * (1 : ℝ))) = (∫ v_uCE_uBE_1 in (0 : ℝ)..x, ((∫ v_uCE_uB6_1 in (0 : ℝ)..v_uCE_uBE_1, ((∫ v_uCE_uB7_1 in v_uCE_uB6_1..v_uCE_uBE_1, ((f v_uCE_uB6_1) * (1 : ℝ))) * (1 : ℝ))) * (1 : ℝ)))))))))))
  (h5 : (forall (v_uCE_uBE : ℝ), ((v_uCE_uBE ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB6 : ℝ), ((v_uCE_uB6 ∈ (Set.univ : Set ℝ)) → ((∫ v_uCE_uBE_1 in (0 : ℝ)..x, ((∫ v_uCE_uB6_1 in (0 : ℝ)..v_uCE_uBE_1, ((∫ v_uCE_uB7 in v_uCE_uB6_1..v_uCE_uBE_1, ((f v_uCE_uB6_1) * (1 : ℝ))) * (1 : ℝ))) * (1 : ℝ))) = (∫ v_uCE_uBE_1 in (0 : ℝ)..x, ((∫ v_uCE_uB6_1 in (0 : ℝ)..v_uCE_uBE_1, (((f v_uCE_uB6_1) * (v_uCE_uBE_1 - v_uCE_uB6_1)) * (1 : ℝ))) * (1 : ℝ)))))))))
  (h6 : (forall (v_uCE_uBE : ℝ), ((v_uCE_uBE ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB6 : ℝ), ((v_uCE_uB6 ∈ (Set.univ : Set ℝ)) → ((∫ v_uCE_uBE_1 in (0 : ℝ)..x, ((∫ v_uCE_uB6_1 in (0 : ℝ)..v_uCE_uBE_1, (((f v_uCE_uB6_1) * (v_uCE_uBE_1 - v_uCE_uB6_1)) * (1 : ℝ))) * (1 : ℝ))) = (∫ v_uCE_uB6_1 in (0 : ℝ)..x, ((∫ v_uCE_uBE_1 in v_uCE_uB6_1..x, (((f v_uCE_uB6_1) * (v_uCE_uBE_1 - v_uCE_uB6_1)) * (1 : ℝ))) * (1 : ℝ)))))))))
  : (forall (v_uCE_uB6 : ℝ), ((v_uCE_uB6 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uBE : ℝ), ((v_uCE_uBE ∈ (Set.univ : Set ℝ)) → ((∫ v_uCE_uB6_1 in (0 : ℝ)..x, ((∫ v_uCE_uBE_1 in v_uCE_uB6_1..x, (((f v_uCE_uB6_1) * (v_uCE_uBE_1 - v_uCE_uB6_1)) * (1 : ℝ))) * (1 : ℝ))) = ((1 /. 2) * (∫ v_uCE_uB6_1 in (0 : ℝ)..x, (((f v_uCE_uB6_1) * ((x - v_uCE_uB6_1) ^ (2 : ℕ))) * (1 : ℝ))))))))) := by
  sorry

theorem proof_gap_exercise_4084_5
  (f : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : x ≥ 0)
  (h3 : ContinuousOn f (Set.Icc 0 x))
  (h4 : (forall (v_uCE_uBE : ℝ), ((v_uCE_uBE ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB7 : ℝ), ((v_uCE_uB7 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB6 : ℝ), ((v_uCE_uB6 ∈ (Set.univ : Set ℝ)) → ((∫ v_uCE_uBE_1 in (0 : ℝ)..x, ((∫ v_uCE_uB7_1 in (0 : ℝ)..v_uCE_uBE_1, ((∫ v_uCE_uB6_1 in (0 : ℝ)..v_uCE_uB7_1, ((f v_uCE_uB6_1) * (1 : ℝ))) * (1 : ℝ))) * (1 : ℝ))) = (∫ v_uCE_uBE_1 in (0 : ℝ)..x, ((∫ v_uCE_uB6_1 in (0 : ℝ)..v_uCE_uBE_1, ((∫ v_uCE_uB7_1 in v_uCE_uB6_1..v_uCE_uBE_1, ((f v_uCE_uB6_1) * (1 : ℝ))) * (1 : ℝ))) * (1 : ℝ)))))))))))
  (h5 : (forall (v_uCE_uBE : ℝ), ((v_uCE_uBE ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB6 : ℝ), ((v_uCE_uB6 ∈ (Set.univ : Set ℝ)) → ((∫ v_uCE_uBE_1 in (0 : ℝ)..x, ((∫ v_uCE_uB6_1 in (0 : ℝ)..v_uCE_uBE_1, ((∫ v_uCE_uB7 in v_uCE_uB6_1..v_uCE_uBE_1, ((f v_uCE_uB6_1) * (1 : ℝ))) * (1 : ℝ))) * (1 : ℝ))) = (∫ v_uCE_uBE_1 in (0 : ℝ)..x, ((∫ v_uCE_uB6_1 in (0 : ℝ)..v_uCE_uBE_1, (((f v_uCE_uB6_1) * (v_uCE_uBE_1 - v_uCE_uB6_1)) * (1 : ℝ))) * (1 : ℝ)))))))))
  (h6 : (forall (v_uCE_uBE : ℝ), ((v_uCE_uBE ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB6 : ℝ), ((v_uCE_uB6 ∈ (Set.univ : Set ℝ)) → ((∫ v_uCE_uBE_1 in (0 : ℝ)..x, ((∫ v_uCE_uB6_1 in (0 : ℝ)..v_uCE_uBE_1, (((f v_uCE_uB6_1) * (v_uCE_uBE_1 - v_uCE_uB6_1)) * (1 : ℝ))) * (1 : ℝ))) = (∫ v_uCE_uB6_1 in (0 : ℝ)..x, ((∫ v_uCE_uBE_1 in v_uCE_uB6_1..x, (((f v_uCE_uB6_1) * (v_uCE_uBE_1 - v_uCE_uB6_1)) * (1 : ℝ))) * (1 : ℝ)))))))))
  (h7 : (forall (v_uCE_uB6 : ℝ), ((v_uCE_uB6 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uBE : ℝ), ((v_uCE_uBE ∈ (Set.univ : Set ℝ)) → ((∫ v_uCE_uB6_1 in (0 : ℝ)..x, ((∫ v_uCE_uBE_1 in v_uCE_uB6_1..x, (((f v_uCE_uB6_1) * (v_uCE_uBE_1 - v_uCE_uB6_1)) * (1 : ℝ))) * (1 : ℝ))) = ((1 /. 2) * (∫ v_uCE_uB6_1 in (0 : ℝ)..x, (((f v_uCE_uB6_1) * ((x - v_uCE_uB6_1) ^ (2 : ℕ))) * (1 : ℝ))))))))))
  : (forall (v_uCE_uBE : ℝ), ((v_uCE_uBE ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB7 : ℝ), ((v_uCE_uB7 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB6 : ℝ), ((v_uCE_uB6 ∈ (Set.univ : Set ℝ)) → ((∫ v_uCE_uBE_1 in (0 : ℝ)..x, ((∫ v_uCE_uB7_1 in (0 : ℝ)..v_uCE_uBE_1, ((∫ v_uCE_uB6_1 in (0 : ℝ)..v_uCE_uB7_1, ((f v_uCE_uB6_1) * (1 : ℝ))) * (1 : ℝ))) * (1 : ℝ))) = ((1 /. 2) * (∫ v_uCE_uB6_1 in (0 : ℝ)..x, (((f v_uCE_uB6_1) * ((x - v_uCE_uB6_1) ^ (2 : ℕ))) * (1 : ℝ))))))))))) := by
  sorry

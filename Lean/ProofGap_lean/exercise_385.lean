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

-- exercise: exercise_385

theorem proof_gap_exercise_385_1
  (f : (ℝ -> ℝ))
  (v_uCE_uB5 : ℝ)
  (h1 : (v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((f x) = ((Real.log x) * ((Real.sin (Real.pi /. x)) ^ (2 : ℕ)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 v_uCE_uB5))) → ((f x) < |((Real.log v_uCE_uB5))|))) := by
  sorry

theorem proof_gap_exercise_385_2
  (f : (ℝ -> ℝ))
  (v_uCE_uB5 : ℝ)
  (h1 : (v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((f x) = ((Real.log x) * ((Real.sin (Real.pi /. x)) ^ (2 : ℕ)))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 v_uCE_uB5))) → ((f x) < |((Real.log v_uCE_uB5))|))))
  : BddAbove (f '' (Set.Ioo 0 v_uCE_uB5)) := by
  sorry

theorem proof_gap_exercise_385_3
  (f : (ℝ -> ℝ))
  (v_uCE_uB5 : ℝ)
  (h1 : (v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((f x) = ((Real.log x) * ((Real.sin (Real.pi /. x)) ^ (2 : ℕ)))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 v_uCE_uB5))) → ((f x) < |((Real.log v_uCE_uB5))|))))
  (h4 : BddAbove (f '' (Set.Ioo 0 v_uCE_uB5)))
  : (exists (x : (ℕ -> ℝ)), (((True ∧ (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) ∈ (Set.Ioo 0 v_uCE_uB5))))) ∧ (Tendsto (fun n : ℕ => (x n)) atTop (𝓝 0))) ∧ (Tendsto (fun n : ℕ => ((f (x n)) : EReal)) atTop (𝓝 ⊥)))) := by
  sorry

theorem proof_gap_exercise_385_4
  (f : (ℝ -> ℝ))
  (v_uCE_uB5 : ℝ)
  (h1 : (v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((f x) = ((Real.log x) * ((Real.sin (Real.pi /. x)) ^ (2 : ℕ)))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 v_uCE_uB5))) → ((f x) < |((Real.log v_uCE_uB5))|))))
  (h4 : BddAbove (f '' (Set.Ioo 0 v_uCE_uB5)))
  (h5 : (exists (x : (ℕ -> ℝ)), (((True ∧ (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) ∈ (Set.Ioo 0 v_uCE_uB5))))) ∧ (Tendsto (fun n : ℕ => (x n)) atTop (𝓝 0))) ∧ (Tendsto (fun n : ℕ => ((f (x n)) : EReal)) atTop (𝓝 ⊥)))))
  : Not (BddBelow (f '' (Set.Ioo 0 v_uCE_uB5))) := by
  sorry

theorem proof_gap_exercise_385_5
  (f : (ℝ -> ℝ))
  (v_uCE_uB5 : ℝ)
  (h1 : (v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((f x) = ((Real.log x) * ((Real.sin (Real.pi /. x)) ^ (2 : ℕ)))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 v_uCE_uB5))) → ((f x) < |((Real.log v_uCE_uB5))|))))
  (h4 : BddAbove (f '' (Set.Ioo 0 v_uCE_uB5)))
  (h5 : (exists (x : (ℕ -> ℝ)), (((True ∧ (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) ∈ (Set.Ioo 0 v_uCE_uB5))))) ∧ (Tendsto (fun n : ℕ => (x n)) atTop (𝓝 0))) ∧ (Tendsto (fun n : ℕ => ((f (x n)) : EReal)) atTop (𝓝 ⊥)))))
  (h6 : Not (BddBelow (f '' (Set.Ioo 0 v_uCE_uB5))))
  : ((BddAbove (f '' (Set.Ioo 0 v_uCE_uB5))) ∧ (Not (BddBelow (f '' (Set.Ioo 0 v_uCE_uB5))))) → ((BddAbove (f '' (Set.Ioo 0 v_uCE_uB5))) ∧ (Not (BddBelow (f '' (Set.Ioo 0 v_uCE_uB5))))) := by
  sorry

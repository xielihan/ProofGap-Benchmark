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

-- exercise: exercise_206

theorem proof_gap_exercise_206_1
  (v_uCF_u86 : (ℝ -> ℝ))
  (v_uCF_u88 : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 x) = (x ^ (2 : ℕ))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u88 x) = (Real.rpow (2 : ℝ) x)))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (v_uCF_u86 x)) = ((x ^ (2 : ℕ)) ^ (2 : ℕ))))) := by
  sorry

theorem proof_gap_exercise_206_2
  (v_uCF_u86 : (ℝ -> ℝ))
  (v_uCF_u88 : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 x) = (x ^ (2 : ℕ))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u88 x) = (Real.rpow (2 : ℝ) x)))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (v_uCF_u86 x)) = ((x ^ (2 : ℕ)) ^ (2 : ℕ))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((x ^ (2 : ℕ)) ^ (2 : ℕ)) = (x ^ (4 : ℕ))))) := by
  sorry

theorem proof_gap_exercise_206_3
  (v_uCF_u86 : (ℝ -> ℝ))
  (v_uCF_u88 : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 x) = (x ^ (2 : ℕ))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u88 x) = (Real.rpow (2 : ℝ) x)))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (v_uCF_u86 x)) = ((x ^ (2 : ℕ)) ^ (2 : ℕ))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((x ^ (2 : ℕ)) ^ (2 : ℕ)) = (x ^ (4 : ℕ))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (v_uCF_u86 x)) = (x ^ (4 : ℕ))))) := by
  sorry

theorem proof_gap_exercise_206_4
  (v_uCF_u86 : (ℝ -> ℝ))
  (v_uCF_u88 : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 x) = (x ^ (2 : ℕ))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u88 x) = (Real.rpow (2 : ℝ) x)))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (v_uCF_u86 x)) = ((x ^ (2 : ℕ)) ^ (2 : ℕ))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((x ^ (2 : ℕ)) ^ (2 : ℕ)) = (x ^ (4 : ℕ))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (v_uCF_u86 x)) = (x ^ (4 : ℕ))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (v_uCF_u88 x)) = ((Real.rpow (2 : ℝ) x) ^ (2 : ℕ))))) := by
  sorry

theorem proof_gap_exercise_206_5
  (v_uCF_u86 : (ℝ -> ℝ))
  (v_uCF_u88 : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 x) = (x ^ (2 : ℕ))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u88 x) = (Real.rpow (2 : ℝ) x)))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (v_uCF_u86 x)) = ((x ^ (2 : ℕ)) ^ (2 : ℕ))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((x ^ (2 : ℕ)) ^ (2 : ℕ)) = (x ^ (4 : ℕ))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (v_uCF_u86 x)) = (x ^ (4 : ℕ))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (v_uCF_u88 x)) = ((Real.rpow (2 : ℝ) x) ^ (2 : ℕ))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((Real.rpow (2 : ℝ) x) ^ (2 : ℕ)) = (Real.rpow (2 : ℝ) (2 * x))))) := by
  sorry

theorem proof_gap_exercise_206_6
  (v_uCF_u86 : (ℝ -> ℝ))
  (v_uCF_u88 : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 x) = (x ^ (2 : ℕ))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u88 x) = (Real.rpow (2 : ℝ) x)))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (v_uCF_u86 x)) = ((x ^ (2 : ℕ)) ^ (2 : ℕ))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((x ^ (2 : ℕ)) ^ (2 : ℕ)) = (x ^ (4 : ℕ))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (v_uCF_u86 x)) = (x ^ (4 : ℕ))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (v_uCF_u88 x)) = ((Real.rpow (2 : ℝ) x) ^ (2 : ℕ))))))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((Real.rpow (2 : ℝ) x) ^ (2 : ℕ)) = (Real.rpow (2 : ℝ) (2 * x))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (v_uCF_u88 x)) = (Real.rpow (2 : ℝ) (2 * x))))) := by
  sorry

theorem proof_gap_exercise_206_7
  (v_uCF_u86 : (ℝ -> ℝ))
  (v_uCF_u88 : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 x) = (x ^ (2 : ℕ))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u88 x) = (Real.rpow (2 : ℝ) x)))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (v_uCF_u86 x)) = ((x ^ (2 : ℕ)) ^ (2 : ℕ))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((x ^ (2 : ℕ)) ^ (2 : ℕ)) = (x ^ (4 : ℕ))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (v_uCF_u86 x)) = (x ^ (4 : ℕ))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (v_uCF_u88 x)) = ((Real.rpow (2 : ℝ) x) ^ (2 : ℕ))))))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((Real.rpow (2 : ℝ) x) ^ (2 : ℕ)) = (Real.rpow (2 : ℝ) (2 * x))))))
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (v_uCF_u88 x)) = (Real.rpow (2 : ℝ) (2 * x))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u88 (v_uCF_u86 x)) = (Real.rpow (2 : ℝ) (x ^ (2 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_206_8
  (v_uCF_u86 : (ℝ -> ℝ))
  (v_uCF_u88 : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 x) = (x ^ (2 : ℕ))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u88 x) = (Real.rpow (2 : ℝ) x)))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (v_uCF_u86 x)) = ((x ^ (2 : ℕ)) ^ (2 : ℕ))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((x ^ (2 : ℕ)) ^ (2 : ℕ)) = (x ^ (4 : ℕ))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (v_uCF_u86 x)) = (x ^ (4 : ℕ))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (v_uCF_u88 x)) = ((Real.rpow (2 : ℝ) x) ^ (2 : ℕ))))))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((Real.rpow (2 : ℝ) x) ^ (2 : ℕ)) = (Real.rpow (2 : ℝ) (2 * x))))))
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (v_uCF_u88 x)) = (Real.rpow (2 : ℝ) (2 * x))))))
  (h9 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u88 (v_uCF_u86 x)) = (Real.rpow (2 : ℝ) (x ^ (2 : ℕ)))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u88 (v_uCF_u88 x)) = (Real.rpow (2 : ℝ) (Real.rpow (2 : ℝ) x))))) := by
  sorry

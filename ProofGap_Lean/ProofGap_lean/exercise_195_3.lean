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

-- exercise: exercise_195_3

theorem proof_gap_exercise_195_3_1
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (h : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a ∈ ({x_1 : ℝ | 0 < x_1})))
  (h2 : (h ∈ (Set.univ : Set ℝ)) ∧ (h ≠ 0))
  (h3 : v_uCF_u86 = (fun (x : ℝ) => (((f (x + h)) - (f x)) /. h)))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (Real.rpow a x)))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 x) = (((f (x + h)) - (f x)) /. h)))) := by
  sorry

theorem proof_gap_exercise_195_3_2
  (f : (ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (a : ℝ)
  (h : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a ∈ ({x_1 : ℝ | 0 < x_1})))
  (h2 : (h ∈ (Set.univ : Set ℝ)) ∧ (h ≠ 0))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (Real.rpow a x)))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 x) = (((f (x + h)) - (f x)) /. h)))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 x) = (((Real.rpow a (x + h)) - (Real.rpow a x)) /. h)))) := by
  sorry

theorem proof_gap_exercise_195_3_3
  (f : (ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (a : ℝ)
  (h : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a ∈ ({x_1 : ℝ | 0 < x_1})))
  (h2 : (h ∈ (Set.univ : Set ℝ)) ∧ (h ≠ 0))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (Real.rpow a x)))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 x) = (((f (x + h)) - (f x)) /. h)))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 x) = (((Real.rpow a (x + h)) - (Real.rpow a x)) /. h)))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 x) = ((Real.rpow a x) * (((Real.rpow a h) - 1) /. h))))) := by
  sorry

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

-- exercise: exercise_208

theorem proof_gap_exercise_208_1
  (v_uCF_u86 : (ℝ -> ℝ))
  (v_uCF_u88 : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 x) = (if (x ≤ 0) then 0 else (if (x > 0) then x else x))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u88 x) = (if (x ≤ 0) then 0 else (if (x > 0) then (-(x ^ (2 : ℕ))) else (-(x ^ (2 : ℕ)))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (v_uCF_u86 x)) = (v_uCF_u86 x)))) := by
  sorry

theorem proof_gap_exercise_208_2
  (v_uCF_u86 : (ℝ -> ℝ))
  (v_uCF_u88 : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 x) = (if (x ≤ 0) then 0 else (if (x > 0) then x else x))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u88 x) = (if (x ≤ 0) then 0 else (if (x > 0) then (-(x ^ (2 : ℕ))) else (-(x ^ (2 : ℕ)))))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (v_uCF_u86 x)) = (v_uCF_u86 x)))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (v_uCF_u88 x)) = 0))) := by
  sorry

theorem proof_gap_exercise_208_3
  (v_uCF_u86 : (ℝ -> ℝ))
  (v_uCF_u88 : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 x) = (if (x ≤ 0) then 0 else (if (x > 0) then x else x))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u88 x) = (if (x ≤ 0) then 0 else (if (x > 0) then (-(x ^ (2 : ℕ))) else (-(x ^ (2 : ℕ)))))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (v_uCF_u86 x)) = (v_uCF_u86 x)))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (v_uCF_u88 x)) = 0))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u88 (v_uCF_u86 x)) = (v_uCF_u88 x)))) := by
  sorry

theorem proof_gap_exercise_208_4
  (v_uCF_u86 : (ℝ -> ℝ))
  (v_uCF_u88 : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 x) = (if (x ≤ 0) then 0 else (if (x > 0) then x else x))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u88 x) = (if (x ≤ 0) then 0 else (if (x > 0) then (-(x ^ (2 : ℕ))) else (-(x ^ (2 : ℕ)))))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (v_uCF_u86 x)) = (v_uCF_u86 x)))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (v_uCF_u88 x)) = 0))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u88 (v_uCF_u86 x)) = (v_uCF_u88 x)))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u88 (v_uCF_u88 x)) = 0))) := by
  sorry

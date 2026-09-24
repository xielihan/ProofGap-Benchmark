import Mathlib

attribute [local instance] Classical.propDecidable

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

-- exercise: exercise_407_12

theorem proof_gap_exercise_407_12_1
  (f : (ℝ -> ℝ))
  (A : ℝ)
  (b : ℝ)
  (h1 : A ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : Tendsto (fun x : ℝ => (f x)) atTop (𝓝 b))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > A)) → ((f x) > b))))
  : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℝ), ((((N ∈ (Set.univ : Set ℝ)) ∧ (N > 0)) ∧ (N > A)) ∧ (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > N)) → ((0 < ((f x) - b)) ∧ (((f x) - b) < v_uCE_uB5)))))))) := by
  sorry

theorem proof_gap_exercise_407_12_2
  (f : (ℝ -> ℝ))
  (A : ℝ)
  (b : ℝ)
  (h1 : A ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℝ), ((((N ∈ (Set.univ : Set ℝ)) ∧ (N > 0)) ∧ (N > A)) ∧ (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > N)) → ((0 < ((f x) - b)) ∧ (((f x) - b) < v_uCE_uB5)))))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0))) → (((y : ℝ → _) x) = (1 /. x))))
  : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℝ), (((N ∈ (Set.univ : Set ℝ)) ∧ (N > 0)) ∧ (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > N)) → ((0 < ((y x) - 0)) ∧ (((y x) - 0) < v_uCE_uB5)))))))) := by
  sorry

theorem proof_gap_exercise_407_12_3
  (f : (ℝ -> ℝ))
  (A : ℝ)
  (b : ℝ)
  (h1 : A ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℝ), ((((N ∈ (Set.univ : Set ℝ)) ∧ (N > 0)) ∧ (N > A)) ∧ (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > N)) → ((0 < ((f x) - b)) ∧ (((f x) - b) < v_uCE_uB5)))))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0))) → (((y : ℝ → _) x) = (1 /. x))))
  (h5 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℝ), (((N ∈ (Set.univ : Set ℝ)) ∧ (N > 0)) ∧ (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > N)) → ((0 < ((y x) - 0)) ∧ (((y x) - 0) < v_uCE_uB5)))))))))
  : Tendsto (fun x : ℝ => (y x)) atTop (𝓝 (0 + 0)) := by
  sorry

theorem proof_gap_exercise_407_12_4
  (f : (ℝ -> ℝ))
  (A : ℝ)
  (b : ℝ)
  (h1 : A ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℝ), ((((N ∈ (Set.univ : Set ℝ)) ∧ (N > 0)) ∧ (N > A)) ∧ (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > N)) → ((0 < ((f x) - b)) ∧ (((f x) - b) < v_uCE_uB5)))))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0))) → (((y : ℝ → _) x) = (1 /. x))))
  (h5 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℝ), (((N ∈ (Set.univ : Set ℝ)) ∧ (N > 0)) ∧ (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > N)) → ((0 < ((y x) - 0)) ∧ (((y x) - 0) < v_uCE_uB5)))))))))
  (h6 : Tendsto (fun x : ℝ => (y x)) atTop (𝓝 (0 + 0)))
  : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℝ), ((((N ∈ (Set.univ : Set ℝ)) ∧ (N > 0)) ∧ (N > A)) ∧ (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > N)) → ((0 < ((f x) - b)) ∧ (((f x) - b) < v_uCE_uB5)))))))) ↔ (Tendsto (fun x : ℝ => (f x)) atTop (𝓝 (b + 0))) := by
  sorry

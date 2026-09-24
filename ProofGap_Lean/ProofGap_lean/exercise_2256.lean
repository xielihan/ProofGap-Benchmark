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

-- exercise: exercise_2256

theorem proof_gap_exercise_2256_1
  (f : (ℝ -> ℝ))
  (A : ℝ)
  (B : ℝ)
  (a : ℝ)
  (b : ℝ)
  (x : ℝ)
  (h1 : A ∈ (Set.univ : Set ℝ))
  (h2 : B ∈ (Set.univ : Set ℝ))
  (h3 : (a ∈ (Set.univ : Set ℝ)) ∧ (A ≤ a))
  (h4 : (b ∈ (Set.univ : Set ℝ)) ∧ (a ≤ b))
  (h5 : ContinuousOn f (Set.Icc A B))
  (h6 : ((x ∈ (Set.univ : Set ℝ)) ∧ ((Set.Icc (a - x) (b - x)) ⊆ (Set.Icc A B))) ∧ ((Set.Icc (a + x) (b + x)) ⊆ (Set.Icc A B)))
  (h7 : b ≤ B)
  : (∫ y in a..b, ((f (x + y)) * (1 : ℝ))) = (∫ y in (a + x)..(b + x), ((f y) * (1 : ℝ))) := by
  sorry

theorem proof_gap_exercise_2256_2
  (f : (ℝ -> ℝ))
  (A : ℝ)
  (B : ℝ)
  (a : ℝ)
  (b : ℝ)
  (x : ℝ)
  (h1 : A ∈ (Set.univ : Set ℝ))
  (h2 : B ∈ (Set.univ : Set ℝ))
  (h3 : (a ∈ (Set.univ : Set ℝ)) ∧ (A ≤ a))
  (h4 : (b ∈ (Set.univ : Set ℝ)) ∧ (a ≤ b))
  (h5 : ContinuousOn f (Set.Icc A B))
  (h6 : ((x ∈ (Set.univ : Set ℝ)) ∧ ((Set.Icc (a - x) (b - x)) ⊆ (Set.Icc A B))) ∧ ((Set.Icc (a + x) (b + x)) ⊆ (Set.Icc A B)))
  (h7 : b ≤ B)
  (h8 : (∫ y in a..b, ((f (x + y)) * (1 : ℝ))) = (∫ y in (a + x)..(b + x), ((f y) * (1 : ℝ))))
  (h9 : (A < (a - x)) ∧ ((b + x) < B))
  : (iteratedDeriv 1 (fun t => (∫ y in a..b, ((f (t + y)) * (1 : ℝ)))) x) = (iteratedDeriv 1 (fun t => (∫ y in (a + t)..(b + t), ((f y) * (1 : ℝ)))) x) := by
  sorry

theorem proof_gap_exercise_2256_3
  (f : (ℝ -> ℝ))
  (A : ℝ)
  (B : ℝ)
  (a : ℝ)
  (b : ℝ)
  (x : ℝ)
  (h1 : A ∈ (Set.univ : Set ℝ))
  (h2 : B ∈ (Set.univ : Set ℝ))
  (h3 : (a ∈ (Set.univ : Set ℝ)) ∧ (A ≤ a))
  (h4 : (b ∈ (Set.univ : Set ℝ)) ∧ (a ≤ b))
  (h5 : ContinuousOn f (Set.Icc A B))
  (h6 : ((x ∈ (Set.univ : Set ℝ)) ∧ ((Set.Icc (a - x) (b - x)) ⊆ (Set.Icc A B))) ∧ ((Set.Icc (a + x) (b + x)) ⊆ (Set.Icc A B)))
  (h7 : b ≤ B)
  (h8 : (∫ y in a..b, ((f (x + y)) * (1 : ℝ))) = (∫ y in (a + x)..(b + x), ((f y) * (1 : ℝ))))
  (h9 : (iteratedDeriv 1 (fun t => (∫ y in a..b, ((f (t + y)) * (1 : ℝ)))) x) = (iteratedDeriv 1 (fun t => (∫ y in (a + t)..(b + t), ((f y) * (1 : ℝ)))) x))
  (h10 : (A < (a - x)) ∧ ((b + x) < B))
  : (iteratedDeriv 1 (fun t => (∫ y in (a + t)..(b + t), ((f y) * (1 : ℝ)))) x) = ((f (b + x)) - (f (a + x))) := by
  sorry

theorem proof_gap_exercise_2256_4
  (f : (ℝ -> ℝ))
  (A : ℝ)
  (B : ℝ)
  (a : ℝ)
  (b : ℝ)
  (x : ℝ)
  (h1 : A ∈ (Set.univ : Set ℝ))
  (h2 : B ∈ (Set.univ : Set ℝ))
  (h3 : (a ∈ (Set.univ : Set ℝ)) ∧ (A ≤ a))
  (h4 : (b ∈ (Set.univ : Set ℝ)) ∧ (a ≤ b))
  (h5 : ContinuousOn f (Set.Icc A B))
  (h6 : ((x ∈ (Set.univ : Set ℝ)) ∧ ((Set.Icc (a - x) (b - x)) ⊆ (Set.Icc A B))) ∧ ((Set.Icc (a + x) (b + x)) ⊆ (Set.Icc A B)))
  (h7 : b ≤ B)
  (h8 : (∫ y in a..b, ((f (x + y)) * (1 : ℝ))) = (∫ y in (a + x)..(b + x), ((f y) * (1 : ℝ))))
  (h9 : (iteratedDeriv 1 (fun t => (∫ y in a..b, ((f (t + y)) * (1 : ℝ)))) x) = (iteratedDeriv 1 (fun t => (∫ y in (a + t)..(b + t), ((f y) * (1 : ℝ)))) x))
  (h10 : (iteratedDeriv 1 (fun t => (∫ y in (a + t)..(b + t), ((f y) * (1 : ℝ)))) x) = ((f (b + x)) - (f (a + x))))
  : (iteratedDeriv 1 (fun t => (∫ y in a..b, ((f (t + y)) * (1 : ℝ)))) x) = ((f (b + x)) - (f (a + x))) := by
  sorry

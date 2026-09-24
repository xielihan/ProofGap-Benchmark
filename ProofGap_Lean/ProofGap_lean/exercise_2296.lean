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

-- exercise: exercise_2296

theorem proof_gap_exercise_2296_1
  (f : (ℝ -> ℝ))
  (n : ℕ)
  (x : ℝ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((f x_1) = (((Real.cos x_1) ^ (n - 1)) * (Real.sin ((n + 1) * x_1)))))))
  : Function.Periodic f Real.pi := by
  sorry

theorem proof_gap_exercise_2296_2
  (f : (ℝ -> ℝ))
  (n : ℕ)
  (x : ℝ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((f x_1) = (((Real.cos x_1) ^ (n - 1)) * (Real.sin ((n + 1) * x_1)))))))
  (h5 : Function.Periodic f Real.pi)
  : Function.Odd f := by
  sorry

theorem proof_gap_exercise_2296_3
  (f : (ℝ -> ℝ))
  (n : ℕ)
  (x : ℝ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((f x_1) = (((Real.cos x_1) ^ (n - 1)) * (Real.sin ((n + 1) * x_1)))))))
  (h5 : Function.Periodic f Real.pi)
  (h6 : Function.Odd f)
  : (∫ x_1 in (0 : ℝ)..Real.pi, ((((Real.cos x_1) ^ (n - 1)) * (Real.sin ((n + 1) * x_1))) * (1 : ℝ))) = (∫ x_1 in (-(Real.pi /. 2))..(Real.pi /. 2), ((f x_1) * (1 : ℝ))) := by
  sorry

theorem proof_gap_exercise_2296_4
  (f : (ℝ -> ℝ))
  (n : ℕ)
  (x : ℝ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((f x_1) = (((Real.cos x_1) ^ (n - 1)) * (Real.sin ((n + 1) * x_1)))))))
  (h5 : Function.Periodic f Real.pi)
  (h6 : Function.Odd f)
  (h7 : (∫ x_1 in (0 : ℝ)..Real.pi, ((((Real.cos x_1) ^ (n - 1)) * (Real.sin ((n + 1) * x_1))) * (1 : ℝ))) = (∫ x_1 in (-(Real.pi /. 2))..(Real.pi /. 2), ((f x_1) * (1 : ℝ))))
  : (∫ x_1 in (-(Real.pi /. 2))..(Real.pi /. 2), ((f x_1) * (1 : ℝ))) = 0 := by
  sorry

theorem proof_gap_exercise_2296_5
  (f : (ℝ -> ℝ))
  (n : ℕ)
  (x : ℝ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((f x_1) = (((Real.cos x_1) ^ (n - 1)) * (Real.sin ((n + 1) * x_1)))))))
  (h5 : Function.Periodic f Real.pi)
  (h6 : Function.Odd f)
  (h7 : (∫ x_1 in (0 : ℝ)..Real.pi, ((((Real.cos x_1) ^ (n - 1)) * (Real.sin ((n + 1) * x_1))) * (1 : ℝ))) = (∫ x_1 in (-(Real.pi /. 2))..(Real.pi /. 2), ((f x_1) * (1 : ℝ))))
  (h8 : (∫ x_1 in (-(Real.pi /. 2))..(Real.pi /. 2), ((f x_1) * (1 : ℝ))) = 0)
  : (∫ x_1 in (0 : ℝ)..Real.pi, ((((Real.cos x_1) ^ (n - 1)) * (Real.sin ((n + 1) * x_1))) * (1 : ℝ))) = 0 := by
  sorry

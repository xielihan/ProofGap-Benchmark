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

-- exercise: exercise_2901

theorem proof_gap_exercise_2901_1
  (F : (ℝ -> ℝ))
  (x : ℝ)
  (n : ℕ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℕ))
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((F x_1) = (∫ t in (0 : ℝ)..x_1, ((Real.exp (-(t ^ (2 : ℕ)))) * (1 : ℝ)))))))
  : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((Real.exp (-(t ^ (2 : ℕ)))) = (∑' n_1, if (0 : ℕ) ≤ n_1 then (((-(1 : ℤ)) ^ n_1) * ((t ^ (2 * n_1)) /. (n_1)!)) else 0)))) := by
  sorry

theorem proof_gap_exercise_2901_2
  (F : (ℝ -> ℝ))
  (x : ℝ)
  (n : ℕ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℕ))
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((F x_1) = (∫ t in (0 : ℝ)..x_1, ((Real.exp (-(t ^ (2 : ℕ)))) * (1 : ℝ)))))))
  (h4 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((Real.exp (-(t ^ (2 : ℕ)))) = (∑' n_1, if (0 : ℕ) ≤ n_1 then (((-(1 : ℤ)) ^ n_1) * ((t ^ (2 * n_1)) /. (n_1)!)) else 0)))))
  : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((F x_1) = (∫ t in (0 : ℝ)..x_1, ((∑' n_1, if (0 : ℕ) ≤ n_1 then (((-(1 : ℤ)) ^ n_1) * ((t ^ (2 * n_1)) /. (n_1)!)) else 0) * (1 : ℝ)))))) := by
  sorry

theorem proof_gap_exercise_2901_3
  (F : (ℝ -> ℝ))
  (x : ℝ)
  (n : ℕ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℕ))
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((F x_1) = (∫ t in (0 : ℝ)..x_1, ((Real.exp (-(t ^ (2 : ℕ)))) * (1 : ℝ)))))))
  (h4 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((Real.exp (-(t ^ (2 : ℕ)))) = (∑' n_1, if (0 : ℕ) ≤ n_1 then (((-(1 : ℤ)) ^ n_1) * ((t ^ (2 * n_1)) /. (n_1)!)) else 0)))))
  (h5 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((F x_1) = (∫ t in (0 : ℝ)..x_1, ((∑' n_1, if (0 : ℕ) ≤ n_1 then (((-(1 : ℤ)) ^ n_1) * ((t ^ (2 * n_1)) /. (n_1)!)) else 0) * (1 : ℝ)))))))
  : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((F x_1) = (∑' n_1, if (0 : ℕ) ≤ n_1 then (((-(1 : ℤ)) ^ n_1) * ((x_1 ^ ((2 * n_1) + 1)) /. ((n_1)! * ((2 * n_1) + 1)))) else 0)))) := by
  sorry

theorem proof_gap_exercise_2901_4
  (F : (ℝ -> ℝ))
  (x : ℝ)
  (n : ℕ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℕ))
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((F x_1) = (∫ t in (0 : ℝ)..x_1, ((Real.exp (-(t ^ (2 : ℕ)))) * (1 : ℝ)))))))
  (h4 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((Real.exp (-(t ^ (2 : ℕ)))) = (∑' n_1, if (0 : ℕ) ≤ n_1 then (((-(1 : ℤ)) ^ n_1) * ((t ^ (2 * n_1)) /. (n_1)!)) else 0)))))
  (h5 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((F x_1) = (∫ t in (0 : ℝ)..x_1, ((∑' n_1, if (0 : ℕ) ≤ n_1 then (((-(1 : ℤ)) ^ n_1) * ((t ^ (2 * n_1)) /. (n_1)!)) else 0) * (1 : ℝ)))))))
  (h6 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((F x_1) = (∑' n_1, if (0 : ℕ) ≤ n_1 then (((-(1 : ℤ)) ^ n_1) * ((x_1 ^ ((2 * n_1) + 1)) /. ((n_1)! * ((2 * n_1) + 1)))) else 0)))))
  : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((F x_1) = (∑' n_1, if (0 : ℕ) ≤ n_1 then (((-(1 : ℤ)) ^ n_1) * ((x_1 ^ ((2 * n_1) + 1)) /. ((n_1)! * ((2 * n_1) + 1)))) else 0)))) := by
  sorry

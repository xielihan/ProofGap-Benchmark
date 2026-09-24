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

-- exercise: exercise_2846

theorem proof_gap_exercise_2846_1
  (f : (ℝ -> ℝ))
  (u : ℝ)
  (h1 : u ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((f x) = (Real.cos (u * (Real.arcsin x)))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((Real.cos (u * (Real.arcsin x))) = (∑' n, if (0 : ℕ) ≤ n then (((((-(1 : ℤ)) ^ n) * (u ^ (2 * n))) * ((Real.arcsin x) ^ (2 * n))) /. ((2 * n))!) else 0)))) := by
  sorry

theorem proof_gap_exercise_2846_2
  (f : (ℝ -> ℝ))
  (u : ℝ)
  (h1 : u ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((f x) = (Real.cos (u * (Real.arcsin x)))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((Real.cos (u * (Real.arcsin x))) = (∑' n, if (0 : ℕ) ≤ n then (((((-(1 : ℤ)) ^ n) * (u ^ (2 * n))) * ((Real.arcsin x) ^ (2 * n))) /. ((2 * n))!) else 0)))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((1 - (((u ^ (2 : ℕ)) /. ((2 : ℕ))!) * (x ^ (2 : ℕ)))) - (∑' n, if (2 : ℕ) ≤ n then ((((u ^ (2 : ℕ)) * (∏ k ∈ Finset.Icc (1 : ℕ) (n - 1), (((2 * k) ^ (2 : ℕ)) - (u ^ (2 : ℕ))))) /. ((2 * n))!) * (x ^ (2 * n))) else 0))))) := by
  sorry

theorem proof_gap_exercise_2846_3
  (f : (ℝ -> ℝ))
  (u : ℝ)
  (h1 : u ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((f x) = (Real.cos (u * (Real.arcsin x)))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((Real.cos (u * (Real.arcsin x))) = (∑' n, if (0 : ℕ) ≤ n then (((((-(1 : ℤ)) ^ n) * (u ^ (2 * n))) * ((Real.arcsin x) ^ (2 * n))) /. ((2 * n))!) else 0)))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((1 - (((u ^ (2 : ℕ)) /. ((2 : ℕ))!) * (x ^ (2 : ℕ)))) - (∑' n, if (2 : ℕ) ≤ n then ((((u ^ (2 : ℕ)) * (∏ k ∈ Finset.Icc (1 : ℕ) (n - 1), (((2 * k) ^ (2 : ℕ)) - (u ^ (2 : ℕ))))) /. ((2 * n))!) * (x ^ (2 * n))) else 0))))))
  : (lpRadiusOfConvergence (fun (n : ℕ) => (((u ^ (2 : ℕ)) * (∏ k ∈ Finset.Icc (1 : ℕ) (n - 1), (((2 * k) ^ (2 : ℕ)) - (u ^ (2 : ℕ))))) /. ((2 * n))!))) = 1 := by
  sorry

theorem proof_gap_exercise_2846_4
  (f : (ℝ -> ℝ))
  (u : ℝ)
  (h1 : u ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((f x) = (Real.cos (u * (Real.arcsin x)))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((Real.cos (u * (Real.arcsin x))) = (∑' n, if (0 : ℕ) ≤ n then (((((-(1 : ℤ)) ^ n) * (u ^ (2 * n))) * ((Real.arcsin x) ^ (2 * n))) /. ((2 * n))!) else 0)))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((1 - (((u ^ (2 : ℕ)) /. ((2 : ℕ))!) * (x ^ (2 : ℕ)))) - (∑' n, if (2 : ℕ) ≤ n then ((((u ^ (2 : ℕ)) * (∏ k ∈ Finset.Icc (1 : ℕ) (n - 1), (((2 * k) ^ (2 : ℕ)) - (u ^ (2 : ℕ))))) /. ((2 * n))!) * (x ^ (2 * n))) else 0))))))
  (h5 : (lpRadiusOfConvergence (fun (n : ℕ) => (((u ^ (2 : ℕ)) * (∏ k ∈ Finset.Icc (1 : ℕ) (n - 1), (((2 * k) ^ (2 : ℕ)) - (u ^ (2 : ℕ))))) /. ((2 * n))!))) = 1)
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((f x) = ((1 - (((u ^ (2 : ℕ)) /. ((2 : ℕ))!) * (x ^ (2 : ℕ)))) - (∑' n, if (2 : ℕ) ≤ n then ((((u ^ (2 : ℕ)) * (∏ k ∈ Finset.Icc (1 : ℕ) (n - 1), (((2 * k) ^ (2 : ℕ)) - (u ^ (2 : ℕ))))) /. ((2 * n))!) * (x ^ (2 * n))) else 0))))) := by
  sorry

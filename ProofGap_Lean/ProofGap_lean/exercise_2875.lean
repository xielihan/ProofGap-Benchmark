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

-- exercise: exercise_2875

theorem proof_gap_exercise_2875_1
  (f : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((f x_1) = (Real.log (1 /. ((2 + (2 * x_1)) + (x_1 ^ (2 : ℕ)))))))))
  : ((2 + (2 * x)) + (x ^ (2 : ℕ))) = (1 + ((x + 1) ^ (2 : ℕ))) := by
  sorry

theorem proof_gap_exercise_2875_2
  (f : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((f x_1) = (Real.log (1 /. ((2 + (2 * x_1)) + (x_1 ^ (2 : ℕ)))))))))
  (h3 : ((2 + (2 * x)) + (x ^ (2 : ℕ))) = (1 + ((x + 1) ^ (2 : ℕ))))
  : (f x) = (-(Real.log (1 + ((x + 1) ^ (2 : ℕ))))) := by
  sorry

theorem proof_gap_exercise_2875_3
  (f : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((f x_1) = (Real.log (1 /. ((2 + (2 * x_1)) + (x_1 ^ (2 : ℕ)))))))))
  (h3 : ((2 + (2 * x)) + (x ^ (2 : ℕ))) = (1 + ((x + 1) ^ (2 : ℕ))))
  (h4 : (f x) = (-(Real.log (1 + ((x + 1) ^ (2 : ℕ))))))
  : (-(Real.log (1 + ((x + 1) ^ (2 : ℕ))))) = (-(∑' n, if (1 : ℕ) ≤ n then ((((-(1 : ℤ)) ^ (n - 1)) * (1 /. n)) * ((x + 1) ^ (2 * n))) else 0)) := by
  sorry

theorem proof_gap_exercise_2875_4
  (f : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((f x_1) = (Real.log (1 /. ((2 + (2 * x_1)) + (x_1 ^ (2 : ℕ)))))))))
  (h3 : ((2 + (2 * x)) + (x ^ (2 : ℕ))) = (1 + ((x + 1) ^ (2 : ℕ))))
  (h4 : (f x) = (-(Real.log (1 + ((x + 1) ^ (2 : ℕ))))))
  (h5 : (-(Real.log (1 + ((x + 1) ^ (2 : ℕ))))) = (-(∑' n, if (1 : ℕ) ≤ n then ((((-(1 : ℤ)) ^ (n - 1)) * (1 /. n)) * ((x + 1) ^ (2 * n))) else 0)))
  : (f x) = (∑' n, if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) * (((x + 1) ^ (2 * n)) /. n)) else 0) := by
  sorry

theorem proof_gap_exercise_2875_5
  (f : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((f x_1) = (Real.log (1 /. ((2 + (2 * x_1)) + (x_1 ^ (2 : ℕ)))))))))
  (h3 : ((2 + (2 * x)) + (x ^ (2 : ℕ))) = (1 + ((x + 1) ^ (2 : ℕ))))
  (h4 : (f x) = (-(Real.log (1 + ((x + 1) ^ (2 : ℕ))))))
  (h5 : (-(Real.log (1 + ((x + 1) ^ (2 : ℕ))))) = (-(∑' n, if (1 : ℕ) ≤ n then ((((-(1 : ℤ)) ^ (n - 1)) * (1 /. n)) * ((x + 1) ^ (2 * n))) else 0)))
  (h6 : (f x) = (∑' n, if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) * (((x + 1) ^ (2 * n)) /. n)) else 0))
  : (|((x + 1))| ≤ 1) ↔ (((-(2 : ℝ)) ≤ x) ∧ (x ≤ 0)) := by
  sorry

theorem proof_gap_exercise_2875_6
  (f : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((f x_1) = (Real.log (1 /. ((2 + (2 * x_1)) + (x_1 ^ (2 : ℕ)))))))))
  (h3 : ((2 + (2 * x)) + (x ^ (2 : ℕ))) = (1 + ((x + 1) ^ (2 : ℕ))))
  (h4 : (f x) = (-(Real.log (1 + ((x + 1) ^ (2 : ℕ))))))
  (h5 : (-(Real.log (1 + ((x + 1) ^ (2 : ℕ))))) = (-(∑' n, if (1 : ℕ) ≤ n then ((((-(1 : ℤ)) ^ (n - 1)) * (1 /. n)) * ((x + 1) ^ (2 * n))) else 0)))
  (h6 : (f x) = (∑' n, if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) * (((x + 1) ^ (2 * n)) /. n)) else 0))
  (h7 : (|((x + 1))| ≤ 1) ↔ (((-(2 : ℝ)) ≤ x) ∧ (x ≤ 0)))
  : (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) * (((x + 1) ^ (2 * n)) /. n)) else 0)) ↔ (|((x + 1))| ≤ 1) := by
  sorry

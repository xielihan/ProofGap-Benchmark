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

-- exercise: exercise_2908

theorem proof_gap_exercise_2908_1
  (F : (ℝ -> ℝ))
  (h1 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F x) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((x ^ (2 * n_1)) /. ((2 * n_1))!) else 0)))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F t) x) = (∑' n, if (0 : ℕ) ≤ n then ((x ^ ((2 * n) + 1)) /. (((2 * n) + 1))!) else 0)))) := by
  sorry

theorem proof_gap_exercise_2908_2
  (F : (ℝ -> ℝ))
  (h1 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F x) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((x ^ (2 * n_1)) /. ((2 * n_1))!) else 0)))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F t) x) = (∑' n, if (0 : ℕ) ≤ n then ((x ^ ((2 * n) + 1)) /. (((2 * n) + 1))!) else 0)))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((F x) - (iteratedDeriv 1 (fun t => F t) x)) = (∑' n, if (0 : ℕ) ≤ n then (((-x) ^ n) /. (n)!) else 0)) ∧ ((∑' n, if (0 : ℕ) ≤ n then (((-x) ^ n) /. (n)!) else 0) = (Real.exp (-x)))))) := by
  sorry

theorem proof_gap_exercise_2908_3
  (F : (ℝ -> ℝ))
  (h1 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F x) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((x ^ (2 * n_1)) /. ((2 * n_1))!) else 0)))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F t) x) = (∑' n, if (0 : ℕ) ≤ n then ((x ^ ((2 * n) + 1)) /. (((2 * n) + 1))!) else 0)))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((F x) - (iteratedDeriv 1 (fun t => F t) x)) = (∑' n, if (0 : ℕ) ≤ n then (((-x) ^ n) /. (n)!) else 0)) ∧ ((∑' n, if (0 : ℕ) ≤ n then (((-x) ^ n) /. (n)!) else 0) = (Real.exp (-x)))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((F x) + (iteratedDeriv 1 (fun t => F t) x)) = (∑' n, if (0 : ℕ) ≤ n then ((x ^ n) /. (n)!) else 0)) ∧ ((∑' n, if (0 : ℕ) ≤ n then ((x ^ n) /. (n)!) else 0) = (Real.exp x))))) := by
  sorry

theorem proof_gap_exercise_2908_4
  (F : (ℝ -> ℝ))
  (h1 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F x) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((x ^ (2 * n_1)) /. ((2 * n_1))!) else 0)))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F t) x) = (∑' n, if (0 : ℕ) ≤ n then ((x ^ ((2 * n) + 1)) /. (((2 * n) + 1))!) else 0)))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((F x) - (iteratedDeriv 1 (fun t => F t) x)) = (∑' n, if (0 : ℕ) ≤ n then (((-x) ^ n) /. (n)!) else 0)) ∧ ((∑' n, if (0 : ℕ) ≤ n then (((-x) ^ n) /. (n)!) else 0) = (Real.exp (-x)))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((F x) + (iteratedDeriv 1 (fun t => F t) x)) = (∑' n, if (0 : ℕ) ≤ n then ((x ^ n) /. (n)!) else 0)) ∧ ((∑' n, if (0 : ℕ) ≤ n then ((x ^ n) /. (n)!) else 0) = (Real.exp x))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((2 * (F x)) = ((Real.exp x) + (Real.exp (-x)))))) := by
  sorry

theorem proof_gap_exercise_2908_5
  (F : (ℝ -> ℝ))
  (h1 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F x) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((x ^ (2 * n_1)) /. ((2 * n_1))!) else 0)))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F t) x) = (∑' n, if (0 : ℕ) ≤ n then ((x ^ ((2 * n) + 1)) /. (((2 * n) + 1))!) else 0)))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((F x) - (iteratedDeriv 1 (fun t => F t) x)) = (∑' n, if (0 : ℕ) ≤ n then (((-x) ^ n) /. (n)!) else 0)) ∧ ((∑' n, if (0 : ℕ) ≤ n then (((-x) ^ n) /. (n)!) else 0) = (Real.exp (-x)))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((F x) + (iteratedDeriv 1 (fun t => F t) x)) = (∑' n, if (0 : ℕ) ≤ n then ((x ^ n) /. (n)!) else 0)) ∧ ((∑' n, if (0 : ℕ) ≤ n then ((x ^ n) /. (n)!) else 0) = (Real.exp x))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((2 * (F x)) = ((Real.exp x) + (Real.exp (-x)))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((F x) = (((Real.exp x) + (Real.exp (-x))) /. 2)) ∧ ((((Real.exp x) + (Real.exp (-x))) /. 2) = (Real.cosh x))))) := by
  sorry

theorem proof_gap_exercise_2908_6
  (F : (ℝ -> ℝ))
  (h1 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F x) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((x ^ (2 * n_1)) /. ((2 * n_1))!) else 0)))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F t) x) = (∑' n, if (0 : ℕ) ≤ n then ((x ^ ((2 * n) + 1)) /. (((2 * n) + 1))!) else 0)))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((F x) - (iteratedDeriv 1 (fun t => F t) x)) = (∑' n, if (0 : ℕ) ≤ n then (((-x) ^ n) /. (n)!) else 0)) ∧ ((∑' n, if (0 : ℕ) ≤ n then (((-x) ^ n) /. (n)!) else 0) = (Real.exp (-x)))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((F x) + (iteratedDeriv 1 (fun t => F t) x)) = (∑' n, if (0 : ℕ) ≤ n then ((x ^ n) /. (n)!) else 0)) ∧ ((∑' n, if (0 : ℕ) ≤ n then ((x ^ n) /. (n)!) else 0) = (Real.exp x))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((2 * (F x)) = ((Real.exp x) + (Real.exp (-x)))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((F x) = (((Real.exp x) + (Real.exp (-x))) /. 2)) ∧ ((((Real.exp x) + (Real.exp (-x))) /. 2) = (Real.cosh x))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((∑' n, if (0 : ℕ) ≤ n then ((x ^ (2 * n)) /. ((2 * n))!) else 0) = (((Real.exp x) + (Real.exp (-x))) /. 2)) ∧ ((((Real.exp x) + (Real.exp (-x))) /. 2) = (Real.cosh x))))) := by
  sorry

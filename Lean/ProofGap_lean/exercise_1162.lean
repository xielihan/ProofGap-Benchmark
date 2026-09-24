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

-- exercise: exercise_1162

theorem proof_gap_exercise_1162_1
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((y x) = ((Real.exp x) /. x)))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 10 (fun t => y t) x) = (∑ i ∈ Finset.Icc (0 : ℕ) (10 : ℕ), (((Nat.choose (10 : ℕ) i) * (Real.exp x)) * (iteratedDeriv (10 - i) (fun t => (1 /. t)) x)))))) := by
  sorry

theorem proof_gap_exercise_1162_2
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((y x) = ((Real.exp x) /. x)))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 10 (fun t => y t) x) = (∑ i ∈ Finset.Icc (0 : ℕ) (10 : ℕ), (((Nat.choose (10 : ℕ) i) * (Real.exp x)) * (iteratedDeriv (10 - i) (fun t => (1 /. t)) x)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 10 (fun t => y t) x) = ((Real.exp x) * (∑ i ∈ Finset.Icc (0 : ℕ) (10 : ℕ), (((-(1 : ℤ)) ^ i) * ((Nat.descFactorial (10 : ℕ) i) /. (x ^ (i + 1))))))))) := by
  sorry

theorem proof_gap_exercise_1162_3
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((y x) = ((Real.exp x) /. x)))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 10 (fun t => y t) x) = (∑ i ∈ Finset.Icc (0 : ℕ) (10 : ℕ), (((Nat.choose (10 : ℕ) i) * (Real.exp x)) * (iteratedDeriv (10 - i) (fun t => (1 /. t)) x)))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 10 (fun t => y t) x) = ((Real.exp x) * (∑ i ∈ Finset.Icc (0 : ℕ) (10 : ℕ), (((-(1 : ℤ)) ^ i) * ((Nat.descFactorial (10 : ℕ) i) /. (x ^ (i + 1))))))))))
  : (Nat.descFactorial (10 : ℕ) (0 : ℕ)) = 1 := by
  sorry

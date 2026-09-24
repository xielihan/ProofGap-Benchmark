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

-- exercise: exercise_3064

theorem proof_gap_exercise_3064_1
  (P : (ℕ -> ℝ))
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) → (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ≥ 1)) → ((P n) = (∏ k_1 ∈ Finset.Icc (1 : ℕ) n, (Real.rpow a (((-(1 : ℤ)) ^ k_1) /. k_1)))))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) → (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ≥ 1)) → ((P n) = (Real.rpow a (-(∑ k_1 ∈ Finset.Icc (1 : ℕ) n, (((-(1 : ℤ)) ^ (k_1 - 1)) /. k_1))))))))) := by
  sorry

theorem proof_gap_exercise_3064_2
  (P : (ℕ -> ℝ))
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) → (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ≥ 1)) → ((P n) = (∏ k_1 ∈ Finset.Icc (1 : ℕ) n, (Real.rpow a (((-(1 : ℤ)) ^ k_1) /. k_1)))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) → (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ≥ 1)) → ((P n) = (Real.rpow a (-(∑ k_1 ∈ Finset.Icc (1 : ℕ) n, (((-(1 : ℤ)) ^ (k_1 - 1)) /. k_1))))))))))
  : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ≥ 1)) → (Tendsto (fun n : ℕ => (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, (((-(1 : ℤ)) ^ (k_1 - 1)) /. k_1))) atTop (𝓝 (Real.log (2 : ℝ)))))) := by
  sorry

theorem proof_gap_exercise_3064_3
  (P : (ℕ -> ℝ))
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) → (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ≥ 1)) → ((P n) = (∏ k_1 ∈ Finset.Icc (1 : ℕ) n, (Real.rpow a (((-(1 : ℤ)) ^ k_1) /. k_1)))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) → (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ≥ 1)) → ((P n) = (Real.rpow a (-(∑ k_1 ∈ Finset.Icc (1 : ℕ) n, (((-(1 : ℤ)) ^ (k_1 - 1)) /. k_1))))))))))
  (h4 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ≥ 1)) → (Tendsto (fun n : ℕ => (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, (((-(1 : ℤ)) ^ (k_1 - 1)) /. k_1))) atTop (𝓝 (Real.log (2 : ℝ)))))))
  : Tendsto (fun n : ℕ => (P n)) atTop (𝓝 (Real.rpow a (-(Real.log (2 : ℝ))))) := by
  sorry

theorem proof_gap_exercise_3064_4
  (P : (ℕ -> ℝ))
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) → (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ≥ 1)) → ((P n) = (∏ k_1 ∈ Finset.Icc (1 : ℕ) n, (Real.rpow a (((-(1 : ℤ)) ^ k_1) /. k_1)))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) → (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ≥ 1)) → ((P n) = (Real.rpow a (-(∑ k_1 ∈ Finset.Icc (1 : ℕ) n, (((-(1 : ℤ)) ^ (k_1 - 1)) /. k_1))))))))))
  (h4 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ≥ 1)) → (Tendsto (fun n : ℕ => (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, (((-(1 : ℤ)) ^ (k_1 - 1)) /. k_1))) atTop (𝓝 (Real.log (2 : ℝ)))))))
  (h5 : Tendsto (fun n : ℕ => (P n)) atTop (𝓝 (Real.rpow a (-(Real.log (2 : ℝ))))))
  : (∏' n, if (1 : ℕ) ≤ n then (Real.rpow a (((-(1 : ℤ)) ^ n) /. n)) else 1) = (Real.rpow a (-(Real.log (2 : ℝ)))) := by
  sorry

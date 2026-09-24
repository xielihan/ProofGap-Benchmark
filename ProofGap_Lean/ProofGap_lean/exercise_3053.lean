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

-- exercise: exercise_3053

theorem proof_gap_exercise_3053_1
  (p : (ℤ -> ℝ))
  (P : (ℤ -> ℝ))
  (h1 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → ((p n) = (1 - (2 /. (n * (n + 1))))))))
  (h2 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → (forall (i : ℤ), (((i ∈ (Set.univ : Set ℤ)) ∧ (i ≥ 2)) → ((P n) = (∏ i_1 ∈ Finset.Icc (2 : ℤ) n, (p i_1))))))))
  : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → ((p n) = (((n + 2) * (n - 1)) /. (n * (n + 1)))))) := by
  sorry

theorem proof_gap_exercise_3053_2
  (p : (ℤ -> ℝ))
  (P : (ℤ -> ℝ))
  (h1 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → ((p n) = (1 - (2 /. (n * (n + 1))))))))
  (h2 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → (forall (i : ℤ), (((i ∈ (Set.univ : Set ℤ)) ∧ (i ≥ 2)) → ((P n) = (∏ i_1 ∈ Finset.Icc (2 : ℤ) n, (p i_1))))))))
  (h3 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → ((p n) = (((n + 2) * (n - 1)) /. (n * (n + 1)))))))
  : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → (forall (i : ℤ), (((((i ∈ (Set.univ : Set ℤ)) ∧ (i ≥ 2)) ∧ (n ∈ (Set.univ : Set ℤ))) ∧ (n ≥ 2)) → ((P n) = (∏ i_1 ∈ Finset.Icc (2 : ℤ) n, (((i_1 + 2) * (i_1 - 1)) /. (i_1 * (i_1 + 1))))))))) := by
  sorry

theorem proof_gap_exercise_3053_3
  (p : (ℤ -> ℝ))
  (P : (ℤ -> ℝ))
  (h1 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → ((p n) = (1 - (2 /. (n * (n + 1))))))))
  (h2 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → (forall (i : ℤ), (((i ∈ (Set.univ : Set ℤ)) ∧ (i ≥ 2)) → ((P n) = (∏ i_1 ∈ Finset.Icc (2 : ℤ) n, (p i_1))))))))
  (h3 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → ((p n) = (((n + 2) * (n - 1)) /. (n * (n + 1)))))))
  (h4 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → (forall (i : ℤ), (((((i ∈ (Set.univ : Set ℤ)) ∧ (i ≥ 2)) ∧ (n ∈ (Set.univ : Set ℤ))) ∧ (n ≥ 2)) → ((P n) = (∏ i_1 ∈ Finset.Icc (2 : ℤ) n, (((i_1 + 2) * (i_1 - 1)) /. (i_1 * (i_1 + 1))))))))))
  : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → ((P n) = ((1 /. 3) * ((n + 2) /. n))))) := by
  sorry

theorem proof_gap_exercise_3053_4
  (p : (ℤ -> ℝ))
  (P : (ℤ -> ℝ))
  (h1 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → ((p n) = (1 - (2 /. (n * (n + 1))))))))
  (h2 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → (forall (i : ℤ), (((i ∈ (Set.univ : Set ℤ)) ∧ (i ≥ 2)) → ((P n) = (∏ i_1 ∈ Finset.Icc (2 : ℤ) n, (p i_1))))))))
  (h3 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → ((p n) = (((n + 2) * (n - 1)) /. (n * (n + 1)))))))
  (h4 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → (forall (i : ℤ), (((((i ∈ (Set.univ : Set ℤ)) ∧ (i ≥ 2)) ∧ (n ∈ (Set.univ : Set ℤ))) ∧ (n ≥ 2)) → ((P n) = (∏ i_1 ∈ Finset.Icc (2 : ℤ) n, (((i_1 + 2) * (i_1 - 1)) /. (i_1 * (i_1 + 1))))))))))
  (h5 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → ((P n) = ((1 /. 3) * ((n + 2) /. n))))))
  : Tendsto (fun n : ℕ => (P n)) atTop (𝓝 (1 /. 3)) := by
  sorry

theorem proof_gap_exercise_3053_5
  (p : (ℤ -> ℝ))
  (P : (ℤ -> ℝ))
  (h1 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → ((p n) = (1 - (2 /. (n * (n + 1))))))))
  (h2 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → (forall (i : ℤ), (((i ∈ (Set.univ : Set ℤ)) ∧ (i ≥ 2)) → ((P n) = (∏ i_1 ∈ Finset.Icc (2 : ℤ) n, (p i_1))))))))
  (h3 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → ((p n) = (((n + 2) * (n - 1)) /. (n * (n + 1)))))))
  (h4 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → (forall (i : ℤ), (((((i ∈ (Set.univ : Set ℤ)) ∧ (i ≥ 2)) ∧ (n ∈ (Set.univ : Set ℤ))) ∧ (n ≥ 2)) → ((P n) = (∏ i_1 ∈ Finset.Icc (2 : ℤ) n, (((i_1 + 2) * (i_1 - 1)) /. (i_1 * (i_1 + 1))))))))))
  (h5 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → ((P n) = ((1 /. 3) * ((n + 2) /. n))))))
  (h6 : Tendsto (fun n : ℕ => (P n)) atTop (𝓝 (1 /. 3)))
  : (∏' n, if (2 : ℕ) ≤ n then (1 - (2 /. (n * (n + 1)))) else 1) = (1 /. 3) := by
  sorry

theorem proof_gap_exercise_3053_6
  (p : (ℤ -> ℝ))
  (P : (ℤ -> ℝ))
  (h1 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → ((p n) = (1 - (2 /. (n * (n + 1))))))))
  (h2 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → (forall (i : ℤ), (((i ∈ (Set.univ : Set ℤ)) ∧ (i ≥ 2)) → ((P n) = (∏ i_1 ∈ Finset.Icc (2 : ℤ) n, (p i_1))))))))
  (h3 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → ((p n) = (((n + 2) * (n - 1)) /. (n * (n + 1)))))))
  (h4 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → (forall (i : ℤ), (((((i ∈ (Set.univ : Set ℤ)) ∧ (i ≥ 2)) ∧ (n ∈ (Set.univ : Set ℤ))) ∧ (n ≥ 2)) → ((P n) = (∏ i_1 ∈ Finset.Icc (2 : ℤ) n, (((i_1 + 2) * (i_1 - 1)) /. (i_1 * (i_1 + 1))))))))))
  (h5 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → ((P n) = ((1 /. 3) * ((n + 2) /. n))))))
  (h6 : Tendsto (fun n : ℕ => (P n)) atTop (𝓝 (1 /. 3)))
  (h7 : (∏' n, if (2 : ℕ) ≤ n then (1 - (2 /. (n * (n + 1)))) else 1) = (1 /. 3))
  : (∏' n, if (2 : ℕ) ≤ n then (1 - (2 /. (n * (n + 1)))) else 1) = (1 /. 3) := by
  sorry

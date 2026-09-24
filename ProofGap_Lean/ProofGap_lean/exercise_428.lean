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

-- exercise: exercise_428

theorem proof_gap_exercise_428_1
  (m : ℕ)
  (n : ℕ)
  (h1 : (m ∈ (Set.univ : Set ℕ)) ∧ (m > 0))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h3 : m ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  : (m = n) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → (((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n)))) = 0))) := by
  sorry

theorem proof_gap_exercise_428_2
  (m : ℕ)
  (n : ℕ)
  (h1 : (m ∈ (Set.univ : Set ℕ)) ∧ (m > 0))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h3 : m ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h5 : (m = n) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → (((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n)))) = 0))))
  : (m = n) → (Tendsto (fun x : ℝ => ((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n))))) (𝓝[≠] 1) (𝓝 0)) := by
  sorry

theorem proof_gap_exercise_428_3
  (m : ℕ)
  (n : ℕ)
  (h1 : (m ∈ (Set.univ : Set ℕ)) ∧ (m > 0))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h3 : m ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h5 : (m = n) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → (((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n)))) = 0))))
  (h6 : (m = n) → (Tendsto (fun x : ℝ => ((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n))))) (𝓝[≠] 1) (𝓝 0)))
  : (m = n) → (0 = ((m - n) /. 2)) := by
  sorry

theorem proof_gap_exercise_428_4
  (m : ℕ)
  (n : ℕ)
  (h1 : (m ∈ (Set.univ : Set ℕ)) ∧ (m > 0))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h3 : m ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h5 : (m = n) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → (((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n)))) = 0))))
  (h6 : (m = n) → (Tendsto (fun x : ℝ => ((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n))))) (𝓝[≠] 1) (𝓝 0)))
  (h7 : (m = n) → (0 = ((m - n) /. 2)))
  : (m = n) → (Tendsto (fun x : ℝ => ((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n))))) (𝓝[≠] 1) (𝓝 ((m - n) /. 2))) := by
  sorry

theorem proof_gap_exercise_428_5
  (m : ℕ)
  (n : ℕ)
  (h1 : (m ∈ (Set.univ : Set ℕ)) ∧ (m > 0))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h3 : m ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h5 : (m = n) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → (((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n)))) = 0))))
  (h6 : (m = n) → (Tendsto (fun x : ℝ => ((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n))))) (𝓝[≠] 1) (𝓝 0)))
  (h7 : (m = n) → (0 = ((m - n) /. 2)))
  (h8 : (m = n) → (Tendsto (fun x : ℝ => ((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n))))) (𝓝[≠] 1) (𝓝 ((m - n) /. 2))))
  (h9 : (m < n) → (l = (n - m)))
  : (m < n) → (l ∈ ({n_1 : ℕ | 0 < n_1})) := by
  sorry

theorem proof_gap_exercise_428_6
  (m : ℕ)
  (n : ℕ)
  (h1 : (m ∈ (Set.univ : Set ℕ)) ∧ (m > 0))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h3 : m ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h5 : (m = n) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → (((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n)))) = 0))))
  (h6 : (m = n) → (Tendsto (fun x : ℝ => ((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n))))) (𝓝[≠] 1) (𝓝 0)))
  (h7 : (m = n) → (0 = ((m - n) /. 2)))
  (h8 : (m = n) → (Tendsto (fun x : ℝ => ((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n))))) (𝓝[≠] 1) (𝓝 ((m - n) /. 2))))
  (h9 : (m < n) → (l = (n - m)))
  (h10 : (m < n) → (l ∈ ({n_1 : ℕ | 0 < n_1})))
  : (m < n) → (n = (m + l)) := by
  sorry

theorem proof_gap_exercise_428_7
  (m : ℕ)
  (n : ℕ)
  (h1 : (m ∈ (Set.univ : Set ℕ)) ∧ (m > 0))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h3 : m ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h5 : (m = n) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → (((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n)))) = 0))))
  (h6 : (m = n) → (Tendsto (fun x : ℝ => ((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n))))) (𝓝[≠] 1) (𝓝 0)))
  (h7 : (m = n) → (0 = ((m - n) /. 2)))
  (h8 : (m = n) → (Tendsto (fun x : ℝ => ((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n))))) (𝓝[≠] 1) (𝓝 ((m - n) /. 2))))
  (h9 : (m < n) → (l = (n - m)))
  (h10 : (m < n) → (l ∈ ({n_1 : ℕ | 0 < n_1})))
  (h11 : (m < n) → (n = (m + l)))
  : (m < n) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → (((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n)))) = (((m * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (x ^ i))) - (n * (∑ j ∈ Finset.Icc (0 : ℕ) (m - 1), (x ^ j)))) /. (((1 - x) * (∑ j ∈ Finset.Icc (0 : ℕ) (m - 1), (x ^ j))) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (x ^ i))))))) := by
  sorry

theorem proof_gap_exercise_428_8
  (m : ℕ)
  (n : ℕ)
  (h1 : (m ∈ (Set.univ : Set ℕ)) ∧ (m > 0))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h3 : m ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h5 : (m = n) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → (((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n)))) = 0))))
  (h6 : (m = n) → (Tendsto (fun x : ℝ => ((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n))))) (𝓝[≠] 1) (𝓝 0)))
  (h7 : (m = n) → (0 = ((m - n) /. 2)))
  (h8 : (m = n) → (Tendsto (fun x : ℝ => ((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n))))) (𝓝[≠] 1) (𝓝 ((m - n) /. 2))))
  (h9 : (m < n) → (l = (n - m)))
  (h10 : (m < n) → (l ∈ ({n_1 : ℕ | 0 < n_1})))
  (h11 : (m < n) → (n = (m + l)))
  (h12 : (m < n) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((x ^ m) ≠ 1)) ∧ ((x ^ n) ≠ 1)) → (((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n)))) = (((m * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (x ^ i))) - (n * (∑ j ∈ Finset.Icc (0 : ℕ) (m - 1), (x ^ j)))) /. (((1 - x) * (∑ j ∈ Finset.Icc (0 : ℕ) (m - 1), (x ^ j))) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (x ^ i))))))))
  : (m < n) → (Tendsto (fun x : ℝ => ((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n))))) (𝓝[≠] 1) (𝓝 (-(((m * (∑ r ∈ Finset.Icc (1 : ℕ) (l - 1), r)) + (l * (∑ s ∈ Finset.Icc (1 : ℕ) m, s))) /. (m * n))))) := by
  sorry

theorem proof_gap_exercise_428_9
  (m : ℕ)
  (n : ℕ)
  (h1 : (m ∈ (Set.univ : Set ℕ)) ∧ (m > 0))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h3 : m ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h5 : (m = n) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → (((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n)))) = 0))))
  (h6 : (m = n) → (Tendsto (fun x : ℝ => ((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n))))) (𝓝[≠] 1) (𝓝 0)))
  (h7 : (m = n) → (0 = ((m - n) /. 2)))
  (h8 : (m = n) → (Tendsto (fun x : ℝ => ((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n))))) (𝓝[≠] 1) (𝓝 ((m - n) /. 2))))
  (h9 : (m < n) → (l = (n - m)))
  (h10 : (m < n) → (l ∈ ({n_1 : ℕ | 0 < n_1})))
  (h11 : (m < n) → (n = (m + l)))
  (h12 : (m < n) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((x ^ m) ≠ 1)) ∧ ((x ^ n) ≠ 1)) → (((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n)))) = (((m * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (x ^ i))) - (n * (∑ j ∈ Finset.Icc (0 : ℕ) (m - 1), (x ^ j)))) /. (((1 - x) * (∑ j ∈ Finset.Icc (0 : ℕ) (m - 1), (x ^ j))) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (x ^ i))))))))
  (h13 : (m < n) → (Tendsto (fun x : ℝ => ((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n))))) (𝓝[≠] 1) (𝓝 (-(((m * (∑ r ∈ Finset.Icc (1 : ℕ) (l - 1), r)) + (l * (∑ s ∈ Finset.Icc (1 : ℕ) m, s))) /. (m * n))))))
  : (m < n) → ((-(((m * (∑ r ∈ Finset.Icc (1 : ℕ) (l - 1), r)) + (l * (∑ s ∈ Finset.Icc (1 : ℕ) m, s))) /. (m * n))) = (-(((((m * l) * (l - 1)) /. 2) + (((m * l) * (m + 1)) /. 2)) /. (m * n)))) := by
  sorry

theorem proof_gap_exercise_428_10
  (m : ℕ)
  (n : ℕ)
  (h1 : (m ∈ (Set.univ : Set ℕ)) ∧ (m > 0))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h3 : m ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h5 : (m = n) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → (((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n)))) = 0))))
  (h6 : (m = n) → (Tendsto (fun x : ℝ => ((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n))))) (𝓝[≠] 1) (𝓝 0)))
  (h7 : (m = n) → (0 = ((m - n) /. 2)))
  (h8 : (m = n) → (Tendsto (fun x : ℝ => ((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n))))) (𝓝[≠] 1) (𝓝 ((m - n) /. 2))))
  (h9 : (m < n) → (l = (n - m)))
  (h10 : (m < n) → (l ∈ ({n_1 : ℕ | 0 < n_1})))
  (h11 : (m < n) → (n = (m + l)))
  (h12 : (m < n) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((x ^ m) ≠ 1)) ∧ ((x ^ n) ≠ 1)) → (((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n)))) = (((m * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (x ^ i))) - (n * (∑ j ∈ Finset.Icc (0 : ℕ) (m - 1), (x ^ j)))) /. (((1 - x) * (∑ j ∈ Finset.Icc (0 : ℕ) (m - 1), (x ^ j))) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (x ^ i))))))))
  (h13 : (m < n) → (Tendsto (fun x : ℝ => ((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n))))) (𝓝[≠] 1) (𝓝 (-(((m * (∑ r ∈ Finset.Icc (1 : ℕ) (l - 1), r)) + (l * (∑ s ∈ Finset.Icc (1 : ℕ) m, s))) /. (m * n))))))
  (h14 : (m < n) → ((-(((m * (∑ r ∈ Finset.Icc (1 : ℕ) (l - 1), r)) + (l * (∑ s ∈ Finset.Icc (1 : ℕ) m, s))) /. (m * n))) = (-(((((m * l) * (l - 1)) /. 2) + (((m * l) * (m + 1)) /. 2)) /. (m * n)))))
  : (m < n) → ((-(((((m * l) * (l - 1)) /. 2) + (((m * l) * (m + 1)) /. 2)) /. (m * n))) = ((m - n) /. 2)) := by
  sorry

theorem proof_gap_exercise_428_11
  (m : ℕ)
  (n : ℕ)
  (h1 : (m ∈ (Set.univ : Set ℕ)) ∧ (m > 0))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h3 : m ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h5 : (m = n) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → (((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n)))) = 0))))
  (h6 : (m = n) → (Tendsto (fun x : ℝ => ((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n))))) (𝓝[≠] 1) (𝓝 0)))
  (h7 : (m = n) → (0 = ((m - n) /. 2)))
  (h8 : (m = n) → (Tendsto (fun x : ℝ => ((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n))))) (𝓝[≠] 1) (𝓝 ((m - n) /. 2))))
  (h9 : (m < n) → (l = (n - m)))
  (h10 : (m < n) → (l ∈ ({n_1 : ℕ | 0 < n_1})))
  (h11 : (m < n) → (n = (m + l)))
  (h12 : (m < n) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → (((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n)))) = (((m * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (x ^ i))) - (n * (∑ j ∈ Finset.Icc (0 : ℕ) (m - 1), (x ^ j)))) /. (((1 - x) * (∑ j ∈ Finset.Icc (0 : ℕ) (m - 1), (x ^ j))) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (x ^ i))))))))
  (h13 : (m < n) → (Tendsto (fun x : ℝ => ((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n))))) (𝓝[≠] 1) (𝓝 (-(((m * (∑ r ∈ Finset.Icc (1 : ℕ) (l - 1), r)) + (l * (∑ s ∈ Finset.Icc (1 : ℕ) m, s))) /. (m * n))))))
  (h14 : (m < n) → ((-(((m * (∑ r ∈ Finset.Icc (1 : ℕ) (l - 1), r)) + (l * (∑ s ∈ Finset.Icc (1 : ℕ) m, s))) /. (m * n))) = (-(((((m * l) * (l - 1)) /. 2) + (((m * l) * (m + 1)) /. 2)) /. (m * n)))))
  (h15 : (m < n) → ((-(((((m * l) * (l - 1)) /. 2) + (((m * l) * (m + 1)) /. 2)) /. (m * n))) = ((m - n) /. 2)))
  : (m < n) → ((-(((m * (∑ r ∈ Finset.Icc (1 : ℕ) (l - 1), r)) + (l * (∑ s ∈ Finset.Icc (1 : ℕ) m, s))) /. (m * n))) = ((m - n) /. 2)) := by
  sorry

theorem proof_gap_exercise_428_12
  (m : ℕ)
  (n : ℕ)
  (h1 : (m ∈ (Set.univ : Set ℕ)) ∧ (m > 0))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h3 : m ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h5 : (m = n) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → (((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n)))) = 0))))
  (h6 : (m = n) → (Tendsto (fun x : ℝ => ((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n))))) (𝓝[≠] 1) (𝓝 0)))
  (h7 : (m = n) → (0 = ((m - n) /. 2)))
  (h8 : (m = n) → (Tendsto (fun x : ℝ => ((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n))))) (𝓝[≠] 1) (𝓝 ((m - n) /. 2))))
  (h9 : (m < n) → (l = (n - m)))
  (h10 : (m < n) → (l ∈ ({n_1 : ℕ | 0 < n_1})))
  (h11 : (m < n) → (n = (m + l)))
  (h12 : (m < n) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((x ^ m) ≠ 1)) ∧ ((x ^ n) ≠ 1)) → (((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n)))) = (((m * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (x ^ i))) - (n * (∑ j ∈ Finset.Icc (0 : ℕ) (m - 1), (x ^ j)))) /. (((1 - x) * (∑ j ∈ Finset.Icc (0 : ℕ) (m - 1), (x ^ j))) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (x ^ i))))))))
  (h13 : (m < n) → (Tendsto (fun x : ℝ => ((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n))))) (𝓝[≠] 1) (𝓝 (-(((m * (∑ r ∈ Finset.Icc (1 : ℕ) (l - 1), r)) + (l * (∑ s ∈ Finset.Icc (1 : ℕ) m, s))) /. (m * n))))))
  (h14 : (m < n) → ((-(((m * (∑ r ∈ Finset.Icc (1 : ℕ) (l - 1), r)) + (l * (∑ s ∈ Finset.Icc (1 : ℕ) m, s))) /. (m * n))) = (-(((((m * l) * (l - 1)) /. 2) + (((m * l) * (m + 1)) /. 2)) /. (m * n)))))
  (h15 : (m < n) → ((-(((((m * l) * (l - 1)) /. 2) + (((m * l) * (m + 1)) /. 2)) /. (m * n))) = ((m - n) /. 2)))
  (h16 : (m < n) → ((-(((m * (∑ r ∈ Finset.Icc (1 : ℕ) (l - 1), r)) + (l * (∑ s ∈ Finset.Icc (1 : ℕ) m, s))) /. (m * n))) = ((m - n) /. 2)))
  : (n < m) → (Tendsto (fun x : ℝ => ((n /. (1 - (x ^ n))) - (m /. (1 - (x ^ m))))) (𝓝[≠] 1) (𝓝 ((n - m) /. 2))) := by
  sorry

theorem proof_gap_exercise_428_13
  (m : ℕ)
  (n : ℕ)
  (h1 : (m ∈ (Set.univ : Set ℕ)) ∧ (m > 0))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h3 : m ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h5 : (m = n) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → (((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n)))) = 0))))
  (h6 : (m = n) → (Tendsto (fun x : ℝ => ((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n))))) (𝓝[≠] 1) (𝓝 0)))
  (h7 : (m = n) → (0 = ((m - n) /. 2)))
  (h8 : (m = n) → (Tendsto (fun x : ℝ => ((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n))))) (𝓝[≠] 1) (𝓝 ((m - n) /. 2))))
  (h9 : (m < n) → (l = (n - m)))
  (h10 : (m < n) → (l ∈ ({n_1 : ℕ | 0 < n_1})))
  (h11 : (m < n) → (n = (m + l)))
  (h12 : (m < n) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((x ^ m) ≠ 1)) ∧ ((x ^ n) ≠ 1)) → (((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n)))) = (((m * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (x ^ i))) - (n * (∑ j ∈ Finset.Icc (0 : ℕ) (m - 1), (x ^ j)))) /. (((1 - x) * (∑ j ∈ Finset.Icc (0 : ℕ) (m - 1), (x ^ j))) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (x ^ i))))))))
  (h13 : (m < n) → (Tendsto (fun x : ℝ => ((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n))))) (𝓝[≠] 1) (𝓝 (-(((m * (∑ r ∈ Finset.Icc (1 : ℕ) (l - 1), r)) + (l * (∑ s ∈ Finset.Icc (1 : ℕ) m, s))) /. (m * n))))))
  (h14 : (m < n) → ((-(((m * (∑ r ∈ Finset.Icc (1 : ℕ) (l - 1), r)) + (l * (∑ s ∈ Finset.Icc (1 : ℕ) m, s))) /. (m * n))) = (-(((((m * l) * (l - 1)) /. 2) + (((m * l) * (m + 1)) /. 2)) /. (m * n)))))
  (h15 : (m < n) → ((-(((((m * l) * (l - 1)) /. 2) + (((m * l) * (m + 1)) /. 2)) /. (m * n))) = ((m - n) /. 2)))
  (h16 : (m < n) → ((-(((m * (∑ r ∈ Finset.Icc (1 : ℕ) (l - 1), r)) + (l * (∑ s ∈ Finset.Icc (1 : ℕ) m, s))) /. (m * n))) = ((m - n) /. 2)))
  (h17 : (n < m) → (Tendsto (fun x : ℝ => ((n /. (1 - (x ^ n))) - (m /. (1 - (x ^ m))))) (𝓝[≠] 1) (𝓝 ((n - m) /. 2))))
  : (n < m) → (Tendsto (fun x : ℝ => ((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n))))) (𝓝[≠] 1) (𝓝 ((m - n) /. 2))) := by
  sorry

theorem proof_gap_exercise_428_14
  (m : ℕ)
  (n : ℕ)
  (h1 : (m ∈ (Set.univ : Set ℕ)) ∧ (m > 0))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h3 : m ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h5 : (m = n) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → (((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n)))) = 0))))
  (h6 : (m = n) → (Tendsto (fun x : ℝ => ((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n))))) (𝓝[≠] 1) (𝓝 0)))
  (h7 : (m = n) → (0 = ((m - n) /. 2)))
  (h8 : (m = n) → (Tendsto (fun x : ℝ => ((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n))))) (𝓝[≠] 1) (𝓝 ((m - n) /. 2))))
  (h9 : (m < n) → (l = (n - m)))
  (h10 : (m < n) → (l ∈ ({n_1 : ℕ | 0 < n_1})))
  (h11 : (m < n) → (n = (m + l)))
  (h12 : (m < n) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → (((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n)))) = (((m * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (x ^ i))) - (n * (∑ j ∈ Finset.Icc (0 : ℕ) (m - 1), (x ^ j)))) /. (((1 - x) * (∑ j ∈ Finset.Icc (0 : ℕ) (m - 1), (x ^ j))) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (x ^ i))))))))
  (h13 : (m < n) → (Tendsto (fun x : ℝ => ((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n))))) (𝓝[≠] 1) (𝓝 (-(((m * (∑ r ∈ Finset.Icc (1 : ℕ) (l - 1), r)) + (l * (∑ s ∈ Finset.Icc (1 : ℕ) m, s))) /. (m * n))))))
  (h14 : (m < n) → ((-(((m * (∑ r ∈ Finset.Icc (1 : ℕ) (l - 1), r)) + (l * (∑ s ∈ Finset.Icc (1 : ℕ) m, s))) /. (m * n))) = (-(((((m * l) * (l - 1)) /. 2) + (((m * l) * (m + 1)) /. 2)) /. (m * n)))))
  (h15 : (m < n) → ((-(((((m * l) * (l - 1)) /. 2) + (((m * l) * (m + 1)) /. 2)) /. (m * n))) = ((m - n) /. 2)))
  (h16 : (m < n) → ((-(((m * (∑ r ∈ Finset.Icc (1 : ℕ) (l - 1), r)) + (l * (∑ s ∈ Finset.Icc (1 : ℕ) m, s))) /. (m * n))) = ((m - n) /. 2)))
  (h17 : (n < m) → (Tendsto (fun x : ℝ => ((n /. (1 - (x ^ n))) - (m /. (1 - (x ^ m))))) (𝓝[≠] 1) (𝓝 ((n - m) /. 2))))
  (h18 : (n < m) → (Tendsto (fun x : ℝ => ((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n))))) (𝓝[≠] 1) (𝓝 ((m - n) /. 2))))
  : Tendsto (fun x : ℝ => ((m /. (1 - (x ^ m))) - (n /. (1 - (x ^ n))))) (𝓝[≠] 1) (𝓝 ((m - n) /. 2)) := by
  sorry

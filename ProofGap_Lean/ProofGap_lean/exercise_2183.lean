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

-- exercise: exercise_2183

theorem proof_gap_exercise_2183_1
  (f : (ℝ -> ℝ))
  (S_lower : (ℕ -> ℝ))
  (x : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h2 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc 1 2))) → ((f x_1) = (x_1 ^ (4 : ℕ))))))
  (h3 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : q = (Real.rpow (2 : ℝ) (((n : ℝ))⁻¹)))
  : q > 0 := by
  sorry

theorem proof_gap_exercise_2183_2
  (f : (ℝ -> ℝ))
  (S_lower : (ℕ -> ℝ))
  (x : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h2 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc 1 2))) → ((f x_1) = (x_1 ^ (4 : ℕ))))))
  (h3 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : q = (Real.rpow (2 : ℝ) (((n : ℝ))⁻¹)))
  (h5 : q > 0)
  : 2 = (q ^ n) := by
  sorry

theorem proof_gap_exercise_2183_3
  (f : (ℝ -> ℝ))
  (S_lower : (ℕ -> ℝ))
  (x : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h2 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc 1 2))) → ((f x_1) = (x_1 ^ (4 : ℕ))))))
  (h3 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : q = (Real.rpow (2 : ℝ) (((n : ℝ))⁻¹)))
  (h5 : q > 0)
  (h6 : 2 = (q ^ n))
  : (forall (i : ℕ), (((i ∈ (Set.univ : Set ℕ)) ∧ (i ≤ n)) → ((x i) = (q ^ i)))) := by
  sorry

theorem proof_gap_exercise_2183_4
  (f : (ℝ -> ℝ))
  (S_lower : (ℕ -> ℝ))
  (x : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h2 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc 1 2))) → ((f x_1) = (x_1 ^ (4 : ℕ))))))
  (h3 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : q = (Real.rpow (2 : ℝ) (((n : ℝ))⁻¹)))
  (h5 : q > 0)
  (h6 : 2 = (q ^ n))
  (h7 : (forall (i : ℕ), (((i ∈ (Set.univ : Set ℕ)) ∧ (i ≤ n)) → ((x i) = (q ^ i)))))
  : (x (0 : ℕ)) = 1 := by
  sorry

theorem proof_gap_exercise_2183_5
  (f : (ℝ -> ℝ))
  (S_lower : (ℕ -> ℝ))
  (x : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h2 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc 1 2))) → ((f x_1) = (x_1 ^ (4 : ℕ))))))
  (h3 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : q = (Real.rpow (2 : ℝ) (((n : ℝ))⁻¹)))
  (h5 : q > 0)
  (h6 : 2 = (q ^ n))
  (h7 : (forall (i : ℕ), (((i ∈ (Set.univ : Set ℕ)) ∧ (i ≤ n)) → ((x i) = (q ^ i)))))
  (h8 : (x (0 : ℕ)) = 1)
  : (x n) = 2 := by
  sorry

theorem proof_gap_exercise_2183_6
  (f : (ℝ -> ℝ))
  (S_lower : (ℕ -> ℝ))
  (x : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h2 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc 1 2))) → ((f x_1) = (x_1 ^ (4 : ℕ))))))
  (h3 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : q = (Real.rpow (2 : ℝ) (((n : ℝ))⁻¹)))
  (h5 : q > 0)
  (h6 : 2 = (q ^ n))
  (h7 : (forall (i : ℕ), (((i ∈ (Set.univ : Set ℕ)) ∧ (i ≤ n)) → ((x i) = (q ^ i)))))
  (h8 : (x (0 : ℕ)) = 1)
  (h9 : (x n) = 2)
  : StrictMonoOn f (Set.Icc 1 2) := by
  sorry

theorem proof_gap_exercise_2183_7
  (f : (ℝ -> ℝ))
  (S_lower : (ℕ -> ℝ))
  (x : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h2 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc 1 2))) → ((f x_1) = (x_1 ^ (4 : ℕ))))))
  (h3 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : q = (Real.rpow (2 : ℝ) (((n : ℝ))⁻¹)))
  (h5 : q > 0)
  (h6 : 2 = (q ^ n))
  (h7 : (forall (i : ℕ), (((i ∈ (Set.univ : Set ℕ)) ∧ (i ≤ n)) → ((x i) = (q ^ i)))))
  (h8 : (x (0 : ℕ)) = 1)
  (h9 : (x n) = 2)
  (h10 : StrictMonoOn f (Set.Icc 1 2))
  : (S_lower n) = (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (((q ^ i) ^ (4 : ℕ)) * ((q ^ (i + 1)) - (q ^ i)))) := by
  sorry

theorem proof_gap_exercise_2183_8
  (f : (ℝ -> ℝ))
  (S_lower : (ℕ -> ℝ))
  (x : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h2 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc 1 2))) → ((f x_1) = (x_1 ^ (4 : ℕ))))))
  (h3 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : q = (Real.rpow (2 : ℝ) (((n : ℝ))⁻¹)))
  (h5 : q > 0)
  (h6 : 2 = (q ^ n))
  (h7 : (forall (i : ℕ), (((i ∈ (Set.univ : Set ℕ)) ∧ (i ≤ n)) → ((x i) = (q ^ i)))))
  (h8 : (x (0 : ℕ)) = 1)
  (h9 : (x n) = 2)
  (h10 : StrictMonoOn f (Set.Icc 1 2))
  (h11 : (S_lower n) = (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (((q ^ i) ^ (4 : ℕ)) * ((q ^ (i + 1)) - (q ^ i)))))
  : (S_lower n) = ((q - 1) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), ((q ^ i) ^ (5 : ℕ)))) := by
  sorry

theorem proof_gap_exercise_2183_9
  (f : (ℝ -> ℝ))
  (S_lower : (ℕ -> ℝ))
  (x : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h2 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc 1 2))) → ((f x_1) = (x_1 ^ (4 : ℕ))))))
  (h3 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : q = (Real.rpow (2 : ℝ) (((n : ℝ))⁻¹)))
  (h5 : q > 0)
  (h6 : 2 = (q ^ n))
  (h7 : (forall (i : ℕ), (((i ∈ (Set.univ : Set ℕ)) ∧ (i ≤ n)) → ((x i) = (q ^ i)))))
  (h8 : (x (0 : ℕ)) = 1)
  (h9 : (x n) = 2)
  (h10 : StrictMonoOn f (Set.Icc 1 2))
  (h11 : (S_lower n) = (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (((q ^ i) ^ (4 : ℕ)) * ((q ^ (i + 1)) - (q ^ i)))))
  (h12 : (S_lower n) = ((q - 1) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), ((q ^ i) ^ (5 : ℕ)))))
  : (S_lower n) = (((q - 1) * ((q ^ (5 * n)) - 1)) /. ((q ^ (5 : ℕ)) - 1)) := by
  sorry

theorem proof_gap_exercise_2183_10
  (f : (ℝ -> ℝ))
  (S_lower : (ℕ -> ℝ))
  (x : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h2 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc 1 2))) → ((f x_1) = (x_1 ^ (4 : ℕ))))))
  (h3 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : q = (Real.rpow (2 : ℝ) (((n : ℝ))⁻¹)))
  (h5 : q > 0)
  (h6 : 2 = (q ^ n))
  (h7 : (forall (i : ℕ), (((i ∈ (Set.univ : Set ℕ)) ∧ (i ≤ n)) → ((x i) = (q ^ i)))))
  (h8 : (x (0 : ℕ)) = 1)
  (h9 : (x n) = 2)
  (h10 : StrictMonoOn f (Set.Icc 1 2))
  (h11 : (S_lower n) = (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (((q ^ i) ^ (4 : ℕ)) * ((q ^ (i + 1)) - (q ^ i)))))
  (h12 : (S_lower n) = ((q - 1) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), ((q ^ i) ^ (5 : ℕ)))))
  (h13 : (S_lower n) = (((q - 1) * ((q ^ (5 * n)) - 1)) /. ((q ^ (5 : ℕ)) - 1)))
  : (S_lower n) = ((31 * ((Real.rpow (2 : ℝ) (((n : ℝ))⁻¹)) - 1)) /. ((Real.rpow (32 : ℝ) (((n : ℝ))⁻¹)) - 1)) := by
  sorry

theorem proof_gap_exercise_2183_11
  (f : (ℝ -> ℝ))
  (S_lower : (ℕ -> ℝ))
  (x : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h2 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc 1 2))) → ((f x_1) = (x_1 ^ (4 : ℕ))))))
  (h3 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : q = (Real.rpow (2 : ℝ) (((n : ℝ))⁻¹)))
  (h5 : q > 0)
  (h6 : 2 = (q ^ n))
  (h7 : (forall (i : ℕ), (((i ∈ (Set.univ : Set ℕ)) ∧ (i ≤ n)) → ((x i) = (q ^ i)))))
  (h8 : (x (0 : ℕ)) = 1)
  (h9 : (x n) = 2)
  (h10 : StrictMonoOn f (Set.Icc 1 2))
  (h11 : (S_lower n) = (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (((q ^ i) ^ (4 : ℕ)) * ((q ^ (i + 1)) - (q ^ i)))))
  (h12 : (S_lower n) = ((q - 1) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), ((q ^ i) ^ (5 : ℕ)))))
  (h13 : (S_lower n) = (((q - 1) * ((q ^ (5 * n)) - 1)) /. ((q ^ (5 : ℕ)) - 1)))
  (h14 : (S_lower n) = ((31 * ((Real.rpow (2 : ℝ) (((n : ℝ))⁻¹)) - 1)) /. ((Real.rpow (32 : ℝ) (((n : ℝ))⁻¹)) - 1)))
  : (∃ L : ℝ, Tendsto (fun n_1 : ℕ => (31 * (((Real.rpow (2 : ℝ) ((n_1)⁻¹)) - 1) /. ((Real.rpow (32 : ℝ) ((n_1)⁻¹)) - 1)))) atTop (𝓝 L) ∧ (Tendsto (fun n_1 : ℕ => (S_lower n_1)) atTop (𝓝 (atTop.limUnder (fun n_1 : ℕ => (31 * (((Real.rpow (2 : ℝ) ((n_1)⁻¹)) - 1) /. ((Real.rpow (32 : ℝ) ((n_1)⁻¹)) - 1)))))))) := by
  sorry

theorem proof_gap_exercise_2183_12
  (f : (ℝ -> ℝ))
  (S_lower : (ℕ -> ℝ))
  (x : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h2 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc 1 2))) → ((f x_1) = (x_1 ^ (4 : ℕ))))))
  (h3 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : q = (Real.rpow (2 : ℝ) (((n : ℝ))⁻¹)))
  (h5 : q > 0)
  (h6 : 2 = (q ^ n))
  (h7 : (forall (i : ℕ), (((i ∈ (Set.univ : Set ℕ)) ∧ (i ≤ n)) → ((x i) = (q ^ i)))))
  (h8 : (x (0 : ℕ)) = 1)
  (h9 : (x n) = 2)
  (h10 : StrictMonoOn f (Set.Icc 1 2))
  (h11 : (S_lower n) = (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (((q ^ i) ^ (4 : ℕ)) * ((q ^ (i + 1)) - (q ^ i)))))
  (h12 : (S_lower n) = ((q - 1) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), ((q ^ i) ^ (5 : ℕ)))))
  (h13 : (S_lower n) = (((q - 1) * ((q ^ (5 * n)) - 1)) /. ((q ^ (5 : ℕ)) - 1)))
  (h14 : (S_lower n) = ((31 * ((Real.rpow (2 : ℝ) (((n : ℝ))⁻¹)) - 1)) /. ((Real.rpow (32 : ℝ) (((n : ℝ))⁻¹)) - 1)))
  (h15 : Tendsto (fun n_1 : ℕ => (S_lower n_1)) atTop (𝓝 (atTop.limUnder (fun n_1 : ℕ => (31 * (((Real.rpow (2 : ℝ) ((n_1)⁻¹)) - 1) /. ((Real.rpow (32 : ℝ) ((n_1)⁻¹)) - 1)))))))
  (h16 : ∃ L : ℝ, Tendsto (fun n_1 : ℕ => (31 * (((Real.rpow (2 : ℝ) ((n_1)⁻¹)) - 1) /. ((Real.rpow (32 : ℝ) ((n_1)⁻¹)) - 1)))) atTop (𝓝 L))
  : (∃ L : ℝ, Tendsto (fun n_1 : ℕ => (31 * (1 /. (((((Real.rpow (16 : ℝ) ((n_1)⁻¹)) + (Real.rpow (8 : ℝ) ((n_1)⁻¹))) + (Real.rpow (4 : ℝ) ((n_1)⁻¹))) + (Real.rpow (2 : ℝ) ((n_1)⁻¹))) + 1)))) atTop (𝓝 L) ∧ (Tendsto (fun n_1 : ℕ => (S_lower n_1)) atTop (𝓝 (atTop.limUnder (fun n_1 : ℕ => (31 * (1 /. (((((Real.rpow (16 : ℝ) ((n_1)⁻¹)) + (Real.rpow (8 : ℝ) ((n_1)⁻¹))) + (Real.rpow (4 : ℝ) ((n_1)⁻¹))) + (Real.rpow (2 : ℝ) ((n_1)⁻¹))) + 1)))))))) := by
  sorry

theorem proof_gap_exercise_2183_13
  (f : (ℝ -> ℝ))
  (S_lower : (ℕ -> ℝ))
  (x : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h2 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc 1 2))) → ((f x_1) = (x_1 ^ (4 : ℕ))))))
  (h3 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : q = (Real.rpow (2 : ℝ) (((n : ℝ))⁻¹)))
  (h5 : q > 0)
  (h6 : 2 = (q ^ n))
  (h7 : (forall (i : ℕ), (((i ∈ (Set.univ : Set ℕ)) ∧ (i ≤ n)) → ((x i) = (q ^ i)))))
  (h8 : (x (0 : ℕ)) = 1)
  (h9 : (x n) = 2)
  (h10 : StrictMonoOn f (Set.Icc 1 2))
  (h11 : (S_lower n) = (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (((q ^ i) ^ (4 : ℕ)) * ((q ^ (i + 1)) - (q ^ i)))))
  (h12 : (S_lower n) = ((q - 1) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), ((q ^ i) ^ (5 : ℕ)))))
  (h13 : (S_lower n) = (((q - 1) * ((q ^ (5 * n)) - 1)) /. ((q ^ (5 : ℕ)) - 1)))
  (h14 : (S_lower n) = ((31 * ((Real.rpow (2 : ℝ) (((n : ℝ))⁻¹)) - 1)) /. ((Real.rpow (32 : ℝ) (((n : ℝ))⁻¹)) - 1)))
  (h15 : Tendsto (fun n_1 : ℕ => (S_lower n_1)) atTop (𝓝 (atTop.limUnder (fun n_1 : ℕ => (31 * (((Real.rpow (2 : ℝ) ((n_1)⁻¹)) - 1) /. ((Real.rpow (32 : ℝ) ((n_1)⁻¹)) - 1)))))))
  (h16 : Tendsto (fun n_1 : ℕ => (S_lower n_1)) atTop (𝓝 (atTop.limUnder (fun n_1 : ℕ => (31 * (1 /. (((((Real.rpow (16 : ℝ) ((n_1)⁻¹)) + (Real.rpow (8 : ℝ) ((n_1)⁻¹))) + (Real.rpow (4 : ℝ) ((n_1)⁻¹))) + (Real.rpow (2 : ℝ) ((n_1)⁻¹))) + 1)))))))
  (h17 : ∃ L : ℝ, Tendsto (fun n_1 : ℕ => (31 * (((Real.rpow (2 : ℝ) ((n_1)⁻¹)) - 1) /. ((Real.rpow (32 : ℝ) ((n_1)⁻¹)) - 1)))) atTop (𝓝 L))
  (h18 : ∃ L : ℝ, Tendsto (fun n_1 : ℕ => (31 * (1 /. (((((Real.rpow (16 : ℝ) ((n_1)⁻¹)) + (Real.rpow (8 : ℝ) ((n_1)⁻¹))) + (Real.rpow (4 : ℝ) ((n_1)⁻¹))) + (Real.rpow (2 : ℝ) ((n_1)⁻¹))) + 1)))) atTop (𝓝 L))
  : Tendsto (fun n_1 : ℕ => (S_lower n_1)) atTop (𝓝 (31 /. 5)) := by
  sorry

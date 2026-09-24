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

-- exercise: exercise_2182_2

theorem proof_gap_exercise_2182_2_1
  (f : (ℝ -> ℝ))
  (S_lower : (ℕ -> ℝ))
  (S_upper : (ℕ -> ℝ))
  (m : (ℤ -> ℝ))
  (M : (ℤ -> ℝ))
  (h : ℝ)
  (h1 : h ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((f x) = (Real.rpow x (((2 : ℝ))⁻¹))))))
  : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (n ∈ ({n_1 : ℕ | 0 < n_1})))) := by
  sorry

theorem proof_gap_exercise_2182_2_2
  (f : (ℝ -> ℝ))
  (S_lower : (ℕ -> ℝ))
  (S_upper : (ℕ -> ℝ))
  (m : (ℤ -> ℝ))
  (M : (ℤ -> ℝ))
  (h : ℝ)
  (h1 : h ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((f x) = (Real.rpow x (((2 : ℝ))⁻¹))))))
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (n ∈ ({n_1 : ℕ | 0 < n_1})))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (h = (1 /. n)))) := by
  sorry

theorem proof_gap_exercise_2182_2_3
  (f : (ℝ -> ℝ))
  (S_lower : (ℕ -> ℝ))
  (S_upper : (ℕ -> ℝ))
  (m : (ℤ -> ℝ))
  (M : (ℤ -> ℝ))
  (h : ℝ)
  (h1 : h ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((f x) = (Real.rpow x (((2 : ℝ))⁻¹))))))
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (n ∈ ({n_1 : ℕ | 0 < n_1})))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (h = (1 /. n)))))
  : MonotoneOn f (Set.Icc 0 1) := by
  sorry

theorem proof_gap_exercise_2182_2_4
  (f : (ℝ -> ℝ))
  (S_lower : (ℕ -> ℝ))
  (S_upper : (ℕ -> ℝ))
  (m : (ℤ -> ℝ))
  (M : (ℤ -> ℝ))
  (h : ℝ)
  (h1 : h ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((f x) = (Real.rpow x (((2 : ℝ))⁻¹))))))
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (n ∈ ({n_1 : ℕ | 0 < n_1})))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (h = (1 /. n)))))
  (h5 : MonotoneOn f (Set.Icc 0 1))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (i : ℤ), ((((i ∈ (Set.univ : Set ℤ)) ∧ (0 ≤ i)) ∧ (i ≤ (n - 1))) → ((m i) = (Real.rpow (i /. n) (((2 : ℝ))⁻¹))))))) := by
  sorry

theorem proof_gap_exercise_2182_2_5
  (f : (ℝ -> ℝ))
  (S_lower : (ℕ -> ℝ))
  (S_upper : (ℕ -> ℝ))
  (m : (ℤ -> ℝ))
  (M : (ℤ -> ℝ))
  (h : ℝ)
  (h1 : h ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((f x) = (Real.rpow x (((2 : ℝ))⁻¹))))))
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (n ∈ ({n_1 : ℕ | 0 < n_1})))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (h = (1 /. n)))))
  (h5 : MonotoneOn f (Set.Icc 0 1))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (i : ℤ), ((((i ∈ (Set.univ : Set ℤ)) ∧ (0 ≤ i)) ∧ (i ≤ (n - 1))) → ((m i) = (Real.rpow (i /. n) (((2 : ℝ))⁻¹))))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (i : ℤ), ((((i ∈ (Set.univ : Set ℤ)) ∧ (0 ≤ i)) ∧ (i ≤ (n - 1))) → ((M i) = (Real.rpow ((i + 1) /. n) (((2 : ℝ))⁻¹))))))) := by
  sorry

theorem proof_gap_exercise_2182_2_6
  (f : (ℝ -> ℝ))
  (S_lower : (ℕ -> ℝ))
  (S_upper : (ℕ -> ℝ))
  (m : (ℤ -> ℝ))
  (M : (ℤ -> ℝ))
  (h : ℝ)
  (h1 : h ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((f x) = (Real.rpow x (((2 : ℝ))⁻¹))))))
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (n ∈ ({n_1 : ℕ | 0 < n_1})))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (h = (1 /. n)))))
  (h5 : MonotoneOn f (Set.Icc 0 1))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (i : ℤ), ((((i ∈ (Set.univ : Set ℤ)) ∧ (0 ≤ i)) ∧ (i ≤ (n - 1))) → ((m i) = (Real.rpow (i /. n) (((2 : ℝ))⁻¹))))))))
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (i : ℤ), ((((i ∈ (Set.univ : Set ℤ)) ∧ (0 ≤ i)) ∧ (i ≤ (n - 1))) → ((M i) = (Real.rpow ((i + 1) /. n) (((2 : ℝ))⁻¹))))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S_lower n) = (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), ((m (i : ℤ)) * h))))) := by
  sorry

theorem proof_gap_exercise_2182_2_7
  (f : (ℝ -> ℝ))
  (S_lower : (ℕ -> ℝ))
  (S_upper : (ℕ -> ℝ))
  (m : (ℤ -> ℝ))
  (M : (ℤ -> ℝ))
  (h : ℝ)
  (h1 : h ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((f x) = (Real.rpow x (((2 : ℝ))⁻¹))))))
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (n ∈ ({n_1 : ℕ | 0 < n_1})))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (h = (1 /. n)))))
  (h5 : MonotoneOn f (Set.Icc 0 1))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (i : ℤ), ((((i ∈ (Set.univ : Set ℤ)) ∧ (0 ≤ i)) ∧ (i ≤ (n - 1))) → ((m i) = (Real.rpow (i /. n) (((2 : ℝ))⁻¹))))))))
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (i : ℤ), ((((i ∈ (Set.univ : Set ℤ)) ∧ (0 ≤ i)) ∧ (i ≤ (n - 1))) → ((M i) = (Real.rpow ((i + 1) /. n) (((2 : ℝ))⁻¹))))))))
  (h8 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S_lower n) = (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), ((m (i : ℤ)) * h))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S_lower n) = ((1 /. n) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (Real.rpow (i /. n) (((2 : ℝ))⁻¹))))))) := by
  sorry

theorem proof_gap_exercise_2182_2_8
  (f : (ℝ -> ℝ))
  (S_lower : (ℕ -> ℝ))
  (S_upper : (ℕ -> ℝ))
  (m : (ℤ -> ℝ))
  (M : (ℤ -> ℝ))
  (h : ℝ)
  (h1 : h ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((f x) = (Real.rpow x (((2 : ℝ))⁻¹))))))
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (n ∈ ({n_1 : ℕ | 0 < n_1})))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (h = (1 /. n)))))
  (h5 : MonotoneOn f (Set.Icc 0 1))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (i : ℤ), ((((i ∈ (Set.univ : Set ℤ)) ∧ (0 ≤ i)) ∧ (i ≤ (n - 1))) → ((m i) = (Real.rpow (i /. n) (((2 : ℝ))⁻¹))))))))
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (i : ℤ), ((((i ∈ (Set.univ : Set ℤ)) ∧ (0 ≤ i)) ∧ (i ≤ (n - 1))) → ((M i) = (Real.rpow ((i + 1) /. n) (((2 : ℝ))⁻¹))))))))
  (h8 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S_lower n) = (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), ((m (i : ℤ)) * h))))))
  (h9 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S_lower n) = ((1 /. n) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (Real.rpow (i /. n) (((2 : ℝ))⁻¹))))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S_upper n) = (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), ((M (i : ℤ)) * h))))) := by
  sorry

theorem proof_gap_exercise_2182_2_9
  (f : (ℝ -> ℝ))
  (S_lower : (ℕ -> ℝ))
  (S_upper : (ℕ -> ℝ))
  (m : (ℤ -> ℝ))
  (M : (ℤ -> ℝ))
  (h : ℝ)
  (h1 : h ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((f x) = (Real.rpow x (((2 : ℝ))⁻¹))))))
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (n ∈ ({n_1 : ℕ | 0 < n_1})))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (h = (1 /. n)))))
  (h5 : MonotoneOn f (Set.Icc 0 1))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (i : ℤ), ((((i ∈ (Set.univ : Set ℤ)) ∧ (0 ≤ i)) ∧ (i ≤ (n - 1))) → ((m i) = (Real.rpow (i /. n) (((2 : ℝ))⁻¹))))))))
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (i : ℤ), ((((i ∈ (Set.univ : Set ℤ)) ∧ (0 ≤ i)) ∧ (i ≤ (n - 1))) → ((M i) = (Real.rpow ((i + 1) /. n) (((2 : ℝ))⁻¹))))))))
  (h8 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S_lower n) = (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), ((m (i : ℤ)) * h))))))
  (h9 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S_lower n) = ((1 /. n) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (Real.rpow (i /. n) (((2 : ℝ))⁻¹))))))))
  (h10 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S_upper n) = (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), ((M (i : ℤ)) * h))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S_upper n) = ((1 /. n) * (∑ i ∈ Finset.Icc (1 : ℕ) n, (Real.rpow (i /. n) (((2 : ℝ))⁻¹))))))) := by
  sorry

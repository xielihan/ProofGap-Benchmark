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

-- exercise: exercise_2626

theorem proof_gap_exercise_2626_1
  (u : (ℤ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → ((u n) = (((Real.rpow (n + 2) (((2 : ℝ))⁻¹)) - (Real.rpow (n - 2) (((2 : ℝ))⁻¹))) /. (Real.rpow (n : ℝ) a))))))
  : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → (0 < (u n)))) := by
  sorry

theorem proof_gap_exercise_2626_2
  (u : (ℤ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → ((u n) = (((Real.rpow (n + 2) (((2 : ℝ))⁻¹)) - (Real.rpow (n - 2) (((2 : ℝ))⁻¹))) /. (Real.rpow (n : ℝ) a))))))
  (h3 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → (0 < (u n)))))
  : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → ((u n) = (4 /. ((Real.rpow (n : ℝ) a) * ((Real.rpow (n + 2) (((2 : ℝ))⁻¹)) + (Real.rpow (n - 2) (((2 : ℝ))⁻¹)))))))) := by
  sorry

theorem proof_gap_exercise_2626_3
  (u : (ℤ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → ((u n) = (((Real.rpow (n + 2) (((2 : ℝ))⁻¹)) - (Real.rpow (n - 2) (((2 : ℝ))⁻¹))) /. (Real.rpow (n : ℝ) a))))))
  (h3 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → (0 < (u n)))))
  (h4 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → ((u n) = (4 /. ((Real.rpow (n : ℝ) a) * ((Real.rpow (n + 2) (((2 : ℝ))⁻¹)) + (Real.rpow (n - 2) (((2 : ℝ))⁻¹)))))))))
  : Tendsto (fun n : ℕ => ((u (n : ℤ)) /. (1 /. (Real.rpow (n : ℝ) (a + (1 /. 2)))))) atTop (𝓝 2) := by
  sorry

theorem proof_gap_exercise_2626_4
  (u : (ℤ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → ((u n) = (((Real.rpow (n + 2) (((2 : ℝ))⁻¹)) - (Real.rpow (n - 2) (((2 : ℝ))⁻¹))) /. (Real.rpow (n : ℝ) a))))))
  (h3 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → (0 < (u n)))))
  (h4 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → ((u n) = (4 /. ((Real.rpow (n : ℝ) a) * ((Real.rpow (n + 2) (((2 : ℝ))⁻¹)) + (Real.rpow (n - 2) (((2 : ℝ))⁻¹)))))))))
  (h5 : Tendsto (fun n : ℕ => ((u (n : ℤ)) /. (1 /. (Real.rpow (n : ℝ) (a + (1 /. 2)))))) atTop (𝓝 2))
  : (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) (a + (1 /. 2)))) else 0)) ↔ ((a + (1 /. 2)) > 1) := by
  sorry

theorem proof_gap_exercise_2626_5
  (u : (ℤ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → ((u n) = (((Real.rpow (n + 2) (((2 : ℝ))⁻¹)) - (Real.rpow (n - 2) (((2 : ℝ))⁻¹))) /. (Real.rpow (n : ℝ) a))))))
  (h3 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → (0 < (u n)))))
  (h4 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → ((u n) = (4 /. ((Real.rpow (n : ℝ) a) * ((Real.rpow (n + 2) (((2 : ℝ))⁻¹)) + (Real.rpow (n - 2) (((2 : ℝ))⁻¹)))))))))
  (h5 : Tendsto (fun n : ℕ => ((u (n : ℤ)) /. (1 /. (Real.rpow (n : ℝ) (a + (1 /. 2)))))) atTop (𝓝 2))
  (h6 : (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) (a + (1 /. 2)))) else 0)) ↔ ((a + (1 /. 2)) > 1))
  : (Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then (u (n : ℤ)) else 0)) ↔ (a > (1 /. 2)) := by
  sorry

theorem proof_gap_exercise_2626_6
  (u : (ℤ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → ((u n) = (((Real.rpow (n + 2) (((2 : ℝ))⁻¹)) - (Real.rpow (n - 2) (((2 : ℝ))⁻¹))) /. (Real.rpow (n : ℝ) a))))))
  (h3 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → (0 < (u n)))))
  (h4 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → ((u n) = (4 /. ((Real.rpow (n : ℝ) a) * ((Real.rpow (n + 2) (((2 : ℝ))⁻¹)) + (Real.rpow (n - 2) (((2 : ℝ))⁻¹)))))))))
  (h5 : Tendsto (fun n : ℕ => ((u (n : ℤ)) /. (1 /. (Real.rpow (n : ℝ) (a + (1 /. 2)))))) atTop (𝓝 2))
  (h6 : (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) (a + (1 /. 2)))) else 0)) ↔ ((a + (1 /. 2)) > 1))
  (h7 : (Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then (u (n : ℤ)) else 0)) ↔ (a > (1 /. 2)))
  : (a ∈ ({a_1 | (a_1 ∈ (Set.univ : Set ℝ)) ∧ (a_1 > (1 /. 2))})) ↔ (Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then (u (n : ℤ)) else 0)) := by
  sorry

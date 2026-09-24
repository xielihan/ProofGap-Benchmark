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

-- exercise: exercise_2631

theorem proof_gap_exercise_2631_1
  (a : (ℕ -> ℝ))
  (A : ℝ)
  (n_0 : ℕ)
  (h1 : A ∈ (Set.univ : Set ℝ))
  (h2 : n_0 ∈ (Set.univ : Set ℕ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (Real.exp ((-(3 : ℝ)) * (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))))))))
  : (exists (A_1 : ℝ), (((A_1 ∈ (Set.univ : Set ℝ)) ∧ (A_1 ∈ ({x : ℝ | 0 < x}))) ∧ (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t > 0)) → ((Real.exp t) ≥ (A_1 * (t ^ (4 : ℕ)))))))) := by
  sorry

theorem proof_gap_exercise_2631_2
  (a : (ℕ -> ℝ))
  (A : ℝ)
  (n_0 : ℕ)
  (h1 : A ∈ (Set.univ : Set ℝ))
  (h2 : n_0 ∈ (Set.univ : Set ℕ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (Real.exp ((-(3 : ℝ)) * (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))))))))
  (h4 : (exists (A_1 : ℝ), (((A_1 ∈ (Set.univ : Set ℝ)) ∧ (A_1 ∈ ({x : ℝ | 0 < x}))) ∧ (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t > 0)) → ((Real.exp t) ≥ (A_1 * (t ^ (4 : ℕ)))))))))
  : (exists (n_0_1 : ℕ), (((n_0_1 ∈ (Set.univ : Set ℕ)) ∧ (n_0_1 ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ n_0_1)) → ((Real.exp (3 * (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹)))) ≥ (A * (Real.rpow (n : ℝ) (4 /. 3)))))))) := by
  sorry

theorem proof_gap_exercise_2631_3
  (a : (ℕ -> ℝ))
  (A : ℝ)
  (n_0 : ℕ)
  (h1 : A ∈ (Set.univ : Set ℝ))
  (h2 : n_0 ∈ (Set.univ : Set ℕ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (Real.exp ((-(3 : ℝ)) * (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))))))))
  (h4 : (exists (A_1 : ℝ), (((A_1 ∈ (Set.univ : Set ℝ)) ∧ (A_1 ∈ ({x : ℝ | 0 < x}))) ∧ (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t > 0)) → ((Real.exp t) ≥ (A_1 * (t ^ (4 : ℕ)))))))))
  (h5 : (exists (n_0_1 : ℕ), (((n_0_1 ∈ (Set.univ : Set ℕ)) ∧ (n_0_1 ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ n_0_1)) → ((Real.exp (3 * (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹)))) ≥ (A * (Real.rpow (n : ℝ) (4 /. 3)))))))))
  : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ n_0)) → ((0 < (Real.exp ((-(3 : ℝ)) * (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))))) ∧ ((Real.exp ((-(3 : ℝ)) * (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹)))) ≤ ((1 /. A) * (Real.rpow (n : ℝ) (-(4 /. 3)))))))) := by
  sorry

theorem proof_gap_exercise_2631_4
  (a : (ℕ -> ℝ))
  (A : ℝ)
  (n_0 : ℕ)
  (h1 : A ∈ (Set.univ : Set ℝ))
  (h2 : n_0 ∈ (Set.univ : Set ℕ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (Real.exp ((-(3 : ℝ)) * (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))))))))
  (h4 : (exists (A_1 : ℝ), (((A_1 ∈ (Set.univ : Set ℝ)) ∧ (A_1 ∈ ({x : ℝ | 0 < x}))) ∧ (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t > 0)) → ((Real.exp t) ≥ (A_1 * (t ^ (4 : ℕ)))))))))
  (h5 : (exists (n_0_1 : ℕ), (((n_0_1 ∈ (Set.univ : Set ℕ)) ∧ (n_0_1 ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ n_0_1)) → ((Real.exp (3 * (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹)))) ≥ (A * (Real.rpow (n : ℝ) (4 /. 3)))))))))
  (h6 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ n_0)) → ((0 < (Real.exp ((-(3 : ℝ)) * (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))))) ∧ ((Real.exp ((-(3 : ℝ)) * (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹)))) ≤ ((1 /. A) * (Real.rpow (n : ℝ) (-(4 /. 3)))))))))
  : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (Real.rpow (n : ℝ) (-(4 /. 3))) else 0) := by
  sorry

theorem proof_gap_exercise_2631_5
  (a : (ℕ -> ℝ))
  (A : ℝ)
  (n_0 : ℕ)
  (h1 : A ∈ (Set.univ : Set ℝ))
  (h2 : n_0 ∈ (Set.univ : Set ℕ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (Real.exp ((-(3 : ℝ)) * (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))))))))
  (h4 : (exists (A_1 : ℝ), (((A_1 ∈ (Set.univ : Set ℝ)) ∧ (A_1 ∈ ({x : ℝ | 0 < x}))) ∧ (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t > 0)) → ((Real.exp t) ≥ (A_1 * (t ^ (4 : ℕ)))))))))
  (h5 : (exists (n_0_1 : ℕ), (((n_0_1 ∈ (Set.univ : Set ℕ)) ∧ (n_0_1 ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ n_0_1)) → ((Real.exp (3 * (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹)))) ≥ (A * (Real.rpow (n : ℝ) (4 /. 3)))))))))
  (h6 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ n_0)) → ((0 < (Real.exp ((-(3 : ℝ)) * (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))))) ∧ ((Real.exp ((-(3 : ℝ)) * (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹)))) ≤ ((1 /. A) * (Real.rpow (n : ℝ) (-(4 /. 3)))))))))
  (h7 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (Real.rpow (n : ℝ) (-(4 /. 3))) else 0))
  : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (Real.exp ((-(3 : ℝ)) * (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹)))) else 0) := by
  sorry

theorem proof_gap_exercise_2631_6
  (a : (ℕ -> ℝ))
  (A : ℝ)
  (n_0 : ℕ)
  (h1 : A ∈ (Set.univ : Set ℝ))
  (h2 : n_0 ∈ (Set.univ : Set ℕ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (Real.exp ((-(3 : ℝ)) * (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))))))))
  (h4 : (exists (A_1 : ℝ), (((A_1 ∈ (Set.univ : Set ℝ)) ∧ (A_1 ∈ ({x : ℝ | 0 < x}))) ∧ (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t > 0)) → ((Real.exp t) ≥ (A_1 * (t ^ (4 : ℕ)))))))))
  (h5 : (exists (n_0_1 : ℕ), (((n_0_1 ∈ (Set.univ : Set ℕ)) ∧ (n_0_1 ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ n_0_1)) → ((Real.exp (3 * (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹)))) ≥ (A * (Real.rpow (n : ℝ) (4 /. 3)))))))))
  (h6 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ n_0)) → ((0 < (Real.exp ((-(3 : ℝ)) * (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))))) ∧ ((Real.exp ((-(3 : ℝ)) * (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹)))) ≤ ((1 /. A) * (Real.rpow (n : ℝ) (-(4 /. 3)))))))))
  (h7 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (Real.rpow (n : ℝ) (-(4 /. 3))) else 0))
  (h8 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (Real.exp ((-(3 : ℝ)) * (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹)))) else 0))
  : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (Real.exp ((-(3 : ℝ)) * (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹)))) else 0) := by
  sorry

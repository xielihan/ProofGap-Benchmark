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

-- exercise: exercise_665

theorem proof_gap_exercise_665_1
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (n : ℤ)
  (h1 : (x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 0))
  (h2 : n ∈ (Set.univ : Set ℤ))
  (h3 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≥ 0)) → ((y x_1) = (Real.rpow x_1 (((2 : ℝ))⁻¹))))))
  (h4 : n ≥ 0)
  (h5 : |(((y x) - 10))| < ((10 : ℝ) ^ (-n)))
  : |(((Real.rpow x (((2 : ℝ))⁻¹)) - 10))| < ((10 : ℝ) ^ (-n)) := by
  sorry

theorem proof_gap_exercise_665_2
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (n : ℤ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℤ))
  (h3 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≥ 0)) → ((y x_1) = (Real.rpow x_1 (((2 : ℝ))⁻¹))))))
  (h4 : n ≥ 0)
  (h5 : |(((Real.rpow x (((2 : ℝ))⁻¹)) - 10))| < ((10 : ℝ) ^ (-n)))
  : (10 * (1 - ((10 : ℝ) ^ (-(n + 1))))) < (Real.rpow x (((2 : ℝ))⁻¹)) := by
  sorry

theorem proof_gap_exercise_665_3
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (n : ℤ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℤ))
  (h3 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≥ 0)) → ((y x_1) = (Real.rpow x_1 (((2 : ℝ))⁻¹))))))
  (h4 : n ≥ 0)
  (h5 : |(((Real.rpow x (((2 : ℝ))⁻¹)) - 10))| < ((10 : ℝ) ^ (-n)))
  (h6 : (10 * (1 - ((10 : ℝ) ^ (-(n + 1))))) < (Real.rpow x (((2 : ℝ))⁻¹)))
  : (Real.rpow x (((2 : ℝ))⁻¹)) < (10 * (1 + ((10 : ℝ) ^ (-(n + 1))))) := by
  sorry

theorem proof_gap_exercise_665_4
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (n : ℤ)
  (h1 : (x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 0))
  (h2 : n ∈ (Set.univ : Set ℤ))
  (h3 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≥ 0)) → ((y x_1) = (Real.rpow x_1 (((2 : ℝ))⁻¹))))))
  (h4 : n ≥ 0)
  (h5 : |(((Real.rpow x (((2 : ℝ))⁻¹)) - 10))| < ((10 : ℝ) ^ (-n)))
  (h6 : (10 * (1 - ((10 : ℝ) ^ (-(n + 1))))) < (Real.rpow x (((2 : ℝ))⁻¹)))
  (h7 : (Real.rpow x (((2 : ℝ))⁻¹)) < (10 * (1 + ((10 : ℝ) ^ (-(n + 1))))))
  : (100 * ((1 - ((10 : ℝ) ^ (-(n + 1)))) ^ (2 : ℕ))) < x := by
  sorry

theorem proof_gap_exercise_665_5
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (n : ℤ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℤ))
  (h3 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≥ 0)) → ((y x_1) = (Real.rpow x_1 (((2 : ℝ))⁻¹))))))
  (h4 : n ≥ 0)
  (h5 : |(((Real.rpow x (((2 : ℝ))⁻¹)) - 10))| < ((10 : ℝ) ^ (-n)))
  (h6 : (10 * (1 - ((10 : ℝ) ^ (-(n + 1))))) < (Real.rpow x (((2 : ℝ))⁻¹)))
  (h7 : (Real.rpow x (((2 : ℝ))⁻¹)) < (10 * (1 + ((10 : ℝ) ^ (-(n + 1))))))
  (h8 : (100 * ((1 - ((10 : ℝ) ^ (-(n + 1)))) ^ (2 : ℕ))) < x)
  : x < (100 * ((1 + ((10 : ℝ) ^ (-(n + 1)))) ^ (2 : ℕ))) := by
  sorry

theorem proof_gap_exercise_665_6
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (n : ℤ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℤ))
  (h3 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≥ 0)) → ((y x_1) = (Real.rpow x_1 (((2 : ℝ))⁻¹))))))
  (h4 : n ≥ 0)
  (h5 : |(((Real.rpow x (((2 : ℝ))⁻¹)) - 10))| < ((10 : ℝ) ^ (-n)))
  (h6 : (10 * (1 - ((10 : ℝ) ^ (-(n + 1))))) < (Real.rpow x (((2 : ℝ))⁻¹)))
  (h7 : (Real.rpow x (((2 : ℝ))⁻¹)) < (10 * (1 + ((10 : ℝ) ^ (-(n + 1))))))
  (h8 : (100 * ((1 - ((10 : ℝ) ^ (-(n + 1)))) ^ (2 : ℕ))) < x)
  (h9 : x < (100 * ((1 + ((10 : ℝ) ^ (-(n + 1)))) ^ (2 : ℕ))))
  : (n = 0) → (81 < x) := by
  sorry

theorem proof_gap_exercise_665_7
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (n : ℤ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℤ))
  (h3 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≥ 0)) → ((y x_1) = (Real.rpow x_1 (((2 : ℝ))⁻¹))))))
  (h4 : n ≥ 0)
  (h5 : |(((Real.rpow x (((2 : ℝ))⁻¹)) - 10))| < ((10 : ℝ) ^ (-n)))
  (h6 : (10 * (1 - ((10 : ℝ) ^ (-(n + 1))))) < (Real.rpow x (((2 : ℝ))⁻¹)))
  (h7 : (Real.rpow x (((2 : ℝ))⁻¹)) < (10 * (1 + ((10 : ℝ) ^ (-(n + 1))))))
  (h8 : (100 * ((1 - ((10 : ℝ) ^ (-(n + 1)))) ^ (2 : ℕ))) < x)
  (h9 : x < (100 * ((1 + ((10 : ℝ) ^ (-(n + 1)))) ^ (2 : ℕ))))
  (h10 : (n = 0) → (81 < x))
  : (n = 0) → (x < 121) := by
  sorry

theorem proof_gap_exercise_665_8
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (n : ℤ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℤ))
  (h3 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≥ 0)) → ((y x_1) = (Real.rpow x_1 (((2 : ℝ))⁻¹))))))
  (h4 : n ≥ 0)
  (h5 : |(((Real.rpow x (((2 : ℝ))⁻¹)) - 10))| < ((10 : ℝ) ^ (-n)))
  (h6 : (10 * (1 - ((10 : ℝ) ^ (-(n + 1))))) < (Real.rpow x (((2 : ℝ))⁻¹)))
  (h7 : (Real.rpow x (((2 : ℝ))⁻¹)) < (10 * (1 + ((10 : ℝ) ^ (-(n + 1))))))
  (h8 : (100 * ((1 - ((10 : ℝ) ^ (-(n + 1)))) ^ (2 : ℕ))) < x)
  (h9 : x < (100 * ((1 + ((10 : ℝ) ^ (-(n + 1)))) ^ (2 : ℕ))))
  (h10 : (n = 0) → (81 < x))
  (h11 : (n = 0) → (x < 121))
  : (n = 1) → ((((9801 : ℝ) /. (100 : ℝ))) < x) := by
  sorry

theorem proof_gap_exercise_665_9
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (n : ℤ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℤ))
  (h3 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≥ 0)) → ((y x_1) = (Real.rpow x_1 (((2 : ℝ))⁻¹))))))
  (h4 : n ≥ 0)
  (h5 : |(((Real.rpow x (((2 : ℝ))⁻¹)) - 10))| < ((10 : ℝ) ^ (-n)))
  (h6 : (10 * (1 - ((10 : ℝ) ^ (-(n + 1))))) < (Real.rpow x (((2 : ℝ))⁻¹)))
  (h7 : (Real.rpow x (((2 : ℝ))⁻¹)) < (10 * (1 + ((10 : ℝ) ^ (-(n + 1))))))
  (h8 : (100 * ((1 - ((10 : ℝ) ^ (-(n + 1)))) ^ (2 : ℕ))) < x)
  (h9 : x < (100 * ((1 + ((10 : ℝ) ^ (-(n + 1)))) ^ (2 : ℕ))))
  (h10 : (n = 0) → (81 < x))
  (h11 : (n = 0) → (x < 121))
  (h12 : (n = 1) → ((((9801 : ℝ) /. (100 : ℝ))) < x))
  : (n = 1) → (x < (((10201 : ℝ) /. (100 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_665_10
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (n : ℤ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℤ))
  (h3 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≥ 0)) → ((y x_1) = (Real.rpow x_1 (((2 : ℝ))⁻¹))))))
  (h4 : n ≥ 0)
  (h5 : |(((Real.rpow x (((2 : ℝ))⁻¹)) - 10))| < ((10 : ℝ) ^ (-n)))
  (h6 : (10 * (1 - ((10 : ℝ) ^ (-(n + 1))))) < (Real.rpow x (((2 : ℝ))⁻¹)))
  (h7 : (Real.rpow x (((2 : ℝ))⁻¹)) < (10 * (1 + ((10 : ℝ) ^ (-(n + 1))))))
  (h8 : (100 * ((1 - ((10 : ℝ) ^ (-(n + 1)))) ^ (2 : ℕ))) < x)
  (h9 : x < (100 * ((1 + ((10 : ℝ) ^ (-(n + 1)))) ^ (2 : ℕ))))
  (h10 : (n = 0) → (81 < x))
  (h11 : (n = 0) → (x < 121))
  (h12 : (n = 1) → ((((9801 : ℝ) /. (100 : ℝ))) < x))
  (h13 : (n = 1) → (x < (((10201 : ℝ) /. (100 : ℝ)))))
  : (n = 2) → ((((988001 : ℝ) /. (10000 : ℝ))) < x) := by
  sorry

theorem proof_gap_exercise_665_11
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (n : ℤ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℤ))
  (h3 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≥ 0)) → ((y x_1) = (Real.rpow x_1 (((2 : ℝ))⁻¹))))))
  (h4 : n ≥ 0)
  (h5 : |(((Real.rpow x (((2 : ℝ))⁻¹)) - 10))| < ((10 : ℝ) ^ (-n)))
  (h6 : (10 * (1 - ((10 : ℝ) ^ (-(n + 1))))) < (Real.rpow x (((2 : ℝ))⁻¹)))
  (h7 : (Real.rpow x (((2 : ℝ))⁻¹)) < (10 * (1 + ((10 : ℝ) ^ (-(n + 1))))))
  (h8 : (100 * ((1 - ((10 : ℝ) ^ (-(n + 1)))) ^ (2 : ℕ))) < x)
  (h9 : x < (100 * ((1 + ((10 : ℝ) ^ (-(n + 1)))) ^ (2 : ℕ))))
  (h10 : (n = 0) → (81 < x))
  (h11 : (n = 0) → (x < 121))
  (h12 : (n = 1) → ((((9801 : ℝ) /. (100 : ℝ))) < x))
  (h13 : (n = 1) → (x < (((10201 : ℝ) /. (100 : ℝ)))))
  (h14 : (n = 2) → ((((988001 : ℝ) /. (10000 : ℝ))) < x))
  : (n = 2) → (x < (((1002001 : ℝ) /. (10000 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_665_12
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (n : ℤ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℤ))
  (h3 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≥ 0)) → ((y x_1) = (Real.rpow x_1 (((2 : ℝ))⁻¹))))))
  (h4 : n ≥ 0)
  (h5 : |(((Real.rpow x (((2 : ℝ))⁻¹)) - 10))| < ((10 : ℝ) ^ (-n)))
  (h6 : (10 * (1 - ((10 : ℝ) ^ (-(n + 1))))) < (Real.rpow x (((2 : ℝ))⁻¹)))
  (h7 : (Real.rpow x (((2 : ℝ))⁻¹)) < (10 * (1 + ((10 : ℝ) ^ (-(n + 1))))))
  (h8 : (100 * ((1 - ((10 : ℝ) ^ (-(n + 1)))) ^ (2 : ℕ))) < x)
  (h9 : x < (100 * ((1 + ((10 : ℝ) ^ (-(n + 1)))) ^ (2 : ℕ))))
  (h10 : (n = 0) → (81 < x))
  (h11 : (n = 0) → (x < 121))
  (h12 : (n = 1) → ((((9801 : ℝ) /. (100 : ℝ))) < x))
  (h13 : (n = 1) → (x < (((10201 : ℝ) /. (100 : ℝ)))))
  (h14 : (n = 2) → ((((988001 : ℝ) /. (10000 : ℝ))) < x))
  (h15 : (n = 2) → (x < (((1002001 : ℝ) /. (10000 : ℝ)))))
  : (n = 3) → ((((99980001 : ℝ) /. (1000000 : ℝ))) < x) := by
  sorry

theorem proof_gap_exercise_665_13
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (n : ℤ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℤ))
  (h3 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≥ 0)) → ((y x_1) = (Real.rpow x_1 (((2 : ℝ))⁻¹))))))
  (h4 : n ≥ 0)
  (h5 : |(((Real.rpow x (((2 : ℝ))⁻¹)) - 10))| < ((10 : ℝ) ^ (-n)))
  (h6 : (10 * (1 - ((10 : ℝ) ^ (-(n + 1))))) < (Real.rpow x (((2 : ℝ))⁻¹)))
  (h7 : (Real.rpow x (((2 : ℝ))⁻¹)) < (10 * (1 + ((10 : ℝ) ^ (-(n + 1))))))
  (h8 : (100 * ((1 - ((10 : ℝ) ^ (-(n + 1)))) ^ (2 : ℕ))) < x)
  (h9 : x < (100 * ((1 + ((10 : ℝ) ^ (-(n + 1)))) ^ (2 : ℕ))))
  (h10 : (n = 0) → (81 < x))
  (h11 : (n = 0) → (x < 121))
  (h12 : (n = 1) → ((((9801 : ℝ) /. (100 : ℝ))) < x))
  (h13 : (n = 1) → (x < (((10201 : ℝ) /. (100 : ℝ)))))
  (h14 : (n = 2) → ((((988001 : ℝ) /. (10000 : ℝ))) < x))
  (h15 : (n = 2) → (x < (((1002001 : ℝ) /. (10000 : ℝ)))))
  (h16 : (n = 3) → ((((99980001 : ℝ) /. (1000000 : ℝ))) < x))
  : (n = 3) → (x < (((100020001 : ℝ) /. (1000000 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_665_14
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (n : ℤ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℤ))
  (h3 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≥ 0)) → ((y x_1) = (Real.rpow x_1 (((2 : ℝ))⁻¹))))))
  (h4 : n ≥ 0)
  (h5 : |(((Real.rpow x (((2 : ℝ))⁻¹)) - 10))| < ((10 : ℝ) ^ (-n)))
  (h6 : (10 * (1 - ((10 : ℝ) ^ (-(n + 1))))) < (Real.rpow x (((2 : ℝ))⁻¹)))
  (h7 : (Real.rpow x (((2 : ℝ))⁻¹)) < (10 * (1 + ((10 : ℝ) ^ (-(n + 1))))))
  (h8 : (100 * ((1 - ((10 : ℝ) ^ (-(n + 1)))) ^ (2 : ℕ))) < x)
  (h9 : x < (100 * ((1 + ((10 : ℝ) ^ (-(n + 1)))) ^ (2 : ℕ))))
  (h10 : (n = 0) → (81 < x))
  (h11 : (n = 0) → (x < 121))
  (h12 : (n = 1) → ((((9801 : ℝ) /. (100 : ℝ))) < x))
  (h13 : (n = 1) → (x < (((10201 : ℝ) /. (100 : ℝ)))))
  (h14 : (n = 2) → ((((988001 : ℝ) /. (10000 : ℝ))) < x))
  (h15 : (n = 2) → (x < (((1002001 : ℝ) /. (10000 : ℝ)))))
  (h16 : (n = 3) → ((((99980001 : ℝ) /. (1000000 : ℝ))) < x))
  (h17 : (n = 3) → (x < (((100020001 : ℝ) /. (1000000 : ℝ)))))
  : (((((((100 * ((1 - ((10 : ℝ) ^ (-(n + 1)))) ^ (2 : ℕ))) < x) ∧ (x < (100 * ((1 + ((10 : ℝ) ^ (-(n + 1)))) ^ (2 : ℕ))))) ∧ ((n = 0) → ((81 < x) ∧ (x < 121)))) ∧ ((n = 1) → (((((9801 : ℝ) /. (100 : ℝ))) < x) ∧ (x < (((10201 : ℝ) /. (100 : ℝ))))))) ∧ ((n = 2) → (((((988001 : ℝ) /. (10000 : ℝ))) < x) ∧ (x < (((1002001 : ℝ) /. (10000 : ℝ))))))) ∧ ((n = 3) → (((((99980001 : ℝ) /. (1000000 : ℝ))) < x) ∧ (x < (((100020001 : ℝ) /. (1000000 : ℝ))))))) ↔ (|(((y x) - 10))| < ((10 : ℝ) ^ (-n))) := by
  sorry

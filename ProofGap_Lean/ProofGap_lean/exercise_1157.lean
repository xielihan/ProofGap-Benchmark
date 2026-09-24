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

-- exercise: exercise_1157

theorem proof_gap_exercise_1157_1
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (m : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : m ∈ (Set.univ : Set ℕ))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((y x) = (a /. (x ^ m))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => y t) x) = (((-a) * m) * (x ^ ((-(m : ℝ)) - 1)))))) := by
  sorry

theorem proof_gap_exercise_1157_2
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (m : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : m ∈ (Set.univ : Set ℕ))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((y x) = (a /. (x ^ m))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => y t) x) = (((-a) * m) * (x ^ ((-(m : ℝ)) - 1)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 2 (fun t => y t) x) = (((a * m) * (m + 1)) * (x ^ ((-(m : ℝ)) - 2)))))) := by
  sorry

theorem proof_gap_exercise_1157_3
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (m : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : m ∈ (Set.univ : Set ℕ))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((y x) = (a /. (x ^ m))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => y t) x) = (((-a) * m) * (x ^ ((-(m : ℝ)) - 1)))))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 2 (fun t => y t) x) = (((a * m) * (m + 1)) * (x ^ ((-(m : ℝ)) - 2)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 3 (fun t => y t) x) = (((((-a) * m) * (m + 1)) * (m + 2)) * (x ^ ((-(m : ℝ)) - 3)))))) := by
  sorry

theorem proof_gap_exercise_1157_4
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (m : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : m ∈ (Set.univ : Set ℕ))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((y x) = (a /. (x ^ m))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => y t) x) = (((-a) * m) * (x ^ ((-(m : ℝ)) - 1)))))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 2 (fun t => y t) x) = (((a * m) * (m + 1)) * (x ^ ((-(m : ℝ)) - 2)))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 3 (fun t => y t) x) = (((((-a) * m) * (m + 1)) * (m + 2)) * (x ^ ((-(m : ℝ)) - 3)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((((((-a) * m) * (m + 1)) * (m + 2)) * (x ^ ((-(m : ℝ)) - 3))) = (-((((a * m) * (m + 1)) * (m + 2)) /. (x ^ (m + 3))))))) := by
  sorry

theorem proof_gap_exercise_1157_5
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (m : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : m ∈ (Set.univ : Set ℕ))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((y x) = (a /. (x ^ m))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => y t) x) = (((-a) * m) * (x ^ ((-(m : ℝ)) - 1)))))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 2 (fun t => y t) x) = (((a * m) * (m + 1)) * (x ^ ((-(m : ℝ)) - 2)))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 3 (fun t => y t) x) = (((((-a) * m) * (m + 1)) * (m + 2)) * (x ^ ((-(m : ℝ)) - 3)))))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((((((-a) * m) * (m + 1)) * (m + 2)) * (x ^ ((-(m : ℝ)) - 3))) = (-((((a * m) * (m + 1)) * (m + 2)) /. (x ^ (m + 3))))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 3 (fun t => y t) x) = (-((((a * m) * (m + 1)) * (m + 2)) /. (x ^ (m + 3))))))) := by
  sorry

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

-- exercise: exercise_395

theorem proof_gap_exercise_395_1
  (f : (ℝ -> ℤ))
  (m_1 : ℤ)
  (M_1 : ℤ)
  (m_2 : ℤ)
  (M_2 : ℤ)
  (h1 : m_1 ∈ (Set.univ : Set ℤ))
  (h2 : M_1 ∈ (Set.univ : Set ℤ))
  (h3 : m_2 ∈ (Set.univ : Set ℤ))
  (h4 : M_2 ∈ (Set.univ : Set ℤ))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ⌊x⌋))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 2))) → ((f x) ∈ ({x | x = 0 ∨ x = 1})))) := by
  sorry

theorem proof_gap_exercise_395_2
  (f : (ℝ -> ℤ))
  (m_1 : ℤ)
  (M_1 : ℤ)
  (m_2 : ℤ)
  (M_2 : ℤ)
  (h1 : m_1 ∈ (Set.univ : Set ℤ))
  (h2 : M_1 ∈ (Set.univ : Set ℤ))
  (h3 : m_2 ∈ (Set.univ : Set ℤ))
  (h4 : M_2 ∈ (Set.univ : Set ℤ))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ⌊x⌋))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 2))) → ((f x) ∈ ({x | x = 0 ∨ x = 1})))))
  (h7 : m_1 = (sInf (f '' (0, 2))))
  : m_1 = 0 := by
  sorry

theorem proof_gap_exercise_395_3
  (f : (ℝ -> ℤ))
  (m_1 : ℤ)
  (M_1 : ℤ)
  (m_2 : ℤ)
  (M_2 : ℤ)
  (h1 : m_1 ∈ (Set.univ : Set ℤ))
  (h2 : M_1 ∈ (Set.univ : Set ℤ))
  (h3 : m_2 ∈ (Set.univ : Set ℤ))
  (h4 : M_2 ∈ (Set.univ : Set ℤ))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ⌊x⌋))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 2))) → ((f x) ∈ ({x | x = 0 ∨ x = 1})))))
  (h7 : m_1 = 0)
  (h8 : M_1 = (sSup (f '' (0, 2))))
  : M_1 = 1 := by
  sorry

theorem proof_gap_exercise_395_4
  (f : (ℝ -> ℤ))
  (m_1 : ℤ)
  (M_1 : ℤ)
  (m_2 : ℤ)
  (M_2 : ℤ)
  (h1 : m_1 ∈ (Set.univ : Set ℤ))
  (h2 : M_1 ∈ (Set.univ : Set ℤ))
  (h3 : m_2 ∈ (Set.univ : Set ℤ))
  (h4 : M_2 ∈ (Set.univ : Set ℤ))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ⌊x⌋))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 2))) → ((f x) ∈ ({x | x = 0 ∨ x = 1})))))
  (h7 : m_1 = 0)
  (h8 : M_1 = 1)
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 2))) → ((f x) ∈ ({x | x = 0 ∨ x = 1 ∨ x = 2})))) := by
  sorry

theorem proof_gap_exercise_395_5
  (f : (ℝ -> ℤ))
  (m_1 : ℤ)
  (M_1 : ℤ)
  (m_2 : ℤ)
  (M_2 : ℤ)
  (h1 : m_1 ∈ (Set.univ : Set ℤ))
  (h2 : M_1 ∈ (Set.univ : Set ℤ))
  (h3 : m_2 ∈ (Set.univ : Set ℤ))
  (h4 : M_2 ∈ (Set.univ : Set ℤ))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ⌊x⌋))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 2))) → ((f x) ∈ ({x | x = 0 ∨ x = 1})))))
  (h7 : m_1 = 0)
  (h8 : M_1 = 1)
  (h9 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 2))) → ((f x) ∈ ({x | x = 0 ∨ x = 1 ∨ x = 2})))))
  (h10 : m_2 = (sInf (f '' (Set.Icc 0 2))))
  : m_2 = 0 := by
  sorry

theorem proof_gap_exercise_395_6
  (f : (ℝ -> ℤ))
  (m_1 : ℤ)
  (M_1 : ℤ)
  (m_2 : ℤ)
  (M_2 : ℤ)
  (h1 : m_1 ∈ (Set.univ : Set ℤ))
  (h2 : M_1 ∈ (Set.univ : Set ℤ))
  (h3 : m_2 ∈ (Set.univ : Set ℤ))
  (h4 : M_2 ∈ (Set.univ : Set ℤ))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ⌊x⌋))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 2))) → ((f x) ∈ ({x | x = 0 ∨ x = 1})))))
  (h7 : m_1 = 0)
  (h8 : M_1 = 1)
  (h9 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 2))) → ((f x) ∈ ({x | x = 0 ∨ x = 1 ∨ x = 2})))))
  (h10 : m_2 = 0)
  (h11 : M_2 = (sSup (f '' (Set.Icc 0 2))))
  : M_2 = 2 := by
  sorry

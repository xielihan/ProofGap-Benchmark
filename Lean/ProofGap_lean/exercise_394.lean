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

-- exercise: exercise_394

theorem proof_gap_exercise_394_1
  (f : (ℝ -> ℝ))
  (m_0 : ℝ)
  (M_0 : ℝ)
  (h1 : m_0 ∈ (Set.univ : Set ℝ))
  (h2 : M_0 ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo (-(1 : ℝ)) 2))) → ((f x) = (Real.rpow (2 : ℝ) x)))))
  : MonotoneOn f (Set.Ioo (-(1 : ℝ)) 2) := by
  sorry

theorem proof_gap_exercise_394_2
  (f : (ℝ -> ℝ))
  (m_0 : ℝ)
  (M_0 : ℝ)
  (h1 : m_0 ∈ (Set.univ : Set ℝ))
  (h2 : M_0 ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo (-(1 : ℝ)) 2))) → ((f x) = (Real.rpow (2 : ℝ) x)))))
  (h4 : MonotoneOn f (Set.Icc (-(1 : ℝ)) 2))
  (h5 : m_0 = (sInf (f '' (Set.Icc (-(1 : ℝ)) 2))))
  : m_0 = (f (-(1 : ℝ))) := by
  sorry

theorem proof_gap_exercise_394_3
  (f : (ℝ -> ℝ))
  (m_0 : ℝ)
  (M_0 : ℝ)
  (h1 : m_0 ∈ (Set.univ : Set ℝ))
  (h2 : M_0 ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(1 : ℝ)) 2))) → ((f x) = (Real.rpow (2 : ℝ) x)))))
  (h4 : MonotoneOn f (Set.Icc (-(1 : ℝ)) 2))
  (h5 : m_0 = (f (-(1 : ℝ))))
  (h6 : m_0 = (sInf (f '' (Set.Icc (-(1 : ℝ)) 2))))
  : (f (-(1 : ℝ))) = (1 /. 2) := by
  sorry

theorem proof_gap_exercise_394_4
  (f : (ℝ -> ℝ))
  (m_0 : ℝ)
  (M_0 : ℝ)
  (h1 : m_0 ∈ (Set.univ : Set ℝ))
  (h2 : M_0 ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo (-(1 : ℝ)) 2))) → ((f x) = (Real.rpow (2 : ℝ) x)))))
  (h4 : MonotoneOn f (Set.Ioo (-(1 : ℝ)) 2))
  (h5 : m_0 = (f (-(1 : ℝ))))
  (h6 : (f (-(1 : ℝ))) = (1 /. 2))
  : m_0 = (1 /. 2) := by
  sorry

theorem proof_gap_exercise_394_5
  (f : (ℝ -> ℝ))
  (m_0 : ℝ)
  (M_0 : ℝ)
  (h1 : m_0 ∈ (Set.univ : Set ℝ))
  (h2 : M_0 ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo (-(1 : ℝ)) 2))) → ((f x) = (Real.rpow (2 : ℝ) x)))))
  (h4 : MonotoneOn f (Set.Icc (-(1 : ℝ)) 2))
  (h5 : m_0 = (f (-(1 : ℝ))))
  (h6 : (f (-(1 : ℝ))) = (1 /. 2))
  (h7 : m_0 = (1 /. 2))
  (h8 : M_0 = (sSup (f '' (Set.Icc (-(1 : ℝ)) 2))))
  : M_0 = (f (2 : ℝ)) := by
  sorry

theorem proof_gap_exercise_394_6
  (f : (ℝ -> ℝ))
  (m_0 : ℝ)
  (M_0 : ℝ)
  (h1 : m_0 ∈ (Set.univ : Set ℝ))
  (h2 : M_0 ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(1 : ℝ)) 2))) → ((f x) = (Real.rpow (2 : ℝ) x)))))
  (h4 : MonotoneOn f (Set.Icc (-(1 : ℝ)) 2))
  (h5 : m_0 = (f (-(1 : ℝ))))
  (h6 : (f (-(1 : ℝ))) = (1 /. 2))
  (h7 : m_0 = (1 /. 2))
  (h8 : M_0 = (f (2 : ℝ)))
  (h9 : M_0 = (sSup (f '' (Set.Icc (-(1 : ℝ)) 2))))
  : (f (2 : ℝ)) = 4 := by
  sorry

theorem proof_gap_exercise_394_7
  (f : (ℝ -> ℝ))
  (m_0 : ℝ)
  (M_0 : ℝ)
  (h1 : m_0 ∈ (Set.univ : Set ℝ))
  (h2 : M_0 ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo (-(1 : ℝ)) 2))) → ((f x) = (Real.rpow (2 : ℝ) x)))))
  (h4 : MonotoneOn f (Set.Ioo (-(1 : ℝ)) 2))
  (h5 : m_0 = (f (-(1 : ℝ))))
  (h6 : (f (-(1 : ℝ))) = (1 /. 2))
  (h7 : m_0 = (1 /. 2))
  (h8 : M_0 = (f (2 : ℝ)))
  (h9 : (f (2 : ℝ)) = 4)
  : M_0 = 4 := by
  sorry

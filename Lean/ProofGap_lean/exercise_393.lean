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

-- exercise: exercise_393

theorem proof_gap_exercise_393_1
  (f : (ℝ -> ℝ))
  (m_0 : ℝ)
  (M_0 : ℝ)
  (h1 : m_0 ∈ (Set.univ : Set ℝ))
  (h2 : M_0 ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 (2 * Real.pi)))) → ((f x) = ((Real.sin x) + (Real.cos x))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 (2 * Real.pi)))) → ((f x) = ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) * (Real.sin (x + (Real.pi /. 4))))))) := by
  sorry

theorem proof_gap_exercise_393_2
  (f : (ℝ -> ℝ))
  (m_0 : ℝ)
  (M_0 : ℝ)
  (h1 : m_0 ∈ (Set.univ : Set ℝ))
  (h2 : M_0 ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 (2 * Real.pi)))) → ((f x) = ((Real.sin x) + (Real.cos x))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 (2 * Real.pi)))) → ((f x) = ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) * (Real.sin (x + (Real.pi /. 4))))))))
  : (sInf (f '' (Set.Icc 0 (2 * Real.pi)))) = (-(Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))) := by
  sorry

theorem proof_gap_exercise_393_3
  (f : (ℝ -> ℝ))
  (m_0 : ℝ)
  (M_0 : ℝ)
  (h1 : m_0 ∈ (Set.univ : Set ℝ))
  (h2 : M_0 ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 (2 * Real.pi)))) → ((f x) = ((Real.sin x) + (Real.cos x))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 (2 * Real.pi)))) → ((f x) = ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) * (Real.sin (x + (Real.pi /. 4))))))))
  (h5 : (sInf (f '' (Set.Icc 0 (2 * Real.pi)))) = (-(Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))))
  : (sSup (f '' (Set.Icc 0 (2 * Real.pi)))) = (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) := by
  sorry

theorem proof_gap_exercise_393_4
  (f : (ℝ -> ℝ))
  (m_0 : ℝ)
  (M_0 : ℝ)
  (h1 : m_0 ∈ (Set.univ : Set ℝ))
  (h2 : M_0 ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 (2 * Real.pi)))) → ((f x) = ((Real.sin x) + (Real.cos x))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 (2 * Real.pi)))) → ((f x) = ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) * (Real.sin (x + (Real.pi /. 4))))))))
  (h5 : (sInf (f '' (Set.Icc 0 (2 * Real.pi)))) = (-(Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))))
  (h6 : (sSup (f '' (Set.Icc 0 (2 * Real.pi)))) = (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)))
  : ((m_0, M_0) = ((-(Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))), (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)))) → (((sInf (f '' (Set.Icc 0 (2 * Real.pi)))) = m_0) ∧ ((sSup (f '' (Set.Icc 0 (2 * Real.pi)))) = M_0)) := by
  sorry

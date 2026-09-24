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

-- exercise: exercise_386

theorem proof_gap_exercise_386_1
  (f : (ℝ -> ℝ))
  (m_0 : ℝ)
  (M_0 : ℝ)
  (h1 : m_0 ∈ (Set.univ : Set ℝ))
  (h2 : M_0 ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ ((x : EReal) < ⊤)) → ((f x) = (x /. (1 + x))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ ((x : EReal) < ⊤)) → (0 ≤ (f x)))) := by
  sorry

theorem proof_gap_exercise_386_2
  (f : (ℝ -> ℝ))
  (m_0 : ℝ)
  (M_0 : ℝ)
  (h1 : m_0 ∈ (Set.univ : Set ℝ))
  (h2 : M_0 ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ ((x : EReal) < ⊤)) → ((f x) = (x /. (1 + x))))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ ((x : EReal) < ⊤)) → (0 ≤ (f x)))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ ((x : EReal) < ⊤)) → ((f x) < 1))) := by
  sorry

theorem proof_gap_exercise_386_3
  (f : (ℝ -> ℝ))
  (m_0 : ℝ)
  (M_0 : ℝ)
  (h1 : m_0 ∈ (Set.univ : Set ℝ))
  (h2 : M_0 ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ ((x : EReal) < ⊤)) → ((f x) = (x /. (1 + x))))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ ((x : EReal) < ⊤)) → (0 ≤ (f x)))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ ((x : EReal) < ⊤)) → ((f x) < 1))))
  : MonotoneOn f ({x | (x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x) ∧ ((x : EReal) < ⊤)}) := by
  sorry

theorem proof_gap_exercise_386_4
  (f : (ℝ -> ℝ))
  (m_0 : ℝ)
  (M_0 : ℝ)
  (h1 : m_0 ∈ (Set.univ : Set ℝ))
  (h2 : M_0 ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ ((x : EReal) < ⊤)) → ((f x) = (x /. (1 + x))))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ ((x : EReal) < ⊤)) → (0 ≤ (f x)))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ ((x : EReal) < ⊤)) → ((f x) < 1))))
  (h6 : MonotoneOn f ({x | (x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x) ∧ ((x : EReal) < ⊤)}))
  : (sInf (f '' ({x | (x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x) ∧ ((x : EReal) < ⊤)}))) = 0 := by
  sorry

theorem proof_gap_exercise_386_5
  (f : (ℝ -> ℝ))
  (m_0 : ℝ)
  (M_0 : ℝ)
  (h1 : m_0 ∈ (Set.univ : Set ℝ))
  (h2 : M_0 ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ ((x : EReal) < ⊤)) → ((f x) = (x /. (1 + x))))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ ((x : EReal) < ⊤)) → (0 ≤ (f x)))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ ((x : EReal) < ⊤)) → ((f x) < 1))))
  (h6 : MonotoneOn f ({x | (x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x) ∧ ((x : EReal) < ⊤)}))
  (h7 : (sInf (f '' ({x | (x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x) ∧ ((x : EReal) < ⊤)}))) = 0)
  : (sSup (f '' ({x | (x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x) ∧ ((x : EReal) < ⊤)}))) = 1 := by
  sorry

theorem proof_gap_exercise_386_6
  (f : (ℝ -> ℝ))
  (m_0 : ℝ)
  (M_0 : ℝ)
  (h1 : m_0 ∈ (Set.univ : Set ℝ))
  (h2 : M_0 ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ ((x : EReal) < ⊤)) → ((f x) = (x /. (1 + x))))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ ((x : EReal) < ⊤)) → (0 ≤ (f x)))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ ((x : EReal) < ⊤)) → ((f x) < 1))))
  (h6 : MonotoneOn f ({x | (x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x) ∧ ((x : EReal) < ⊤)}))
  (h7 : (sInf (f '' ({x | (x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x) ∧ ((x : EReal) < ⊤)}))) = 0)
  (h8 : (sSup (f '' ({x | (x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x) ∧ ((x : EReal) < ⊤)}))) = 1)
  (h9 : m_0 = (sInf (f '' ({x | (x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x) ∧ ((x : EReal) < ⊤)}))))
  : m_0 = 0 := by
  sorry

theorem proof_gap_exercise_386_7
  (f : (ℝ -> ℝ))
  (m_0 : ℝ)
  (M_0 : ℝ)
  (h1 : m_0 ∈ (Set.univ : Set ℝ))
  (h2 : M_0 ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ ((x : EReal) < ⊤)) → ((f x) = (x /. (1 + x))))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ ((x : EReal) < ⊤)) → (0 ≤ (f x)))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ ((x : EReal) < ⊤)) → ((f x) < 1))))
  (h6 : MonotoneOn f ({x | (x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x) ∧ ((x : EReal) < ⊤)}))
  (h7 : (sInf (f '' ({x | (x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x) ∧ ((x : EReal) < ⊤)}))) = 0)
  (h8 : (sSup (f '' ({x | (x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x) ∧ ((x : EReal) < ⊤)}))) = 1)
  (h9 : m_0 = 0)
  (h10 : M_0 = (sSup (f '' ({x | (x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x) ∧ ((x : EReal) < ⊤)}))))
  : M_0 = 1 := by
  sorry

theorem proof_gap_exercise_386_8
  (f : (ℝ -> ℝ))
  (m_0 : ℝ)
  (M_0 : ℝ)
  (h1 : m_0 ∈ (Set.univ : Set ℝ))
  (h2 : M_0 ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ ((x : EReal) < ⊤)) → ((f x) = (x /. (1 + x))))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ ((x : EReal) < ⊤)) → (0 ≤ (f x)))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ ((x : EReal) < ⊤)) → ((f x) < 1))))
  (h6 : MonotoneOn f ({x | (x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x) ∧ ((x : EReal) < ⊤)}))
  (h7 : (sInf (f '' ({x | (x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x) ∧ ((x : EReal) < ⊤)}))) = 0)
  (h8 : (sSup (f '' ({x | (x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x) ∧ ((x : EReal) < ⊤)}))) = 1)
  (h9 : m_0 = 0)
  (h10 : M_0 = 1)
  : (((m_0 = 0) ∧ (M_0 = 1)) ∧ ((sInf (f '' ({x | (x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x) ∧ ((x : EReal) < ⊤)}))) = m_0)) ∧ ((sSup (f '' ({x | (x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x) ∧ ((x : EReal) < ⊤)}))) = M_0) := by
  sorry

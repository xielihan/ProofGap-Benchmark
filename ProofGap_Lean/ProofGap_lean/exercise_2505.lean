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

-- exercise: exercise_2505

theorem proof_gap_exercise_2505_1
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (s : ℝ)
  (v_uCE_uBE : ℝ)
  (v_uCE_uB7 : ℝ)
  (S : ℝ)
  (h1 : C ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h2 : (s ∈ (Set.univ : Set ℝ)) ∧ (s > 0))
  (h3 : v_uCE_uBE ∈ (Set.univ : Set ℝ))
  (h4 : v_uCE_uB7 ∈ (Set.univ : Set ℝ))
  (h5 : S ∈ (Set.univ : Set ℝ))
  (h6 : ContinuousOn x (Set.Icc 0 s))
  (h7 : ContinuousOn y (Set.Icc 0 s))
  (h8 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Icc 0 s))) → (((x t), (y t)) ∈ C))))
  (h9 : (v_uCE_uBE * s) = (∫ t in (0 : ℝ)..s, ((x t) * (1 : ℝ))))
  (h10 : (v_uCE_uB7 * s) = (∫ t in (0 : ℝ)..s, ((y t) * (1 : ℝ))))
  (h11 : S = ((2 * Real.pi) * (∫ t in (0 : ℝ)..s, ((y t) * (1 : ℝ)))))
  : (v_uCE_uB7 * s) = (∫ t in (0 : ℝ)..s, ((y t) * (1 : ℝ))) := by
  sorry

theorem proof_gap_exercise_2505_2
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (s : ℝ)
  (v_uCE_uBE : ℝ)
  (v_uCE_uB7 : ℝ)
  (S : ℝ)
  (h1 : C ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h2 : (s ∈ (Set.univ : Set ℝ)) ∧ (s > 0))
  (h3 : v_uCE_uBE ∈ (Set.univ : Set ℝ))
  (h4 : v_uCE_uB7 ∈ (Set.univ : Set ℝ))
  (h5 : S ∈ (Set.univ : Set ℝ))
  (h6 : ContinuousOn x (Set.Icc 0 s))
  (h7 : ContinuousOn y (Set.Icc 0 s))
  (h8 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Icc 0 s))) → (((x t), (y t)) ∈ C))))
  (h9 : (v_uCE_uBE * s) = (∫ t in (0 : ℝ)..s, ((x t) * (1 : ℝ))))
  (h10 : (v_uCE_uB7 * s) = (∫ t in (0 : ℝ)..s, ((y t) * (1 : ℝ))))
  (h11 : S = ((2 * Real.pi) * (∫ t in (0 : ℝ)..s, ((y t) * (1 : ℝ)))))
  (h12 : (v_uCE_uB7 * s) = (∫ t in (0 : ℝ)..s, ((y t) * (1 : ℝ))))
  : (((2 * Real.pi) * v_uCE_uB7) * s) = ((2 * Real.pi) * (∫ t in (0 : ℝ)..s, ((y t) * (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_2505_3
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (s : ℝ)
  (v_uCE_uBE : ℝ)
  (v_uCE_uB7 : ℝ)
  (S : ℝ)
  (h1 : C ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h2 : (s ∈ (Set.univ : Set ℝ)) ∧ (s > 0))
  (h3 : v_uCE_uBE ∈ (Set.univ : Set ℝ))
  (h4 : v_uCE_uB7 ∈ (Set.univ : Set ℝ))
  (h5 : S ∈ (Set.univ : Set ℝ))
  (h6 : ContinuousOn x (Set.Icc 0 s))
  (h7 : ContinuousOn y (Set.Icc 0 s))
  (h8 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Icc 0 s))) → (((x t), (y t)) ∈ C))))
  (h9 : (v_uCE_uBE * s) = (∫ t in (0 : ℝ)..s, ((x t) * (1 : ℝ))))
  (h10 : (v_uCE_uB7 * s) = (∫ t in (0 : ℝ)..s, ((y t) * (1 : ℝ))))
  (h11 : S = ((2 * Real.pi) * (∫ t in (0 : ℝ)..s, ((y t) * (1 : ℝ)))))
  (h12 : (v_uCE_uB7 * s) = (∫ t in (0 : ℝ)..s, ((y t) * (1 : ℝ))))
  (h13 : (((2 * Real.pi) * v_uCE_uB7) * s) = ((2 * Real.pi) * (∫ t in (0 : ℝ)..s, ((y t) * (1 : ℝ)))))
  : ((2 * Real.pi) * (∫ t in (0 : ℝ)..s, ((y t) * (1 : ℝ)))) = S := by
  sorry

theorem proof_gap_exercise_2505_4
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (s : ℝ)
  (v_uCE_uBE : ℝ)
  (v_uCE_uB7 : ℝ)
  (S : ℝ)
  (h1 : C ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h2 : (s ∈ (Set.univ : Set ℝ)) ∧ (s > 0))
  (h3 : v_uCE_uBE ∈ (Set.univ : Set ℝ))
  (h4 : v_uCE_uB7 ∈ (Set.univ : Set ℝ))
  (h5 : S ∈ (Set.univ : Set ℝ))
  (h6 : ContinuousOn x (Set.Icc 0 s))
  (h7 : ContinuousOn y (Set.Icc 0 s))
  (h8 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Icc 0 s))) → (((x t), (y t)) ∈ C))))
  (h9 : (v_uCE_uBE * s) = (∫ t in (0 : ℝ)..s, ((x t) * (1 : ℝ))))
  (h10 : (v_uCE_uB7 * s) = (∫ t in (0 : ℝ)..s, ((y t) * (1 : ℝ))))
  (h11 : S = ((2 * Real.pi) * (∫ t in (0 : ℝ)..s, ((y t) * (1 : ℝ)))))
  (h12 : (v_uCE_uB7 * s) = (∫ t in (0 : ℝ)..s, ((y t) * (1 : ℝ))))
  (h13 : (((2 * Real.pi) * v_uCE_uB7) * s) = ((2 * Real.pi) * (∫ t in (0 : ℝ)..s, ((y t) * (1 : ℝ)))))
  (h14 : ((2 * Real.pi) * (∫ t in (0 : ℝ)..s, ((y t) * (1 : ℝ)))) = S)
  : S = (((s * 2) * Real.pi) * v_uCE_uB7) := by
  sorry

theorem proof_gap_exercise_2505_5
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (s : ℝ)
  (v_uCE_uBE : ℝ)
  (v_uCE_uB7 : ℝ)
  (S : ℝ)
  (h1 : C ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h2 : (s ∈ (Set.univ : Set ℝ)) ∧ (s > 0))
  (h3 : v_uCE_uBE ∈ (Set.univ : Set ℝ))
  (h4 : v_uCE_uB7 ∈ (Set.univ : Set ℝ))
  (h5 : S ∈ (Set.univ : Set ℝ))
  (h6 : ContinuousOn x (Set.Icc 0 s))
  (h7 : ContinuousOn y (Set.Icc 0 s))
  (h8 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Icc 0 s))) → (((x t), (y t)) ∈ C))))
  (h9 : (v_uCE_uBE * s) = (∫ t in (0 : ℝ)..s, ((x t) * (1 : ℝ))))
  (h10 : (v_uCE_uB7 * s) = (∫ t in (0 : ℝ)..s, ((y t) * (1 : ℝ))))
  (h11 : S = ((2 * Real.pi) * (∫ t in (0 : ℝ)..s, ((y t) * (1 : ℝ)))))
  (h12 : (v_uCE_uB7 * s) = (∫ t in (0 : ℝ)..s, ((y t) * (1 : ℝ))))
  (h13 : (((2 * Real.pi) * v_uCE_uB7) * s) = ((2 * Real.pi) * (∫ t in (0 : ℝ)..s, ((y t) * (1 : ℝ)))))
  (h14 : ((2 * Real.pi) * (∫ t in (0 : ℝ)..s, ((y t) * (1 : ℝ)))) = S)
  (h15 : S = (((s * 2) * Real.pi) * v_uCE_uB7))
  : S = (((s * 2) * Real.pi) * v_uCE_uB7) := by
  sorry

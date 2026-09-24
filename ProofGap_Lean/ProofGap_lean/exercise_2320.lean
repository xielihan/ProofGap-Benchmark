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

-- exercise: exercise_2320

theorem proof_gap_exercise_2320_1
  (v : (ℝ -> ℝ))
  (v_0 : ℝ)
  (g : ℝ)
  (T : ℝ)
  (v_T : ℝ)
  (Avg_v : ℝ)
  (h1 : v_0 ∈ (Set.univ : Set ℝ))
  (h2 : g ∈ (Set.univ : Set ℝ))
  (h3 : T ∈ (Set.univ : Set ℝ))
  (h4 : v_T ∈ (Set.univ : Set ℝ))
  (h5 : Avg_v ∈ (Set.univ : Set ℝ))
  (h6 : T > 0)
  (h7 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≥ 0)) → ((v t) = (v_0 + (g * t))))))
  (h8 : v_T = (v T))
  (h9 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Icc 0 T))) → ((v t) = (v_0 + (g * t))))) ∧ (Avg_v = ((1 /. T) * (∫ t in (0 : ℝ)..T, ((v t) * (1 : ℝ))))))
  : Avg_v = ((1 /. T) * (∫ t in (0 : ℝ)..T, ((v_0 + (g * t)) * (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_2320_2
  (v : (ℝ -> ℝ))
  (v_0 : ℝ)
  (g : ℝ)
  (T : ℝ)
  (v_T : ℝ)
  (Avg_v : ℝ)
  (h1 : v_0 ∈ (Set.univ : Set ℝ))
  (h2 : g ∈ (Set.univ : Set ℝ))
  (h3 : T ∈ (Set.univ : Set ℝ))
  (h4 : v_T ∈ (Set.univ : Set ℝ))
  (h5 : Avg_v ∈ (Set.univ : Set ℝ))
  (h6 : T > 0)
  (h7 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≥ 0)) → ((v t) = (v_0 + (g * t))))))
  (h8 : v_T = (v T))
  (h9 : Avg_v = ((1 /. T) * (∫ t in (0 : ℝ)..T, ((v_0 + (g * t)) * (1 : ℝ)))))
  : ((1 /. T) * (∫ t in (0 : ℝ)..T, ((v_0 + (g * t)) * (1 : ℝ)))) = ((((1 /. 2) * g) * T) + v_0) := by
  sorry

theorem proof_gap_exercise_2320_3
  (v : (ℝ -> ℝ))
  (v_0 : ℝ)
  (g : ℝ)
  (T : ℝ)
  (v_T : ℝ)
  (Avg_v : ℝ)
  (h1 : v_0 ∈ (Set.univ : Set ℝ))
  (h2 : g ∈ (Set.univ : Set ℝ))
  (h3 : T ∈ (Set.univ : Set ℝ))
  (h4 : v_T ∈ (Set.univ : Set ℝ))
  (h5 : Avg_v ∈ (Set.univ : Set ℝ))
  (h6 : T > 0)
  (h7 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≥ 0)) → ((v t) = (v_0 + (g * t))))))
  (h8 : v_T = (v T))
  (h9 : Avg_v = ((1 /. T) * (∫ t in (0 : ℝ)..T, ((v_0 + (g * t)) * (1 : ℝ)))))
  (h10 : ((1 /. T) * (∫ t in (0 : ℝ)..T, ((v_0 + (g * t)) * (1 : ℝ)))) = ((((1 /. 2) * g) * T) + v_0))
  : ((((1 /. 2) * g) * T) + v_0) = ((1 /. 2) * (v_0 + v_T)) := by
  sorry

theorem proof_gap_exercise_2320_4
  (v : (ℝ -> ℝ))
  (v_0 : ℝ)
  (g : ℝ)
  (T : ℝ)
  (v_T : ℝ)
  (Avg_v : ℝ)
  (h1 : v_0 ∈ (Set.univ : Set ℝ))
  (h2 : g ∈ (Set.univ : Set ℝ))
  (h3 : T ∈ (Set.univ : Set ℝ))
  (h4 : v_T ∈ (Set.univ : Set ℝ))
  (h5 : Avg_v ∈ (Set.univ : Set ℝ))
  (h6 : T > 0)
  (h7 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≥ 0)) → ((v t) = (v_0 + (g * t))))))
  (h8 : v_T = (v T))
  (h9 : Avg_v = ((1 /. T) * (∫ t in (0 : ℝ)..T, ((v_0 + (g * t)) * (1 : ℝ)))))
  (h10 : ((1 /. T) * (∫ t in (0 : ℝ)..T, ((v_0 + (g * t)) * (1 : ℝ)))) = ((((1 /. 2) * g) * T) + v_0))
  (h11 : ((((1 /. 2) * g) * T) + v_0) = ((1 /. 2) * (v_0 + v_T)))
  : Avg_v = ((1 /. 2) * (v_0 + v_T)) := by
  sorry

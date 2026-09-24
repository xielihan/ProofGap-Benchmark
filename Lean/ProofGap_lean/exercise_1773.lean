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

-- exercise: exercise_1773

theorem proof_gap_exercise_1773_1
  (h1 : t = (Real.tan x))
  : (Real.cos x) ≠ 0 := by
  sorry

theorem proof_gap_exercise_1773_2
  (h1 : t = (Real.tan x))
  (h2 : (Real.cos x) ≠ 0)
  : ((1 /. ((Real.cos x) ^ (4 : ℕ))) • (fderiv ℝ (fun (x : ℝ) => x))) = ((1 + (t ^ (2 : ℕ))) • (fderiv ℝ (fun (t : ℝ) => t))) := by
  sorry

theorem proof_gap_exercise_1773_3
  (h1 : t = (Real.tan x))
  (h2 : (Real.cos x) ≠ 0)
  (h3 : ((1 /. ((Real.cos x) ^ (4 : ℕ))) • (fderiv ℝ (fun (x : ℝ) => x))) = ((1 + (t ^ (2 : ℕ))) • (fderiv ℝ (fun (t : ℝ) => t))))
  : ((((Real.sin x) ^ (2 : ℕ)) /. ((Real.cos x) ^ (6 : ℕ))) • (fderiv ℝ (fun (x : ℝ) => x))) = (((t ^ (4 : ℕ)) + (t ^ (2 : ℕ))) • (fderiv ℝ (fun (t : ℝ) => t))) := by
  sorry

theorem proof_gap_exercise_1773_4
  (h1 : t = (Real.tan x))
  (h2 : (Real.cos x) ≠ 0)
  (h3 : ((1 /. ((Real.cos x) ^ (4 : ℕ))) • (fderiv ℝ (fun (x : ℝ) => x))) = ((1 + (t ^ (2 : ℕ))) • (fderiv ℝ (fun (t : ℝ) => t))))
  (h4 : ((((Real.sin x) ^ (2 : ℕ)) /. ((Real.cos x) ^ (6 : ℕ))) • (fderiv ℝ (fun (x : ℝ) => x))) = (((t ^ (4 : ℕ)) + (t ^ (2 : ℕ))) • (fderiv ℝ (fun (t : ℝ) => t))))
  : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((Real.cos x) ≠ 0)) → ((iteratedDeriv 1 (fun t_1 => F_2 t_1) x) = ((((Real.sin x) ^ (2 : ℕ)) /. ((Real.cos x) ^ (6 : ℕ))) * (iteratedDeriv 1 (fun t_1 => t_1) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t_1 => F_3 t_1) t) = (((t ^ (4 : ℕ)) + (t ^ (2 : ℕ))) * (iteratedDeriv 1 (fun t_1 => t_1) t)))))}) := by
  sorry

theorem proof_gap_exercise_1773_5
  (h1 : t = (Real.tan x))
  (h2 : (Real.cos x) ≠ 0)
  (h3 : ((1 /. ((Real.cos x) ^ (4 : ℕ))) • (fderiv ℝ (fun (x : ℝ) => x))) = ((1 + (t ^ (2 : ℕ))) • (fderiv ℝ (fun (t : ℝ) => t))))
  (h4 : ((((Real.sin x) ^ (2 : ℕ)) /. ((Real.cos x) ^ (6 : ℕ))) • (fderiv ℝ (fun (x : ℝ) => x))) = (((t ^ (4 : ℕ)) + (t ^ (2 : ℕ))) • (fderiv ℝ (fun (t : ℝ) => t))))
  (h5 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((Real.cos x) ≠ 0)) → ((iteratedDeriv 1 (fun t_1 => F_2 t_1) x) = ((((Real.sin x) ^ (2 : ℕ)) /. ((Real.cos x) ^ (6 : ℕ))) * (iteratedDeriv 1 (fun t_1 => t_1) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t_1 => F_3 t_1) t) = (((t ^ (4 : ℕ)) + (t ^ (2 : ℕ))) * (iteratedDeriv 1 (fun t_1 => t_1) t)))))}))
  : ({F_4 : (ℝ -> ℝ) | (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t_1 => F_4 t_1) t) = (((t ^ (4 : ℕ)) + (t ^ (2 : ℕ))) * (iteratedDeriv 1 (fun t_1 => t_1) t)))))}) = ({F_5 : (ℝ -> ℝ) | (exists (C : ℝ), ((C ∈ (Set.univ : Set ℝ)) ∧ (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((F_5 t) = ((((1 /. 5) * (t ^ (5 : ℕ))) + ((1 /. 3) * (t ^ (3 : ℕ)))) + C))))))}) := by
  sorry

theorem proof_gap_exercise_1773_6
  (h1 : t = (Real.tan x))
  (h2 : (Real.cos x) ≠ 0)
  (h3 : ((1 /. ((Real.cos x) ^ (4 : ℕ))) • (fderiv ℝ (fun (x : ℝ) => x))) = ((1 + (t ^ (2 : ℕ))) • (fderiv ℝ (fun (t : ℝ) => t))))
  (h4 : ((((Real.sin x) ^ (2 : ℕ)) /. ((Real.cos x) ^ (6 : ℕ))) • (fderiv ℝ (fun (x : ℝ) => x))) = (((t ^ (4 : ℕ)) + (t ^ (2 : ℕ))) • (fderiv ℝ (fun (t : ℝ) => t))))
  (h5 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((Real.cos x) ≠ 0)) → ((iteratedDeriv 1 (fun t_1 => F_2 t_1) x) = ((((Real.sin x) ^ (2 : ℕ)) /. ((Real.cos x) ^ (6 : ℕ))) * (iteratedDeriv 1 (fun t_1 => t_1) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t_1 => F_3 t_1) t) = (((t ^ (4 : ℕ)) + (t ^ (2 : ℕ))) * (iteratedDeriv 1 (fun t_1 => t_1) t)))))}))
  (h6 : ({F_4 : (ℝ -> ℝ) | (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t_1 => F_4 t_1) t) = (((t ^ (4 : ℕ)) + (t ^ (2 : ℕ))) * (iteratedDeriv 1 (fun t_1 => t_1) t)))))}) = ({F_5 : (ℝ -> ℝ) | (exists (C : ℝ), ((C ∈ (Set.univ : Set ℝ)) ∧ (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((F_5 t) = ((((1 /. 5) * (t ^ (5 : ℕ))) + ((1 /. 3) * (t ^ (3 : ℕ)))) + C))))))}))
  : ({F_6 : (ℝ -> ℝ) | (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((Real.cos x) ≠ 0)) → ((iteratedDeriv 1 (fun t_1 => F_6 t_1) x) = ((((Real.sin x) ^ (2 : ℕ)) /. ((Real.cos x) ^ (6 : ℕ))) * (iteratedDeriv 1 (fun t_1 => t_1) x)))))}) = ({F_7 : (ℝ -> ℝ) | (exists (C : ℝ), ((C ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((Real.cos x) ≠ 0)) → ((F_7 x) = ((((1 /. 5) * ((Real.tan x) ^ (5 : ℕ))) + ((1 /. 3) * ((Real.tan x) ^ (3 : ℕ)))) + C))))))}) := by
  sorry

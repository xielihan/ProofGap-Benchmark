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

-- exercise: exercise_1602

theorem proof_gap_exercise_1602_1
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (R : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((x t) = (a * ((Real.cos t) + (t * (Real.sin t))))))))
  (h3 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((y t) = (a * ((Real.sin t) - (t * (Real.cos t))))))))
  : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 0)) ∧ ((Real.cos t) ≠ 0)) → (((lpFunDeri y x) t) = (Real.tan t)))) := by
  sorry

theorem proof_gap_exercise_1602_2
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (R : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((x t) = (a * ((Real.cos t) + (t * (Real.sin t))))))))
  (h3 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((y t) = (a * ((Real.sin t) - (t * (Real.cos t))))))))
  (h4 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 0)) ∧ ((Real.cos t) ≠ 0)) → (((lpFunDeri y x) t) = (Real.tan t)))))
  : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 0)) ∧ ((Real.cos t) ≠ 0)) → (((lpFunDeri (lpFunDeri y x) x) t) = (1 /. ((a * t) * ((Real.cos t) ^ (3 : ℕ))))))) := by
  sorry

theorem proof_gap_exercise_1602_3
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (R : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((x t) = (a * ((Real.cos t) + (t * (Real.sin t))))))))
  (h3 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((y t) = (a * ((Real.sin t) - (t * (Real.cos t))))))))
  (h4 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 0)) ∧ ((Real.cos t) ≠ 0)) → (((lpFunDeri y x) t) = (Real.tan t)))))
  (h5 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 0)) ∧ ((Real.cos t) ≠ 0)) → (((lpFunDeri (lpFunDeri y x) x) t) = (1 /. ((a * t) * ((Real.cos t) ^ (3 : ℕ))))))))
  : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((R t) = ((Real.rpow (1 + ((Real.tan t) ^ (2 : ℕ))) (3 /. 2)) /. (1 /. (a * |((t * ((Real.cos t) ^ (3 : ℕ))))|)))))) := by
  sorry

theorem proof_gap_exercise_1602_4
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (R : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((x t) = (a * ((Real.cos t) + (t * (Real.sin t))))))))
  (h3 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((y t) = (a * ((Real.sin t) - (t * (Real.cos t))))))))
  (h4 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 0)) ∧ ((Real.cos t) ≠ 0)) → (((lpFunDeri y x) t) = (Real.tan t)))))
  (h5 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 0)) ∧ ((Real.cos t) ≠ 0)) → (((lpFunDeri (lpFunDeri y x) x) t) = (1 /. ((a * t) * ((Real.cos t) ^ (3 : ℕ))))))))
  (h6 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((R t) = ((Real.rpow (1 + ((Real.tan t) ^ (2 : ℕ))) (3 /. 2)) /. (1 /. (a * |((t * ((Real.cos t) ^ (3 : ℕ))))|)))))))
  : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((R t) = (a * |(t)|)))) := by
  sorry

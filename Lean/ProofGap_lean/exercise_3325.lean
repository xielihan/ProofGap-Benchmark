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

-- exercise: exercise_3325

theorem proof_gap_exercise_3325_1
  (u : (ℝ × (ℝ × ℝ) -> ℝ))
  (v_uCF_u86 : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) ∧ (z ≠ 0)) → ((u (x, (y, z))) = ((((x * y) /. z) * (Real.log x)) + (x * (v_uCF_u86 ((y /. x), (z /. x)))))))))
  (h2 : Differentiable ℝ v_uCF_u86)
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → (forall (z : ℝ), (((((x > 0) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) ∧ (z ≠ 0)) → ((x * (iteratedDeriv 1 (fun t => u (t, (y, z))) x)) = (((((((x * y) /. z) * (Real.log x)) + ((x * y) /. z)) + (x * (v_uCF_u86 ((y /. x), (z /. x))))) - (y * (iteratedDeriv 1 (fun t => v_uCF_u86 (t, (z /. x))) (y /. x)))) - (z * (iteratedDeriv 1 (fun t => v_uCF_u86 ((y /. x), t)) (z /. x))))))))))) := by
  sorry

theorem proof_gap_exercise_3325_2
  (u : (ℝ × (ℝ × ℝ) -> ℝ))
  (v_uCF_u86 : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) ∧ (z ≠ 0)) → ((u (x, (y, z))) = ((((x * y) /. z) * (Real.log x)) + (x * (v_uCF_u86 ((y /. x), (z /. x)))))))))
  (h2 : Differentiable ℝ v_uCF_u86)
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → (forall (z : ℝ), (((((x > 0) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) ∧ (z ≠ 0)) → ((x * (iteratedDeriv 1 (fun t => u (t, (y, z))) x)) = (((((((x * y) /. z) * (Real.log x)) + ((x * y) /. z)) + (x * (v_uCF_u86 ((y /. x), (z /. x))))) - (y * (iteratedDeriv 1 (fun t => v_uCF_u86 (t, (z /. x))) (y /. x)))) - (z * (iteratedDeriv 1 (fun t => v_uCF_u86 ((y /. x), t)) (z /. x))))))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → (forall (z : ℝ), (((((x > 0) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) ∧ (z ≠ 0)) → ((y * (iteratedDeriv 1 (fun t => u (x, (t, z))) y)) = ((((x * y) /. z) * (Real.log x)) + (y * (iteratedDeriv 1 (fun t => v_uCF_u86 (t, (z /. x))) (y /. x))))))))))) := by
  sorry

theorem proof_gap_exercise_3325_3
  (u : (ℝ × (ℝ × ℝ) -> ℝ))
  (v_uCF_u86 : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) ∧ (z ≠ 0)) → ((u (x, (y, z))) = ((((x * y) /. z) * (Real.log x)) + (x * (v_uCF_u86 ((y /. x), (z /. x)))))))))
  (h2 : Differentiable ℝ v_uCF_u86)
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → (forall (z : ℝ), (((((x > 0) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) ∧ (z ≠ 0)) → ((x * (iteratedDeriv 1 (fun t => u (t, (y, z))) x)) = (((((((x * y) /. z) * (Real.log x)) + ((x * y) /. z)) + (x * (v_uCF_u86 ((y /. x), (z /. x))))) - (y * (iteratedDeriv 1 (fun t => v_uCF_u86 (t, (z /. x))) (y /. x)))) - (z * (iteratedDeriv 1 (fun t => v_uCF_u86 ((y /. x), t)) (z /. x))))))))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → (forall (z : ℝ), (((((x > 0) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) ∧ (z ≠ 0)) → ((y * (iteratedDeriv 1 (fun t => u (x, (t, z))) y)) = ((((x * y) /. z) * (Real.log x)) + (y * (iteratedDeriv 1 (fun t => v_uCF_u86 (t, (z /. x))) (y /. x))))))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → (forall (z : ℝ), (((((x > 0) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) ∧ (z ≠ 0)) → ((z * (iteratedDeriv 1 (fun t => u (x, (y, t))) z)) = (((-((x * y) /. z)) * (Real.log x)) + (z * (iteratedDeriv 1 (fun t => v_uCF_u86 ((y /. x), t)) (z /. x))))))))))) := by
  sorry

theorem proof_gap_exercise_3325_4
  (u : (ℝ × (ℝ × ℝ) -> ℝ))
  (v_uCF_u86 : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) ∧ (z ≠ 0)) → ((u (x, (y, z))) = ((((x * y) /. z) * (Real.log x)) + (x * (v_uCF_u86 ((y /. x), (z /. x)))))))))
  (h2 : Differentiable ℝ v_uCF_u86)
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → (forall (z : ℝ), (((((x > 0) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) ∧ (z ≠ 0)) → ((x * (iteratedDeriv 1 (fun t => u (t, (y, z))) x)) = (((((((x * y) /. z) * (Real.log x)) + ((x * y) /. z)) + (x * (v_uCF_u86 ((y /. x), (z /. x))))) - (y * (iteratedDeriv 1 (fun t => v_uCF_u86 (t, (z /. x))) (y /. x)))) - (z * (iteratedDeriv 1 (fun t => v_uCF_u86 ((y /. x), t)) (z /. x))))))))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → (forall (z : ℝ), (((((x > 0) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) ∧ (z ≠ 0)) → ((y * (iteratedDeriv 1 (fun t => u (x, (t, z))) y)) = ((((x * y) /. z) * (Real.log x)) + (y * (iteratedDeriv 1 (fun t => v_uCF_u86 (t, (z /. x))) (y /. x))))))))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → (forall (z : ℝ), (((((x > 0) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) ∧ (z ≠ 0)) → ((z * (iteratedDeriv 1 (fun t => u (x, (y, t))) z)) = (((-((x * y) /. z)) * (Real.log x)) + (z * (iteratedDeriv 1 (fun t => v_uCF_u86 ((y /. x), t)) (z /. x))))))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → (forall (z : ℝ), (((((x > 0) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) ∧ (z ≠ 0)) → ((((x * (iteratedDeriv 1 (fun t => u (t, (y, z))) x)) + (y * (iteratedDeriv 1 (fun t => u (x, (t, z))) y))) + (z * (iteratedDeriv 1 (fun t => u (x, (y, t))) z))) = ((u (x, (y, z))) + ((x * y) /. z))))))))) := by
  sorry

theorem proof_gap_exercise_3325_5
  (u : (ℝ × (ℝ × ℝ) -> ℝ))
  (v_uCF_u86 : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) ∧ (z ≠ 0)) → ((u (x, (y, z))) = ((((x * y) /. z) * (Real.log x)) + (x * (v_uCF_u86 ((y /. x), (z /. x)))))))))
  (h2 : Differentiable ℝ v_uCF_u86)
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → (forall (z : ℝ), (((((x > 0) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) ∧ (z ≠ 0)) → ((x * (iteratedDeriv 1 (fun t => u (t, (y, z))) x)) = (((((((x * y) /. z) * (Real.log x)) + ((x * y) /. z)) + (x * (v_uCF_u86 ((y /. x), (z /. x))))) - (y * (iteratedDeriv 1 (fun t => v_uCF_u86 (t, (z /. x))) (y /. x)))) - (z * (iteratedDeriv 1 (fun t => v_uCF_u86 ((y /. x), t)) (z /. x))))))))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → (forall (z : ℝ), (((((x > 0) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) ∧ (z ≠ 0)) → ((y * (iteratedDeriv 1 (fun t => u (x, (t, z))) y)) = ((((x * y) /. z) * (Real.log x)) + (y * (iteratedDeriv 1 (fun t => v_uCF_u86 (t, (z /. x))) (y /. x))))))))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → (forall (z : ℝ), (((((x > 0) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) ∧ (z ≠ 0)) → ((z * (iteratedDeriv 1 (fun t => u (x, (y, t))) z)) = (((-((x * y) /. z)) * (Real.log x)) + (z * (iteratedDeriv 1 (fun t => v_uCF_u86 ((y /. x), t)) (z /. x))))))))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → (forall (z : ℝ), (((((x > 0) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) ∧ (z ≠ 0)) → ((((x * (iteratedDeriv 1 (fun t => u (t, (y, z))) x)) + (y * (iteratedDeriv 1 (fun t => u (x, (t, z))) y))) + (z * (iteratedDeriv 1 (fun t => u (x, (y, t))) z))) = ((u (x, (y, z))) + ((x * y) /. z))))))))))
  : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) ∧ (z ≠ 0)) → ((((x * (iteratedDeriv 1 (fun t => u (t, (y, z))) x)) + (y * (iteratedDeriv 1 (fun t => u (x, (t, z))) y))) + (z * (iteratedDeriv 1 (fun t => u (x, (y, t))) z))) = ((u (x, (y, z))) + ((x * y) /. z))))) := by
  sorry

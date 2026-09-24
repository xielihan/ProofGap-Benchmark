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

-- exercise: exercise_2390_1

theorem proof_gap_exercise_2390_1_1
  (VP : ℝ)
  (h1 : VP ∈ (Set.univ : Set ℝ))
  (h2 : (forall (v_uCE_uB5 : ℝ), ((((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5)) ∧ (v_uCE_uB5 < 1)) → (Tendsto (fun v_uCE_uB5_1 : ℝ => ((∫ x in (-(1 : ℝ))..(0 - v_uCE_uB5_1), (((1 : ℝ) /. x) * (1 : ℝ))) + (∫ x in (0 + v_uCE_uB5_1)..(1 : ℝ), (((1 : ℝ) /. x) * (1 : ℝ))))) (𝓝[>] 0) (𝓝 VP)))))
  : (forall (v_uCE_uB5 : ℝ), ((((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5)) ∧ (v_uCE_uB5 < 1)) → (((∫ x in (-(1 : ℝ))..(0 - v_uCE_uB5), (((1 : ℝ) /. x) * (1 : ℝ))) + (∫ x in (0 + v_uCE_uB5)..(1 : ℝ), (((1 : ℝ) /. x) * (1 : ℝ)))) = ((((Real.log v_uCE_uB5) - (Real.log (1 : ℝ))) + (Real.log (1 : ℝ))) - (Real.log v_uCE_uB5))))) := by
  sorry

theorem proof_gap_exercise_2390_1_2
  (VP : ℝ)
  (h1 : VP ∈ (Set.univ : Set ℝ))
  (h2 : (forall (v_uCE_uB5 : ℝ), ((((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5)) ∧ (v_uCE_uB5 < 1)) → (Tendsto (fun v_uCE_uB5_1 : ℝ => ((∫ x in (-(1 : ℝ))..(0 - v_uCE_uB5_1), (((1 : ℝ) /. x) * (1 : ℝ))) + (∫ x in (0 + v_uCE_uB5_1)..(1 : ℝ), (((1 : ℝ) /. x) * (1 : ℝ))))) (𝓝[>] 0) (𝓝 VP)))))
  (h3 : (forall (v_uCE_uB5 : ℝ), ((((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5)) ∧ (v_uCE_uB5 < 1)) → (((∫ x in (-(1 : ℝ))..(0 - v_uCE_uB5), (((1 : ℝ) /. x) * (1 : ℝ))) + (∫ x in (0 + v_uCE_uB5)..(1 : ℝ), (((1 : ℝ) /. x) * (1 : ℝ)))) = ((((Real.log v_uCE_uB5) - (Real.log (1 : ℝ))) + (Real.log (1 : ℝ))) - (Real.log v_uCE_uB5))))))
  : (forall (v_uCE_uB5 : ℝ), ((((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5)) ∧ (v_uCE_uB5 < 1)) → (((((Real.log v_uCE_uB5) - (Real.log (1 : ℝ))) + (Real.log (1 : ℝ))) - (Real.log v_uCE_uB5)) = 0))) := by
  sorry

theorem proof_gap_exercise_2390_1_3
  (VP : ℝ)
  (h1 : VP ∈ (Set.univ : Set ℝ))
  (h2 : (forall (v_uCE_uB5 : ℝ), ((((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5)) ∧ (v_uCE_uB5 < 1)) → (Tendsto (fun v_uCE_uB5_1 : ℝ => ((∫ x in (-(1 : ℝ))..(0 - v_uCE_uB5_1), (((1 : ℝ) /. x) * (1 : ℝ))) + (∫ x in (0 + v_uCE_uB5_1)..(1 : ℝ), (((1 : ℝ) /. x) * (1 : ℝ))))) (𝓝[>] 0) (𝓝 VP)))))
  (h3 : (forall (v_uCE_uB5 : ℝ), ((((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5)) ∧ (v_uCE_uB5 < 1)) → (((∫ x in (-(1 : ℝ))..(0 - v_uCE_uB5), (((1 : ℝ) /. x) * (1 : ℝ))) + (∫ x in (0 + v_uCE_uB5)..(1 : ℝ), (((1 : ℝ) /. x) * (1 : ℝ)))) = ((((Real.log v_uCE_uB5) - (Real.log (1 : ℝ))) + (Real.log (1 : ℝ))) - (Real.log v_uCE_uB5))))))
  (h4 : (forall (v_uCE_uB5 : ℝ), ((((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5)) ∧ (v_uCE_uB5 < 1)) → (((((Real.log v_uCE_uB5) - (Real.log (1 : ℝ))) + (Real.log (1 : ℝ))) - (Real.log v_uCE_uB5)) = 0))))
  : (forall (v_uCE_uB5 : ℝ), ((((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5)) ∧ (v_uCE_uB5 < 1)) → (Tendsto (fun v_uCE_uB5_1 : ℝ => ((∫ x in (-(1 : ℝ))..(0 - v_uCE_uB5_1), (((1 : ℝ) /. x) * (1 : ℝ))) + (∫ x in (0 + v_uCE_uB5_1)..(1 : ℝ), (((1 : ℝ) /. x) * (1 : ℝ))))) (𝓝[>] 0) (𝓝 0)))) := by
  sorry

theorem proof_gap_exercise_2390_1_4
  (VP : ℝ)
  (h1 : VP ∈ (Set.univ : Set ℝ))
  (h2 : (forall (v_uCE_uB5 : ℝ), ((((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5)) ∧ (v_uCE_uB5 < 1)) → (Tendsto (fun v_uCE_uB5_1 : ℝ => ((∫ x in (-(1 : ℝ))..(0 - v_uCE_uB5_1), (((1 : ℝ) /. x) * (1 : ℝ))) + (∫ x in (0 + v_uCE_uB5_1)..(1 : ℝ), (((1 : ℝ) /. x) * (1 : ℝ))))) (𝓝[>] 0) (𝓝 VP)))))
  (h3 : (forall (v_uCE_uB5 : ℝ), ((((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5)) ∧ (v_uCE_uB5 < 1)) → (((∫ x in (-(1 : ℝ))..(0 - v_uCE_uB5), (((1 : ℝ) /. x) * (1 : ℝ))) + (∫ x in (0 + v_uCE_uB5)..(1 : ℝ), (((1 : ℝ) /. x) * (1 : ℝ)))) = ((((Real.log v_uCE_uB5) - (Real.log (1 : ℝ))) + (Real.log (1 : ℝ))) - (Real.log v_uCE_uB5))))))
  (h4 : (forall (v_uCE_uB5 : ℝ), ((((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5)) ∧ (v_uCE_uB5 < 1)) → (((((Real.log v_uCE_uB5) - (Real.log (1 : ℝ))) + (Real.log (1 : ℝ))) - (Real.log v_uCE_uB5)) = 0))))
  (h5 : (forall (v_uCE_uB5 : ℝ), ((((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5)) ∧ (v_uCE_uB5 < 1)) → (Tendsto (fun v_uCE_uB5_1 : ℝ => ((∫ x in (-(1 : ℝ))..(0 - v_uCE_uB5_1), (((1 : ℝ) /. x) * (1 : ℝ))) + (∫ x in (0 + v_uCE_uB5_1)..(1 : ℝ), (((1 : ℝ) /. x) * (1 : ℝ))))) (𝓝[>] 0) (𝓝 0)))))
  : VP = 0 := by
  sorry

theorem proof_gap_exercise_2390_1_5
  (VP : ℝ)
  (h1 : VP ∈ (Set.univ : Set ℝ))
  (h2 : (forall (v_uCE_uB5 : ℝ), ((((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5)) ∧ (v_uCE_uB5 < 1)) → (Tendsto (fun v_uCE_uB5_1 : ℝ => ((∫ x in (-(1 : ℝ))..(0 - v_uCE_uB5_1), (((1 : ℝ) /. x) * (1 : ℝ))) + (∫ x in (0 + v_uCE_uB5_1)..(1 : ℝ), (((1 : ℝ) /. x) * (1 : ℝ))))) (𝓝[>] 0) (𝓝 VP)))))
  (h3 : (forall (v_uCE_uB5 : ℝ), ((((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5)) ∧ (v_uCE_uB5 < 1)) → (((∫ x in (-(1 : ℝ))..(0 - v_uCE_uB5), (((1 : ℝ) /. x) * (1 : ℝ))) + (∫ x in (0 + v_uCE_uB5)..(1 : ℝ), (((1 : ℝ) /. x) * (1 : ℝ)))) = ((((Real.log v_uCE_uB5) - (Real.log (1 : ℝ))) + (Real.log (1 : ℝ))) - (Real.log v_uCE_uB5))))))
  (h4 : (forall (v_uCE_uB5 : ℝ), ((((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5)) ∧ (v_uCE_uB5 < 1)) → (((((Real.log v_uCE_uB5) - (Real.log (1 : ℝ))) + (Real.log (1 : ℝ))) - (Real.log v_uCE_uB5)) = 0))))
  (h5 : (forall (v_uCE_uB5 : ℝ), ((((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5)) ∧ (v_uCE_uB5 < 1)) → (Tendsto (fun v_uCE_uB5_1 : ℝ => ((∫ x in (-(1 : ℝ))..(0 - v_uCE_uB5_1), (((1 : ℝ) /. x) * (1 : ℝ))) + (∫ x in (0 + v_uCE_uB5_1)..(1 : ℝ), (((1 : ℝ) /. x) * (1 : ℝ))))) (𝓝[>] 0) (𝓝 0)))))
  (h6 : VP = 0)
  : VP = 0 := by
  sorry

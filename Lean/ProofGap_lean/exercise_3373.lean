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

-- exercise: exercise_3373

theorem proof_gap_exercise_3373_1
  (y : (ℝ -> ℝ))
  (v_uCE_uB5 : ℝ)
  (h1 : v_uCE_uB5 ∈ (Set.univ : Set ℝ))
  (h2 : 0 < v_uCE_uB5)
  (h3 : v_uCE_uB5 < 1)
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((y x) - (v_uCE_uB5 * (Real.sin (y x)))) = x))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => y t) x) - ((v_uCE_uB5 * (iteratedDeriv 1 (fun t => y t) x)) * (Real.cos (y x)))) = 1))) := by
  sorry

theorem proof_gap_exercise_3373_2
  (y : (ℝ -> ℝ))
  (v_uCE_uB5 : ℝ)
  (h1 : v_uCE_uB5 ∈ (Set.univ : Set ℝ))
  (h2 : 0 < v_uCE_uB5)
  (h3 : v_uCE_uB5 < 1)
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((y x) - (v_uCE_uB5 * (Real.sin (y x)))) = x))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => y t) x) - ((v_uCE_uB5 * (iteratedDeriv 1 (fun t => y t) x)) * (Real.cos (y x)))) = 1))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (1 /. (1 - (v_uCE_uB5 * (Real.cos (y x)))))))) := by
  sorry

theorem proof_gap_exercise_3373_3
  (y : (ℝ -> ℝ))
  (v_uCE_uB5 : ℝ)
  (h1 : v_uCE_uB5 ∈ (Set.univ : Set ℝ))
  (h2 : 0 < v_uCE_uB5)
  (h3 : v_uCE_uB5 < 1)
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((y x) - (v_uCE_uB5 * (Real.sin (y x)))) = x))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => y t) x) - ((v_uCE_uB5 * (iteratedDeriv 1 (fun t => y t) x)) * (Real.cos (y x)))) = 1))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (1 /. (1 - (v_uCE_uB5 * (Real.cos (y x)))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => y t) x) = (-(((v_uCE_uB5 * (iteratedDeriv 1 (fun t => y t) x)) * (Real.sin (y x))) /. ((1 - (v_uCE_uB5 * (Real.cos (y x)))) ^ (2 : ℕ))))))) := by
  sorry

theorem proof_gap_exercise_3373_4
  (y : (ℝ -> ℝ))
  (v_uCE_uB5 : ℝ)
  (h1 : v_uCE_uB5 ∈ (Set.univ : Set ℝ))
  (h2 : 0 < v_uCE_uB5)
  (h3 : v_uCE_uB5 < 1)
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((y x) - (v_uCE_uB5 * (Real.sin (y x)))) = x))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => y t) x) - ((v_uCE_uB5 * (iteratedDeriv 1 (fun t => y t) x)) * (Real.cos (y x)))) = 1))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (1 /. (1 - (v_uCE_uB5 * (Real.cos (y x)))))))))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => y t) x) = (-(((v_uCE_uB5 * (iteratedDeriv 1 (fun t => y t) x)) * (Real.sin (y x))) /. ((1 - (v_uCE_uB5 * (Real.cos (y x)))) ^ (2 : ℕ))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => y t) x) = (-((v_uCE_uB5 * (Real.sin (y x))) /. ((1 - (v_uCE_uB5 * (Real.cos (y x)))) ^ (3 : ℕ))))))) := by
  sorry

theorem proof_gap_exercise_3373_5
  (y : (ℝ -> ℝ))
  (v_uCE_uB5 : ℝ)
  (h1 : v_uCE_uB5 ∈ (Set.univ : Set ℝ))
  (h2 : 0 < v_uCE_uB5)
  (h3 : v_uCE_uB5 < 1)
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((y x) - (v_uCE_uB5 * (Real.sin (y x)))) = x))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => y t) x) - ((v_uCE_uB5 * (iteratedDeriv 1 (fun t => y t) x)) * (Real.cos (y x)))) = 1))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (1 /. (1 - (v_uCE_uB5 * (Real.cos (y x)))))))))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => y t) x) = (-(((v_uCE_uB5 * (iteratedDeriv 1 (fun t => y t) x)) * (Real.sin (y x))) /. ((1 - (v_uCE_uB5 * (Real.cos (y x)))) ^ (2 : ℕ))))))))
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => y t) x) = (-((v_uCE_uB5 * (Real.sin (y x))) /. ((1 - (v_uCE_uB5 * (Real.cos (y x)))) ^ (3 : ℕ))))))))
  : (fun (x1 : ℝ) => (iteratedDeriv 1 (fun t => y t) x1)) = (fun (x : ℝ) => (1 /. (1 - (v_uCE_uB5 * (Real.cos (y x)))))) := by
  sorry

theorem proof_gap_exercise_3373_6
  (y : (ℝ -> ℝ))
  (v_uCE_uB5 : ℝ)
  (h1 : v_uCE_uB5 ∈ (Set.univ : Set ℝ))
  (h2 : 0 < v_uCE_uB5)
  (h3 : v_uCE_uB5 < 1)
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((y x) - (v_uCE_uB5 * (Real.sin (y x)))) = x))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => y t) x) - ((v_uCE_uB5 * (iteratedDeriv 1 (fun t => y t) x)) * (Real.cos (y x)))) = 1))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (1 /. (1 - (v_uCE_uB5 * (Real.cos (y x)))))))))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => y t) x) = (-(((v_uCE_uB5 * (iteratedDeriv 1 (fun t => y t) x)) * (Real.sin (y x))) /. ((1 - (v_uCE_uB5 * (Real.cos (y x)))) ^ (2 : ℕ))))))))
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => y t) x) = (-((v_uCE_uB5 * (Real.sin (y x))) /. ((1 - (v_uCE_uB5 * (Real.cos (y x)))) ^ (3 : ℕ))))))))
  (h9 : (fun (x1 : ℝ) => (iteratedDeriv 1 (fun t => y t) x1)) = (fun (x : ℝ) => (1 /. (1 - (v_uCE_uB5 * (Real.cos (y x)))))))
  : (fun (x1 : ℝ) => (iteratedDeriv 2 (fun t => y t) x1)) = (fun (x : ℝ) => (-((v_uCE_uB5 * (Real.sin (y x))) /. ((1 - (v_uCE_uB5 * (Real.cos (y x)))) ^ (3 : ℕ))))) := by
  sorry

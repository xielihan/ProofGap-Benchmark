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

-- exercise: exercise_650_2

theorem proof_gap_exercise_650_2_1
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (((x * (Real.sin (Real.rpow x (((2 : ℝ))⁻¹)))) /. (x * (Real.rpow x (((2 : ℝ))⁻¹)))) = ((Real.sin (Real.rpow x (((2 : ℝ))⁻¹))) /. (Real.rpow x (((2 : ℝ))⁻¹)))))) := by
  sorry

theorem proof_gap_exercise_650_2_2
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (((x * (Real.sin (Real.rpow x (((2 : ℝ))⁻¹)))) /. (x * (Real.rpow x (((2 : ℝ))⁻¹)))) = ((Real.sin (Real.rpow x (((2 : ℝ))⁻¹))) /. (Real.rpow x (((2 : ℝ))⁻¹)))))))
  : Tendsto (fun x : ℝ => ((x * (Real.sin (Real.rpow x (((2 : ℝ))⁻¹)))) /. (x * (Real.rpow x (((2 : ℝ))⁻¹))))) (𝓝[>] 0) (𝓝 1) := by
  sorry

theorem proof_gap_exercise_650_2_3
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (((x * (Real.sin (Real.rpow x (((2 : ℝ))⁻¹)))) /. (x * (Real.rpow x (((2 : ℝ))⁻¹)))) = ((Real.sin (Real.rpow x (((2 : ℝ))⁻¹))) /. (Real.rpow x (((2 : ℝ))⁻¹)))))))
  (h2 : Tendsto (fun x : ℝ => ((x * (Real.sin (Real.rpow x (((2 : ℝ))⁻¹)))) /. (x * (Real.rpow x (((2 : ℝ))⁻¹))))) (𝓝[>] 0) (𝓝 1))
  : 1 ∈ (Set.univ : Set ℝ) := by
  sorry

theorem proof_gap_exercise_650_2_4
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (((x * (Real.sin (Real.rpow x (((2 : ℝ))⁻¹)))) /. (x * (Real.rpow x (((2 : ℝ))⁻¹)))) = ((Real.sin (Real.rpow x (((2 : ℝ))⁻¹))) /. (Real.rpow x (((2 : ℝ))⁻¹)))))))
  (h2 : Tendsto (fun x : ℝ => ((x * (Real.sin (Real.rpow x (((2 : ℝ))⁻¹)))) /. (x * (Real.rpow x (((2 : ℝ))⁻¹))))) (𝓝[>] 0) (𝓝 1))
  (h3 : 1 ∈ (Set.univ : Set ℝ))
  : 1 ≠ 0 := by
  sorry

theorem proof_gap_exercise_650_2_5
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (((x * (Real.sin (Real.rpow x (((2 : ℝ))⁻¹)))) /. (x * (Real.rpow x (((2 : ℝ))⁻¹)))) = ((Real.sin (Real.rpow x (((2 : ℝ))⁻¹))) /. (Real.rpow x (((2 : ℝ))⁻¹)))))))
  (h2 : Tendsto (fun x : ℝ => ((x * (Real.sin (Real.rpow x (((2 : ℝ))⁻¹)))) /. (x * (Real.rpow x (((2 : ℝ))⁻¹))))) (𝓝[>] 0) (𝓝 1))
  (h3 : 1 ∈ (Set.univ : Set ℝ))
  (h4 : 1 ≠ 0)
  : (exists (C : ℝ), (((C ∈ (Set.univ : Set ℝ)) ∧ (C ≠ 0)) ∧ (Tendsto (fun x : ℝ => ((x * (Real.sin (Real.rpow x (((2 : ℝ))⁻¹)))) /. (x * (Real.rpow x (((2 : ℝ))⁻¹))))) (𝓝[>] 0) (𝓝 C)))) := by
  sorry

theorem proof_gap_exercise_650_2_6
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (((x * (Real.sin (Real.rpow x (((2 : ℝ))⁻¹)))) /. (x * (Real.rpow x (((2 : ℝ))⁻¹)))) = ((Real.sin (Real.rpow x (((2 : ℝ))⁻¹))) /. (Real.rpow x (((2 : ℝ))⁻¹)))))))
  (h2 : Tendsto (fun x : ℝ => ((x * (Real.sin (Real.rpow x (((2 : ℝ))⁻¹)))) /. (x * (Real.rpow x (((2 : ℝ))⁻¹))))) (𝓝[>] 0) (𝓝 1))
  (h3 : 1 ∈ (Set.univ : Set ℝ))
  (h4 : 1 ≠ 0)
  (h5 : (exists (C : ℝ), (((C ∈ (Set.univ : Set ℝ)) ∧ (C ≠ 0)) ∧ (Tendsto (fun x : ℝ => ((x * (Real.sin (Real.rpow x (((2 : ℝ))⁻¹)))) /. (x * (Real.rpow x (((2 : ℝ))⁻¹))))) (𝓝[>] 0) (𝓝 C)))))
  : (exists (C : ℝ), (((C ∈ (Set.univ : Set ℝ)) ∧ (C ≠ 0)) ∧ (Tendsto (fun x : ℝ => ((x * (Real.sin (Real.rpow x (((2 : ℝ))⁻¹)))) /. (x * (Real.rpow x (((2 : ℝ))⁻¹))))) (𝓝[>] 0) (𝓝 C)))) := by
  sorry

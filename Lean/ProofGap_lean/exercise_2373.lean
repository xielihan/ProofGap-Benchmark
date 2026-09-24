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

-- exercise: exercise_2373

theorem proof_gap_exercise_2373_1
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ (Real.pi /. 2))) → (((Real.sin x) > 0) ∧ ((Real.log (Real.sin x)) ∈ (Set.univ : Set ℝ))))) := by
  sorry

theorem proof_gap_exercise_2373_2
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ (Real.pi /. 2))) → (((Real.sin x) > 0) ∧ ((Real.log (Real.sin x)) ∈ (Set.univ : Set ℝ))))))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => (((Real.rpow (x /. (Real.sin x)) (1 /. 3)) * (Real.rpow (Real.sin x) (((3 : ℝ))⁻¹))) * (Real.log (Real.sin x)))) (𝓝[>] 0) (𝓝 L) ∧ (Tendsto (fun x : ℝ => ((Real.rpow x (5 /. 6)) * ((Real.log (Real.sin x)) /. (Real.rpow x (((2 : ℝ))⁻¹))))) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x : ℝ => (((Real.rpow (x /. (Real.sin x)) (1 /. 3)) * (Real.rpow (Real.sin x) (((3 : ℝ))⁻¹))) * (Real.log (Real.sin x)))))))) := by
  sorry

theorem proof_gap_exercise_2373_3
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ (Real.pi /. 2))) → (((Real.sin x) > 0) ∧ ((Real.log (Real.sin x)) ∈ (Set.univ : Set ℝ))))))
  (h2 : Tendsto (fun x : ℝ => ((Real.rpow x (5 /. 6)) * ((Real.log (Real.sin x)) /. (Real.rpow x (((2 : ℝ))⁻¹))))) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x : ℝ => (((Real.rpow (x /. (Real.sin x)) (1 /. 3)) * (Real.rpow (Real.sin x) (((3 : ℝ))⁻¹))) * (Real.log (Real.sin x)))))))
  (h3 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((Real.rpow (x /. (Real.sin x)) (1 /. 3)) * (Real.rpow (Real.sin x) (((3 : ℝ))⁻¹))) * (Real.log (Real.sin x)))) (𝓝[>] 0) (𝓝 L))
  : Tendsto (fun x : ℝ => (((Real.rpow (x /. (Real.sin x)) (1 /. 3)) * (Real.rpow (Real.sin x) (((3 : ℝ))⁻¹))) * (Real.log (Real.sin x)))) (𝓝[>] 0) (𝓝 0) := by
  sorry

theorem proof_gap_exercise_2373_4
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ (Real.pi /. 2))) → (((Real.sin x) > 0) ∧ ((Real.log (Real.sin x)) ∈ (Set.univ : Set ℝ))))))
  (h2 : Tendsto (fun x : ℝ => ((Real.rpow x (5 /. 6)) * ((Real.log (Real.sin x)) /. (Real.rpow x (((2 : ℝ))⁻¹))))) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x : ℝ => (((Real.rpow (x /. (Real.sin x)) (1 /. 3)) * (Real.rpow (Real.sin x) (((3 : ℝ))⁻¹))) * (Real.log (Real.sin x)))))))
  (h3 : Tendsto (fun x : ℝ => (((Real.rpow (x /. (Real.sin x)) (1 /. 3)) * (Real.rpow (Real.sin x) (((3 : ℝ))⁻¹))) * (Real.log (Real.sin x)))) (𝓝[>] 0) (𝓝 0))
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((Real.rpow (x /. (Real.sin x)) (1 /. 3)) * (Real.rpow (Real.sin x) (((3 : ℝ))⁻¹))) * (Real.log (Real.sin x)))) (𝓝[>] 0) (𝓝 L))
  : Tendsto (fun x : ℝ => ((Real.rpow x (5 /. 6)) * ((Real.log (Real.sin x)) /. (Real.rpow x (((2 : ℝ))⁻¹))))) (𝓝[>] 0) (𝓝 0) := by
  sorry

theorem proof_gap_exercise_2373_5
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ (Real.pi /. 2))) → (((Real.sin x) > 0) ∧ ((Real.log (Real.sin x)) ∈ (Set.univ : Set ℝ))))))
  (h2 : Tendsto (fun x : ℝ => ((Real.rpow x (5 /. 6)) * ((Real.log (Real.sin x)) /. (Real.rpow x (((2 : ℝ))⁻¹))))) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x : ℝ => (((Real.rpow (x /. (Real.sin x)) (1 /. 3)) * (Real.rpow (Real.sin x) (((3 : ℝ))⁻¹))) * (Real.log (Real.sin x)))))))
  (h3 : Tendsto (fun x : ℝ => (((Real.rpow (x /. (Real.sin x)) (1 /. 3)) * (Real.rpow (Real.sin x) (((3 : ℝ))⁻¹))) * (Real.log (Real.sin x)))) (𝓝[>] 0) (𝓝 0))
  (h4 : Tendsto (fun x : ℝ => ((Real.rpow x (5 /. 6)) * ((Real.log (Real.sin x)) /. (Real.rpow x (((2 : ℝ))⁻¹))))) (𝓝[>] 0) (𝓝 0))
  (h5 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((Real.rpow (x /. (Real.sin x)) (1 /. 3)) * (Real.rpow (Real.sin x) (((3 : ℝ))⁻¹))) * (Real.log (Real.sin x)))) (𝓝[>] 0) (𝓝 L))
  : (exists (I : ℝ), ((I ∈ (Set.univ : Set ℝ)) ∧ ((∫ x in (0 : ℝ)..(Real.pi /. 2), (((Real.log (Real.sin x)) /. (Real.rpow x (((2 : ℝ))⁻¹))) * (1 : ℝ))) = I))) := by
  sorry

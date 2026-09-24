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

-- exercise: exercise_506_3

theorem proof_gap_exercise_506_3_1
  : (forall (x : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 0)) ∧ (x ≠ 1)) ∧ (x ≠ (-(2 : ℝ)))) ∧ (((1 + x) /. (2 + x)) > 0)) → ((Real.rpow ((1 + x) /. (2 + x)) ((1 - (Real.rpow x (((2 : ℝ))⁻¹))) /. (1 - x))) = (Real.rpow ((1 + x) /. (2 + x)) (1 /. (1 + (Real.rpow x (((2 : ℝ))⁻¹)))))))) := by
  sorry

theorem proof_gap_exercise_506_3_2
  (h1 : (forall (x : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 0)) ∧ (x ≠ 1)) ∧ (x ≠ (-(2 : ℝ)))) ∧ (((1 + x) /. (2 + x)) > 0)) → ((Real.rpow ((1 + x) /. (2 + x)) ((1 - (Real.rpow x (((2 : ℝ))⁻¹))) /. (1 - x))) = (Real.rpow ((1 + x) /. (2 + x)) (1 /. (1 + (Real.rpow x (((2 : ℝ))⁻¹)))))))))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => (Real.rpow ((1 + x) /. (2 + x)) (1 /. (1 + (Real.rpow x (((2 : ℝ))⁻¹)))))) atTop (𝓝 L) ∧ (Tendsto (fun x : ℝ => (Real.rpow ((1 + x) /. (2 + x)) ((1 - (Real.rpow x (((2 : ℝ))⁻¹))) /. (1 - x)))) atTop (𝓝 (atTop.limUnder (fun x : ℝ => (Real.rpow ((1 + x) /. (2 + x)) (1 /. (1 + (Real.rpow x (((2 : ℝ))⁻¹)))))))))) := by
  sorry

theorem proof_gap_exercise_506_3_3
  (h1 : (forall (x : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 0)) ∧ (x ≠ 1)) ∧ (x ≠ (-(2 : ℝ)))) ∧ (((1 + x) /. (2 + x)) > 0)) → ((Real.rpow ((1 + x) /. (2 + x)) ((1 - (Real.rpow x (((2 : ℝ))⁻¹))) /. (1 - x))) = (Real.rpow ((1 + x) /. (2 + x)) (1 /. (1 + (Real.rpow x (((2 : ℝ))⁻¹)))))))))
  (h2 : Tendsto (fun x : ℝ => (Real.rpow ((1 + x) /. (2 + x)) ((1 - (Real.rpow x (((2 : ℝ))⁻¹))) /. (1 - x)))) atTop (𝓝 (atTop.limUnder (fun x : ℝ => (Real.rpow ((1 + x) /. (2 + x)) (1 /. (1 + (Real.rpow x (((2 : ℝ))⁻¹)))))))))
  (h3 : ∃ L : ℝ, Tendsto (fun x : ℝ => (Real.rpow ((1 + x) /. (2 + x)) (1 /. (1 + (Real.rpow x (((2 : ℝ))⁻¹)))))) atTop (𝓝 L))
  : Tendsto (fun x : ℝ => (Real.rpow ((1 + x) /. (2 + x)) (1 /. (1 + (Real.rpow x (((2 : ℝ))⁻¹)))))) atTop (𝓝 ((1 : ℕ) ^ (0 : ℕ))) := by
  sorry

theorem proof_gap_exercise_506_3_4
  (h1 : (forall (x : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 0)) ∧ (x ≠ 1)) ∧ (x ≠ (-(2 : ℝ)))) ∧ (((1 + x) /. (2 + x)) > 0)) → ((Real.rpow ((1 + x) /. (2 + x)) ((1 - (Real.rpow x (((2 : ℝ))⁻¹))) /. (1 - x))) = (Real.rpow ((1 + x) /. (2 + x)) (1 /. (1 + (Real.rpow x (((2 : ℝ))⁻¹)))))))))
  (h2 : Tendsto (fun x : ℝ => (Real.rpow ((1 + x) /. (2 + x)) ((1 - (Real.rpow x (((2 : ℝ))⁻¹))) /. (1 - x)))) atTop (𝓝 (atTop.limUnder (fun x : ℝ => (Real.rpow ((1 + x) /. (2 + x)) (1 /. (1 + (Real.rpow x (((2 : ℝ))⁻¹)))))))))
  (h3 : Tendsto (fun x : ℝ => (Real.rpow ((1 + x) /. (2 + x)) (1 /. (1 + (Real.rpow x (((2 : ℝ))⁻¹)))))) atTop (𝓝 ((1 : ℕ) ^ (0 : ℕ))))
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => (Real.rpow ((1 + x) /. (2 + x)) (1 /. (1 + (Real.rpow x (((2 : ℝ))⁻¹)))))) atTop (𝓝 L))
  : ((1 : ℕ) ^ (0 : ℕ)) = 1 := by
  sorry

theorem proof_gap_exercise_506_3_5
  (h1 : (forall (x : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 0)) ∧ (x ≠ 1)) ∧ (x ≠ (-(2 : ℝ)))) ∧ (((1 + x) /. (2 + x)) > 0)) → ((Real.rpow ((1 + x) /. (2 + x)) ((1 - (Real.rpow x (((2 : ℝ))⁻¹))) /. (1 - x))) = (Real.rpow ((1 + x) /. (2 + x)) (1 /. (1 + (Real.rpow x (((2 : ℝ))⁻¹)))))))))
  (h2 : Tendsto (fun x : ℝ => (Real.rpow ((1 + x) /. (2 + x)) ((1 - (Real.rpow x (((2 : ℝ))⁻¹))) /. (1 - x)))) atTop (𝓝 (atTop.limUnder (fun x : ℝ => (Real.rpow ((1 + x) /. (2 + x)) (1 /. (1 + (Real.rpow x (((2 : ℝ))⁻¹)))))))))
  (h3 : Tendsto (fun x : ℝ => (Real.rpow ((1 + x) /. (2 + x)) (1 /. (1 + (Real.rpow x (((2 : ℝ))⁻¹)))))) atTop (𝓝 ((1 : ℕ) ^ (0 : ℕ))))
  (h4 : ((1 : ℕ) ^ (0 : ℕ)) = 1)
  (h5 : ∃ L : ℝ, Tendsto (fun x : ℝ => (Real.rpow ((1 + x) /. (2 + x)) (1 /. (1 + (Real.rpow x (((2 : ℝ))⁻¹)))))) atTop (𝓝 L))
  : Tendsto (fun x : ℝ => (Real.rpow ((1 + x) /. (2 + x)) ((1 - (Real.rpow x (((2 : ℝ))⁻¹))) /. (1 - x)))) atTop (𝓝 1) := by
  sorry

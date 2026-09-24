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

-- exercise: exercise_505

theorem proof_gap_exercise_505_1
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 0)) → (((Real.sin (Real.rpow (x + 1) (((2 : ℝ))⁻¹))) - (Real.sin (Real.rpow x (((2 : ℝ))⁻¹)))) = ((2 * (Real.sin (((Real.rpow (x + 1) (((2 : ℝ))⁻¹)) - (Real.rpow x (((2 : ℝ))⁻¹))) /. 2))) * (Real.cos (((Real.rpow (x + 1) (((2 : ℝ))⁻¹)) + (Real.rpow x (((2 : ℝ))⁻¹))) /. 2)))))) := by
  sorry

theorem proof_gap_exercise_505_2
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 0)) → (((Real.sin (Real.rpow (x + 1) (((2 : ℝ))⁻¹))) - (Real.sin (Real.rpow x (((2 : ℝ))⁻¹)))) = ((2 * (Real.sin (((Real.rpow (x + 1) (((2 : ℝ))⁻¹)) - (Real.rpow x (((2 : ℝ))⁻¹))) /. 2))) * (Real.cos (((Real.rpow (x + 1) (((2 : ℝ))⁻¹)) + (Real.rpow x (((2 : ℝ))⁻¹))) /. 2)))))))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => (1 /. ((Real.rpow (x + 1) (((2 : ℝ))⁻¹)) + (Real.rpow x (((2 : ℝ))⁻¹))))) atTop (𝓝 L) ∧ (Tendsto (fun x : ℝ => ((Real.rpow (x + 1) (((2 : ℝ))⁻¹)) - (Real.rpow x (((2 : ℝ))⁻¹)))) atTop (𝓝 (atTop.limUnder (fun x : ℝ => (1 /. ((Real.rpow (x + 1) (((2 : ℝ))⁻¹)) + (Real.rpow x (((2 : ℝ))⁻¹))))))))) := by
  sorry

theorem proof_gap_exercise_505_3
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 0)) → (((Real.sin (Real.rpow (x + 1) (((2 : ℝ))⁻¹))) - (Real.sin (Real.rpow x (((2 : ℝ))⁻¹)))) = ((2 * (Real.sin (((Real.rpow (x + 1) (((2 : ℝ))⁻¹)) - (Real.rpow x (((2 : ℝ))⁻¹))) /. 2))) * (Real.cos (((Real.rpow (x + 1) (((2 : ℝ))⁻¹)) + (Real.rpow x (((2 : ℝ))⁻¹))) /. 2)))))))
  (h2 : Tendsto (fun x : ℝ => ((Real.rpow (x + 1) (((2 : ℝ))⁻¹)) - (Real.rpow x (((2 : ℝ))⁻¹)))) atTop (𝓝 (atTop.limUnder (fun x : ℝ => (1 /. ((Real.rpow (x + 1) (((2 : ℝ))⁻¹)) + (Real.rpow x (((2 : ℝ))⁻¹))))))))
  (h3 : ∃ L : ℝ, Tendsto (fun x : ℝ => (1 /. ((Real.rpow (x + 1) (((2 : ℝ))⁻¹)) + (Real.rpow x (((2 : ℝ))⁻¹))))) atTop (𝓝 L))
  : Tendsto (fun x : ℝ => (1 /. ((Real.rpow (x + 1) (((2 : ℝ))⁻¹)) + (Real.rpow x (((2 : ℝ))⁻¹))))) atTop (𝓝 0) := by
  sorry

theorem proof_gap_exercise_505_4
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 0)) → (((Real.sin (Real.rpow (x + 1) (((2 : ℝ))⁻¹))) - (Real.sin (Real.rpow x (((2 : ℝ))⁻¹)))) = ((2 * (Real.sin (((Real.rpow (x + 1) (((2 : ℝ))⁻¹)) - (Real.rpow x (((2 : ℝ))⁻¹))) /. 2))) * (Real.cos (((Real.rpow (x + 1) (((2 : ℝ))⁻¹)) + (Real.rpow x (((2 : ℝ))⁻¹))) /. 2)))))))
  (h2 : Tendsto (fun x : ℝ => ((Real.rpow (x + 1) (((2 : ℝ))⁻¹)) - (Real.rpow x (((2 : ℝ))⁻¹)))) atTop (𝓝 (atTop.limUnder (fun x : ℝ => (1 /. ((Real.rpow (x + 1) (((2 : ℝ))⁻¹)) + (Real.rpow x (((2 : ℝ))⁻¹))))))))
  (h3 : Tendsto (fun x : ℝ => (1 /. ((Real.rpow (x + 1) (((2 : ℝ))⁻¹)) + (Real.rpow x (((2 : ℝ))⁻¹))))) atTop (𝓝 0))
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => (1 /. ((Real.rpow (x + 1) (((2 : ℝ))⁻¹)) + (Real.rpow x (((2 : ℝ))⁻¹))))) atTop (𝓝 L))
  : Tendsto (fun x : ℝ => ((Real.rpow (x + 1) (((2 : ℝ))⁻¹)) - (Real.rpow x (((2 : ℝ))⁻¹)))) atTop (𝓝 0) := by
  sorry

theorem proof_gap_exercise_505_5
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 0)) → (((Real.sin (Real.rpow (x + 1) (((2 : ℝ))⁻¹))) - (Real.sin (Real.rpow x (((2 : ℝ))⁻¹)))) = ((2 * (Real.sin (((Real.rpow (x + 1) (((2 : ℝ))⁻¹)) - (Real.rpow x (((2 : ℝ))⁻¹))) /. 2))) * (Real.cos (((Real.rpow (x + 1) (((2 : ℝ))⁻¹)) + (Real.rpow x (((2 : ℝ))⁻¹))) /. 2)))))))
  (h2 : Tendsto (fun x : ℝ => ((Real.rpow (x + 1) (((2 : ℝ))⁻¹)) - (Real.rpow x (((2 : ℝ))⁻¹)))) atTop (𝓝 (atTop.limUnder (fun x : ℝ => (1 /. ((Real.rpow (x + 1) (((2 : ℝ))⁻¹)) + (Real.rpow x (((2 : ℝ))⁻¹))))))))
  (h3 : Tendsto (fun x : ℝ => (1 /. ((Real.rpow (x + 1) (((2 : ℝ))⁻¹)) + (Real.rpow x (((2 : ℝ))⁻¹))))) atTop (𝓝 0))
  (h4 : Tendsto (fun x : ℝ => ((Real.rpow (x + 1) (((2 : ℝ))⁻¹)) - (Real.rpow x (((2 : ℝ))⁻¹)))) atTop (𝓝 0))
  (h5 : ∃ L : ℝ, Tendsto (fun x : ℝ => (1 /. ((Real.rpow (x + 1) (((2 : ℝ))⁻¹)) + (Real.rpow x (((2 : ℝ))⁻¹))))) atTop (𝓝 L))
  : Tendsto (fun x : ℝ => (Real.sin (((Real.rpow (x + 1) (((2 : ℝ))⁻¹)) - (Real.rpow x (((2 : ℝ))⁻¹))) /. 2))) atTop (𝓝 0) := by
  sorry

theorem proof_gap_exercise_505_6
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 0)) → (((Real.sin (Real.rpow (x + 1) (((2 : ℝ))⁻¹))) - (Real.sin (Real.rpow x (((2 : ℝ))⁻¹)))) = ((2 * (Real.sin (((Real.rpow (x + 1) (((2 : ℝ))⁻¹)) - (Real.rpow x (((2 : ℝ))⁻¹))) /. 2))) * (Real.cos (((Real.rpow (x + 1) (((2 : ℝ))⁻¹)) + (Real.rpow x (((2 : ℝ))⁻¹))) /. 2)))))))
  (h2 : Tendsto (fun x : ℝ => ((Real.rpow (x + 1) (((2 : ℝ))⁻¹)) - (Real.rpow x (((2 : ℝ))⁻¹)))) atTop (𝓝 (atTop.limUnder (fun x : ℝ => (1 /. ((Real.rpow (x + 1) (((2 : ℝ))⁻¹)) + (Real.rpow x (((2 : ℝ))⁻¹))))))))
  (h3 : Tendsto (fun x : ℝ => (1 /. ((Real.rpow (x + 1) (((2 : ℝ))⁻¹)) + (Real.rpow x (((2 : ℝ))⁻¹))))) atTop (𝓝 0))
  (h4 : Tendsto (fun x : ℝ => ((Real.rpow (x + 1) (((2 : ℝ))⁻¹)) - (Real.rpow x (((2 : ℝ))⁻¹)))) atTop (𝓝 0))
  (h5 : Tendsto (fun x : ℝ => (Real.sin (((Real.rpow (x + 1) (((2 : ℝ))⁻¹)) - (Real.rpow x (((2 : ℝ))⁻¹))) /. 2))) atTop (𝓝 0))
  (h6 : ∃ L : ℝ, Tendsto (fun x : ℝ => (1 /. ((Real.rpow (x + 1) (((2 : ℝ))⁻¹)) + (Real.rpow x (((2 : ℝ))⁻¹))))) atTop (𝓝 L))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 0)) → (|((Real.cos (((Real.rpow (x + 1) (((2 : ℝ))⁻¹)) + (Real.rpow x (((2 : ℝ))⁻¹))) /. 2)))| ≤ 1))) := by
  sorry

theorem proof_gap_exercise_505_7
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 0)) → (((Real.sin (Real.rpow (x + 1) (((2 : ℝ))⁻¹))) - (Real.sin (Real.rpow x (((2 : ℝ))⁻¹)))) = ((2 * (Real.sin (((Real.rpow (x + 1) (((2 : ℝ))⁻¹)) - (Real.rpow x (((2 : ℝ))⁻¹))) /. 2))) * (Real.cos (((Real.rpow (x + 1) (((2 : ℝ))⁻¹)) + (Real.rpow x (((2 : ℝ))⁻¹))) /. 2)))))))
  (h2 : Tendsto (fun x : ℝ => ((Real.rpow (x + 1) (((2 : ℝ))⁻¹)) - (Real.rpow x (((2 : ℝ))⁻¹)))) atTop (𝓝 (atTop.limUnder (fun x : ℝ => (1 /. ((Real.rpow (x + 1) (((2 : ℝ))⁻¹)) + (Real.rpow x (((2 : ℝ))⁻¹))))))))
  (h3 : Tendsto (fun x : ℝ => (1 /. ((Real.rpow (x + 1) (((2 : ℝ))⁻¹)) + (Real.rpow x (((2 : ℝ))⁻¹))))) atTop (𝓝 0))
  (h4 : Tendsto (fun x : ℝ => ((Real.rpow (x + 1) (((2 : ℝ))⁻¹)) - (Real.rpow x (((2 : ℝ))⁻¹)))) atTop (𝓝 0))
  (h5 : Tendsto (fun x : ℝ => (Real.sin (((Real.rpow (x + 1) (((2 : ℝ))⁻¹)) - (Real.rpow x (((2 : ℝ))⁻¹))) /. 2))) atTop (𝓝 0))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 0)) → (|((Real.cos (((Real.rpow (x + 1) (((2 : ℝ))⁻¹)) + (Real.rpow x (((2 : ℝ))⁻¹))) /. 2)))| ≤ 1))))
  (h7 : ∃ L : ℝ, Tendsto (fun x : ℝ => (1 /. ((Real.rpow (x + 1) (((2 : ℝ))⁻¹)) + (Real.rpow x (((2 : ℝ))⁻¹))))) atTop (𝓝 L))
  : Tendsto (fun x : ℝ => ((Real.sin (Real.rpow (x + 1) (((2 : ℝ))⁻¹))) - (Real.sin (Real.rpow x (((2 : ℝ))⁻¹))))) atTop (𝓝 0) := by
  sorry

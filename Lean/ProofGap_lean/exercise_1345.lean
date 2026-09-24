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

-- exercise: exercise_1345

theorem proof_gap_exercise_1345_1
  (k : ℝ)
  (h1 : k ∈ (Set.univ : Set ℝ))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) ∧ (x ≠ (Real.exp (-(1 : ℝ))))) → (∃ L : ℝ, Tendsto (fun x_1 : ℝ => ((Real.log x_1) /. (1 + (Real.log x_1)))) (𝓝[>] 0) (𝓝 L) ∧ (Tendsto (fun x_1 : ℝ => ((k /. (1 + (Real.log x_1))) * (Real.log x_1))) (𝓝[>] 0) (𝓝 (k * (𝓝[>] 0).limUnder (fun x_1 : ℝ => ((Real.log x_1) /. (1 + (Real.log x_1)))))))))) := by
  sorry

theorem proof_gap_exercise_1345_2
  (k : ℝ)
  (h1 : k ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (∃ L : ℝ, Tendsto (fun x_1 : ℝ => ((Real.log x_1) /. (1 + (Real.log x_1)))) (𝓝[>] 0) (𝓝 L) ∧ ((((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) ∧ (x ≠ (Real.exp (-(1 : ℝ))))) → (Tendsto (fun x_1 : ℝ => ((k /. (1 + (Real.log x_1))) * (Real.log x_1))) (𝓝[>] 0) (𝓝 (k * (𝓝[>] 0).limUnder (fun x_1 : ℝ => ((Real.log x_1) /. (1 + (Real.log x_1)))))))))))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => ((1 /. x) /. (1 /. x))) (𝓝[>] 0) (𝓝 L) ∧ (Tendsto (fun x : ℝ => ((Real.log x) /. (1 + (Real.log x)))) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x : ℝ => ((1 /. x) /. (1 /. x))))))) := by
  sorry

theorem proof_gap_exercise_1345_3
  (k : ℝ)
  (h1 : k ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (∃ L : ℝ, Tendsto (fun x_1 : ℝ => ((Real.log x_1) /. (1 + (Real.log x_1)))) (𝓝[>] 0) (𝓝 L) ∧ ((((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) ∧ (x ≠ (Real.exp (-(1 : ℝ))))) → (Tendsto (fun x_1 : ℝ => ((k /. (1 + (Real.log x_1))) * (Real.log x_1))) (𝓝[>] 0) (𝓝 (k * (𝓝[>] 0).limUnder (fun x_1 : ℝ => ((Real.log x_1) /. (1 + (Real.log x_1)))))))))))
  (h3 : Tendsto (fun x : ℝ => ((Real.log x) /. (1 + (Real.log x)))) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x : ℝ => ((1 /. x) /. (1 /. x))))))
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((1 /. x) /. (1 /. x))) (𝓝[>] 0) (𝓝 L))
  : Tendsto (fun x : ℝ => ((1 /. x) /. (1 /. x))) (𝓝[>] 0) (𝓝 1) := by
  sorry

theorem proof_gap_exercise_1345_4
  (k : ℝ)
  (h1 : k ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (∃ L : ℝ, Tendsto (fun x_1 : ℝ => ((Real.log x_1) /. (1 + (Real.log x_1)))) (𝓝[>] 0) (𝓝 L) ∧ ((((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) ∧ (x ≠ (Real.exp (-(1 : ℝ))))) → (Tendsto (fun x_1 : ℝ => ((k /. (1 + (Real.log x_1))) * (Real.log x_1))) (𝓝[>] 0) (𝓝 (k * (𝓝[>] 0).limUnder (fun x_1 : ℝ => ((Real.log x_1) /. (1 + (Real.log x_1)))))))))))
  (h3 : Tendsto (fun x : ℝ => ((Real.log x) /. (1 + (Real.log x)))) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x : ℝ => ((1 /. x) /. (1 /. x))))))
  (h4 : Tendsto (fun x : ℝ => ((1 /. x) /. (1 /. x))) (𝓝[>] 0) (𝓝 1))
  (h5 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((1 /. x) /. (1 /. x))) (𝓝[>] 0) (𝓝 L))
  : Tendsto (fun x : ℝ => ((Real.log x) /. (1 + (Real.log x)))) (𝓝[>] 0) (𝓝 1) := by
  sorry

theorem proof_gap_exercise_1345_5
  (k : ℝ)
  (h1 : k ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (∃ L : ℝ, Tendsto (fun x_1 : ℝ => ((Real.log x_1) /. (1 + (Real.log x_1)))) (𝓝[>] 0) (𝓝 L) ∧ ((((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) ∧ (x ≠ (Real.exp (-(1 : ℝ))))) → (Tendsto (fun x_1 : ℝ => ((k /. (1 + (Real.log x_1))) * (Real.log x_1))) (𝓝[>] 0) (𝓝 (k * (𝓝[>] 0).limUnder (fun x_1 : ℝ => ((Real.log x_1) /. (1 + (Real.log x_1)))))))))))
  (h3 : Tendsto (fun x : ℝ => ((Real.log x) /. (1 + (Real.log x)))) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x : ℝ => ((1 /. x) /. (1 /. x))))))
  (h4 : Tendsto (fun x : ℝ => ((1 /. x) /. (1 /. x))) (𝓝[>] 0) (𝓝 1))
  (h5 : Tendsto (fun x : ℝ => ((Real.log x) /. (1 + (Real.log x)))) (𝓝[>] 0) (𝓝 1))
  (h6 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((1 /. x) /. (1 /. x))) (𝓝[>] 0) (𝓝 L))
  : Tendsto (fun x : ℝ => ((k /. (1 + (Real.log x))) * (Real.log x))) (𝓝[>] 0) (𝓝 k) := by
  sorry

theorem proof_gap_exercise_1345_6
  (k : ℝ)
  (h1 : k ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (∃ L : ℝ, Tendsto (fun x_1 : ℝ => ((Real.log x_1) /. (1 + (Real.log x_1)))) (𝓝[>] 0) (𝓝 L) ∧ ((((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) ∧ (x ≠ (Real.exp (-(1 : ℝ))))) → (Tendsto (fun x_1 : ℝ => ((k /. (1 + (Real.log x_1))) * (Real.log x_1))) (𝓝[>] 0) (𝓝 (k * (𝓝[>] 0).limUnder (fun x_1 : ℝ => ((Real.log x_1) /. (1 + (Real.log x_1)))))))))))
  (h3 : Tendsto (fun x : ℝ => ((Real.log x) /. (1 + (Real.log x)))) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x : ℝ => ((1 /. x) /. (1 /. x))))))
  (h4 : Tendsto (fun x : ℝ => ((1 /. x) /. (1 /. x))) (𝓝[>] 0) (𝓝 1))
  (h5 : Tendsto (fun x : ℝ => ((Real.log x) /. (1 + (Real.log x)))) (𝓝[>] 0) (𝓝 1))
  (h6 : Tendsto (fun x : ℝ => ((k /. (1 + (Real.log x))) * (Real.log x))) (𝓝[>] 0) (𝓝 k))
  (h7 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((1 /. x) /. (1 /. x))) (𝓝[>] 0) (𝓝 L))
  : Tendsto (fun x : ℝ => (Real.rpow x (k /. (1 + (Real.log x))))) (𝓝[>] 0) (𝓝 (Real.exp k)) := by
  sorry

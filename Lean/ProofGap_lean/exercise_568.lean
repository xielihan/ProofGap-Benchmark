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

-- exercise: exercise_568

theorem proof_gap_exercise_568_1
  (h1 : (forall (x : ℝ), ((x ∈ ({x_1 : ℝ | 0 < x_1})) → (x > 0))))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => (Real.log (((Real.rpow (x + 2) (x + 2)) * (Real.rpow x x)) /. (Real.rpow (x + 1) ((2 * x) + 2))))) atTop (𝓝 L) ∧ (Tendsto (fun x : ℝ => ((((x + 2) * (Real.log (x + 2))) - ((2 * (x + 1)) * (Real.log (x + 1)))) + (x * (Real.log x)))) atTop (𝓝 (atTop.limUnder (fun x : ℝ => (Real.log (((Real.rpow (x + 2) (x + 2)) * (Real.rpow x x)) /. (Real.rpow (x + 1) ((2 * x) + 2))))))))) := by
  sorry

theorem proof_gap_exercise_568_2
  (h1 : (forall (x : ℝ), ((x ∈ ({x_1 : ℝ | 0 < x_1})) → (x > 0))))
  (h2 : Tendsto (fun x : ℝ => ((((x + 2) * (Real.log (x + 2))) - ((2 * (x + 1)) * (Real.log (x + 1)))) + (x * (Real.log x)))) atTop (𝓝 (atTop.limUnder (fun x : ℝ => (Real.log (((Real.rpow (x + 2) (x + 2)) * (Real.rpow x x)) /. (Real.rpow (x + 1) ((2 * x) + 2))))))))
  (h3 : ∃ L : ℝ, Tendsto (fun x : ℝ => (Real.log (((Real.rpow (x + 2) (x + 2)) * (Real.rpow x x)) /. (Real.rpow (x + 1) ((2 * x) + 2))))) atTop (𝓝 L))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => (Real.log ((Real.rpow (1 + (2 /. x)) (((x /. 2) * 2) + 2)) /. (Real.rpow (1 + (1 /. x)) ((2 * x) + 2))))) atTop (𝓝 L) ∧ (Tendsto (fun x : ℝ => ((((x + 2) * (Real.log (x + 2))) - ((2 * (x + 1)) * (Real.log (x + 1)))) + (x * (Real.log x)))) atTop (𝓝 (atTop.limUnder (fun x : ℝ => (Real.log ((Real.rpow (1 + (2 /. x)) (((x /. 2) * 2) + 2)) /. (Real.rpow (1 + (1 /. x)) ((2 * x) + 2))))))))) := by
  sorry

theorem proof_gap_exercise_568_3
  (h1 : (forall (x : ℝ), ((x ∈ ({x_1 : ℝ | 0 < x_1})) → (x > 0))))
  (h2 : Tendsto (fun x : ℝ => ((((x + 2) * (Real.log (x + 2))) - ((2 * (x + 1)) * (Real.log (x + 1)))) + (x * (Real.log x)))) atTop (𝓝 (atTop.limUnder (fun x : ℝ => (Real.log (((Real.rpow (x + 2) (x + 2)) * (Real.rpow x x)) /. (Real.rpow (x + 1) ((2 * x) + 2))))))))
  (h3 : Tendsto (fun x : ℝ => ((((x + 2) * (Real.log (x + 2))) - ((2 * (x + 1)) * (Real.log (x + 1)))) + (x * (Real.log x)))) atTop (𝓝 (atTop.limUnder (fun x : ℝ => (Real.log ((Real.rpow (1 + (2 /. x)) (((x /. 2) * 2) + 2)) /. (Real.rpow (1 + (1 /. x)) ((2 * x) + 2))))))))
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => (Real.log (((Real.rpow (x + 2) (x + 2)) * (Real.rpow x x)) /. (Real.rpow (x + 1) ((2 * x) + 2))))) atTop (𝓝 L))
  (h5 : ∃ L : ℝ, Tendsto (fun x : ℝ => (Real.log ((Real.rpow (1 + (2 /. x)) (((x /. 2) * 2) + 2)) /. (Real.rpow (1 + (1 /. x)) ((2 * x) + 2))))) atTop (𝓝 L))
  : Tendsto (fun x : ℝ => ((((x + 2) * (Real.log (x + 2))) - ((2 * (x + 1)) * (Real.log (x + 1)))) + (x * (Real.log x)))) atTop (𝓝 (Real.log ((Real.exp (2 : ℝ)) /. (Real.exp (2 : ℝ))))) := by
  sorry

theorem proof_gap_exercise_568_4
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (x > 0))))
  (h2 : Tendsto (fun x : ℝ => ((((x + 2) * (Real.log (x + 2))) - ((2 * (x + 1)) * (Real.log (x + 1)))) + (x * (Real.log x)))) atTop (𝓝 (atTop.limUnder (fun x : ℝ => (Real.log (((Real.rpow (x + 2) (x + 2)) * (Real.rpow x x)) /. (Real.rpow (x + 1) ((2 * x) + 2))))))))
  (h3 : Tendsto (fun x : ℝ => ((((x + 2) * (Real.log (x + 2))) - ((2 * (x + 1)) * (Real.log (x + 1)))) + (x * (Real.log x)))) atTop (𝓝 (atTop.limUnder (fun x : ℝ => (Real.log ((Real.rpow (1 + (2 /. x)) (((x /. 2) * 2) + 2)) /. (Real.rpow (1 + (1 /. x)) ((2 * x) + 2))))))))
  (h4 : Tendsto (fun x : ℝ => ((((x + 2) * (Real.log (x + 2))) - ((2 * (x + 1)) * (Real.log (x + 1)))) + (x * (Real.log x)))) atTop (𝓝 (Real.log ((Real.exp (2 : ℝ)) /. (Real.exp (2 : ℝ))))))
  (h5 : ∃ L : ℝ, Tendsto (fun x : ℝ => (Real.log (((Real.rpow (x + 2) (x + 2)) * (Real.rpow x x)) /. (Real.rpow (x + 1) ((2 * x) + 2))))) atTop (𝓝 L))
  (h6 : ∃ L : ℝ, Tendsto (fun x : ℝ => (Real.log ((Real.rpow (1 + (2 /. x)) (((x /. 2) * 2) + 2)) /. (Real.rpow (1 + (1 /. x)) ((2 * x) + 2))))) atTop (𝓝 L))
  : (Real.log ((Real.exp (2 : ℝ)) /. (Real.exp (2 : ℝ)))) = 0 := by
  sorry

theorem proof_gap_exercise_568_5
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (x > 0))))
  (h2 : Tendsto (fun x : ℝ => ((((x + 2) * (Real.log (x + 2))) - ((2 * (x + 1)) * (Real.log (x + 1)))) + (x * (Real.log x)))) atTop (𝓝 (atTop.limUnder (fun x : ℝ => (Real.log (((Real.rpow (x + 2) (x + 2)) * (Real.rpow x x)) /. (Real.rpow (x + 1) ((2 * x) + 2))))))))
  (h3 : Tendsto (fun x : ℝ => ((((x + 2) * (Real.log (x + 2))) - ((2 * (x + 1)) * (Real.log (x + 1)))) + (x * (Real.log x)))) atTop (𝓝 (atTop.limUnder (fun x : ℝ => (Real.log ((Real.rpow (1 + (2 /. x)) (((x /. 2) * 2) + 2)) /. (Real.rpow (1 + (1 /. x)) ((2 * x) + 2))))))))
  (h4 : Tendsto (fun x : ℝ => ((((x + 2) * (Real.log (x + 2))) - ((2 * (x + 1)) * (Real.log (x + 1)))) + (x * (Real.log x)))) atTop (𝓝 (Real.log ((Real.exp (2 : ℝ)) /. (Real.exp (2 : ℝ))))))
  (h5 : (Real.log ((Real.exp (2 : ℝ)) /. (Real.exp (2 : ℝ)))) = 0)
  (h6 : ∃ L : ℝ, Tendsto (fun x : ℝ => (Real.log (((Real.rpow (x + 2) (x + 2)) * (Real.rpow x x)) /. (Real.rpow (x + 1) ((2 * x) + 2))))) atTop (𝓝 L))
  (h7 : ∃ L : ℝ, Tendsto (fun x : ℝ => (Real.log ((Real.rpow (1 + (2 /. x)) (((x /. 2) * 2) + 2)) /. (Real.rpow (1 + (1 /. x)) ((2 * x) + 2))))) atTop (𝓝 L))
  : Tendsto (fun x : ℝ => ((((x + 2) * (Real.log (x + 2))) - ((2 * (x + 1)) * (Real.log (x + 1)))) + (x * (Real.log x)))) atTop (𝓝 0) := by
  sorry

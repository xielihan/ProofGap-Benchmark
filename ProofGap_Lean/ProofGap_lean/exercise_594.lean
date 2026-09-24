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

-- exercise: exercise_594

theorem proof_gap_exercise_594_1
  (h1 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((Real.rpow ((1 + x) + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) - (Real.rpow ((1 - x) + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) = ((2 * x) /. ((Real.rpow ((1 + x) + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) + (Real.rpow ((1 - x) + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))) := by
  sorry

theorem proof_gap_exercise_594_2
  (h1 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((Real.rpow ((1 + x) + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) - (Real.rpow ((1 - x) + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) = ((2 * x) /. ((Real.rpow ((1 + x) + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) + (Real.rpow ((1 - x) + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x < 0)) ∧ (x = (-(Real.rpow (x ^ (2 : ℕ)) (((2 : ℝ))⁻¹))))) → (∃ L : ℝ, Tendsto (fun x_1 : ℝ => ((-(2 : ℝ)) /. ((Real.rpow (((1 /. (x_1 ^ (2 : ℕ))) + (1 /. x_1)) + 1) (((2 : ℝ))⁻¹)) + (Real.rpow (((1 /. (x_1 ^ (2 : ℕ))) - (1 /. x_1)) + 1) (((2 : ℝ))⁻¹))))) atBot (𝓝 L) ∧ (Tendsto (fun x_1 : ℝ => ((Real.rpow ((1 + x_1) + (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) - (Real.rpow ((1 - x_1) + (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) atBot (𝓝 (atBot.limUnder (fun x_1 : ℝ => ((-(2 : ℝ)) /. ((Real.rpow (((1 /. (x_1 ^ (2 : ℕ))) + (1 /. x_1)) + 1) (((2 : ℝ))⁻¹)) + (Real.rpow (((1 /. (x_1 ^ (2 : ℕ))) - (1 /. x_1)) + 1) (((2 : ℝ))⁻¹))))))))))) := by
  sorry

theorem proof_gap_exercise_594_3
  (h1 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((Real.rpow ((1 + x) + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) - (Real.rpow ((1 - x) + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) = ((2 * x) /. ((Real.rpow ((1 + x) + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) + (Real.rpow ((1 - x) + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))))
  (h3 : (forall (x : ℝ), (∃ L : ℝ, Tendsto (fun x_1 : ℝ => ((-(2 : ℝ)) /. ((Real.rpow (((1 /. (x_1 ^ (2 : ℕ))) + (1 /. x_1)) + 1) (((2 : ℝ))⁻¹)) + (Real.rpow (((1 /. (x_1 ^ (2 : ℕ))) - (1 /. x_1)) + 1) (((2 : ℝ))⁻¹))))) atBot (𝓝 L) ∧ ((((x ∈ (Set.univ : Set ℝ)) ∧ (x < 0)) ∧ (x = (-(Real.rpow (x ^ (2 : ℕ)) (((2 : ℝ))⁻¹))))) → (Tendsto (fun x_1 : ℝ => ((Real.rpow ((1 + x_1) + (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) - (Real.rpow ((1 - x_1) + (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) atBot (𝓝 (atBot.limUnder (fun x_1 : ℝ => ((-(2 : ℝ)) /. ((Real.rpow (((1 /. (x_1 ^ (2 : ℕ))) + (1 /. x_1)) + 1) (((2 : ℝ))⁻¹)) + (Real.rpow (((1 /. (x_1 ^ (2 : ℕ))) - (1 /. x_1)) + 1) (((2 : ℝ))⁻¹))))))))))))
  : Tendsto (fun x : ℝ => ((-(2 : ℝ)) /. ((Real.rpow (((1 /. (x ^ (2 : ℕ))) + (1 /. x)) + 1) (((2 : ℝ))⁻¹)) + (Real.rpow (((1 /. (x ^ (2 : ℕ))) - (1 /. x)) + 1) (((2 : ℝ))⁻¹))))) atBot (𝓝 (-(1 : ℝ))) := by
  sorry

theorem proof_gap_exercise_594_4
  (h1 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((Real.rpow ((1 + x) + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) - (Real.rpow ((1 - x) + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) = ((2 * x) /. ((Real.rpow ((1 + x) + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) + (Real.rpow ((1 - x) + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))))
  (h3 : (forall (x : ℝ), (∃ L : ℝ, Tendsto (fun x_1 : ℝ => ((-(2 : ℝ)) /. ((Real.rpow (((1 /. (x_1 ^ (2 : ℕ))) + (1 /. x_1)) + 1) (((2 : ℝ))⁻¹)) + (Real.rpow (((1 /. (x_1 ^ (2 : ℕ))) - (1 /. x_1)) + 1) (((2 : ℝ))⁻¹))))) atBot (𝓝 L) ∧ ((((x ∈ (Set.univ : Set ℝ)) ∧ (x < 0)) ∧ (x = (-(Real.rpow (x ^ (2 : ℕ)) (((2 : ℝ))⁻¹))))) → (Tendsto (fun x_1 : ℝ => ((Real.rpow ((1 + x_1) + (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) - (Real.rpow ((1 - x_1) + (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) atBot (𝓝 (atBot.limUnder (fun x_1 : ℝ => ((-(2 : ℝ)) /. ((Real.rpow (((1 /. (x_1 ^ (2 : ℕ))) + (1 /. x_1)) + 1) (((2 : ℝ))⁻¹)) + (Real.rpow (((1 /. (x_1 ^ (2 : ℕ))) - (1 /. x_1)) + 1) (((2 : ℝ))⁻¹))))))))))))
  (h4 : Tendsto (fun x : ℝ => ((-(2 : ℝ)) /. ((Real.rpow (((1 /. (x ^ (2 : ℕ))) + (1 /. x)) + 1) (((2 : ℝ))⁻¹)) + (Real.rpow (((1 /. (x ^ (2 : ℕ))) - (1 /. x)) + 1) (((2 : ℝ))⁻¹))))) atBot (𝓝 (-(1 : ℝ))))
  : Tendsto (fun x : ℝ => ((Real.rpow ((1 + x) + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) - (Real.rpow ((1 - x) + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) atBot (𝓝 (-(1 : ℝ))) := by
  sorry

theorem proof_gap_exercise_594_5
  (h1 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((Real.rpow ((1 + x) + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) - (Real.rpow ((1 - x) + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) = ((2 * x) /. ((Real.rpow ((1 + x) + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) + (Real.rpow ((1 - x) + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))))
  (h3 : (forall (x : ℝ), (∃ L : ℝ, Tendsto (fun x_1 : ℝ => ((-(2 : ℝ)) /. ((Real.rpow (((1 /. (x_1 ^ (2 : ℕ))) + (1 /. x_1)) + 1) (((2 : ℝ))⁻¹)) + (Real.rpow (((1 /. (x_1 ^ (2 : ℕ))) - (1 /. x_1)) + 1) (((2 : ℝ))⁻¹))))) atBot (𝓝 L) ∧ ((((x ∈ (Set.univ : Set ℝ)) ∧ (x < 0)) ∧ (x = (-(Real.rpow (x ^ (2 : ℕ)) (((2 : ℝ))⁻¹))))) → (Tendsto (fun x_1 : ℝ => ((Real.rpow ((1 + x_1) + (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) - (Real.rpow ((1 - x_1) + (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) atBot (𝓝 (atBot.limUnder (fun x_1 : ℝ => ((-(2 : ℝ)) /. ((Real.rpow (((1 /. (x_1 ^ (2 : ℕ))) + (1 /. x_1)) + 1) (((2 : ℝ))⁻¹)) + (Real.rpow (((1 /. (x_1 ^ (2 : ℕ))) - (1 /. x_1)) + 1) (((2 : ℝ))⁻¹))))))))))))
  (h4 : Tendsto (fun x : ℝ => ((-(2 : ℝ)) /. ((Real.rpow (((1 /. (x ^ (2 : ℕ))) + (1 /. x)) + 1) (((2 : ℝ))⁻¹)) + (Real.rpow (((1 /. (x ^ (2 : ℕ))) - (1 /. x)) + 1) (((2 : ℝ))⁻¹))))) atBot (𝓝 (-(1 : ℝ))))
  (h5 : Tendsto (fun x : ℝ => ((Real.rpow ((1 + x) + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) - (Real.rpow ((1 - x) + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) atBot (𝓝 (-(1 : ℝ))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 0)) ∧ (x = (Real.rpow (x ^ (2 : ℕ)) (((2 : ℝ))⁻¹)))) → (∃ L : ℝ, Tendsto (fun x_1 : ℝ => (2 /. ((Real.rpow (((1 /. (x_1 ^ (2 : ℕ))) + (1 /. x_1)) + 1) (((2 : ℝ))⁻¹)) + (Real.rpow (((1 /. (x_1 ^ (2 : ℕ))) - (1 /. x_1)) + 1) (((2 : ℝ))⁻¹))))) atTop (𝓝 L) ∧ (Tendsto (fun x_1 : ℝ => ((Real.rpow ((1 + x_1) + (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) - (Real.rpow ((1 - x_1) + (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) atTop (𝓝 (atTop.limUnder (fun x_1 : ℝ => (2 /. ((Real.rpow (((1 /. (x_1 ^ (2 : ℕ))) + (1 /. x_1)) + 1) (((2 : ℝ))⁻¹)) + (Real.rpow (((1 /. (x_1 ^ (2 : ℕ))) - (1 /. x_1)) + 1) (((2 : ℝ))⁻¹))))))))))) := by
  sorry

theorem proof_gap_exercise_594_6
  (h1 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((Real.rpow ((1 + x) + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) - (Real.rpow ((1 - x) + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) = ((2 * x) /. ((Real.rpow ((1 + x) + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) + (Real.rpow ((1 - x) + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))))
  (h3 : (forall (x : ℝ), (∃ L : ℝ, Tendsto (fun x_1 : ℝ => ((-(2 : ℝ)) /. ((Real.rpow (((1 /. (x_1 ^ (2 : ℕ))) + (1 /. x_1)) + 1) (((2 : ℝ))⁻¹)) + (Real.rpow (((1 /. (x_1 ^ (2 : ℕ))) - (1 /. x_1)) + 1) (((2 : ℝ))⁻¹))))) atBot (𝓝 L) ∧ ((((x ∈ (Set.univ : Set ℝ)) ∧ (x < 0)) ∧ (x = (-(Real.rpow (x ^ (2 : ℕ)) (((2 : ℝ))⁻¹))))) → (Tendsto (fun x_1 : ℝ => ((Real.rpow ((1 + x_1) + (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) - (Real.rpow ((1 - x_1) + (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) atBot (𝓝 (atBot.limUnder (fun x_1 : ℝ => ((-(2 : ℝ)) /. ((Real.rpow (((1 /. (x_1 ^ (2 : ℕ))) + (1 /. x_1)) + 1) (((2 : ℝ))⁻¹)) + (Real.rpow (((1 /. (x_1 ^ (2 : ℕ))) - (1 /. x_1)) + 1) (((2 : ℝ))⁻¹))))))))))))
  (h4 : Tendsto (fun x : ℝ => ((-(2 : ℝ)) /. ((Real.rpow (((1 /. (x ^ (2 : ℕ))) + (1 /. x)) + 1) (((2 : ℝ))⁻¹)) + (Real.rpow (((1 /. (x ^ (2 : ℕ))) - (1 /. x)) + 1) (((2 : ℝ))⁻¹))))) atBot (𝓝 (-(1 : ℝ))))
  (h5 : Tendsto (fun x : ℝ => ((Real.rpow ((1 + x) + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) - (Real.rpow ((1 - x) + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) atBot (𝓝 (-(1 : ℝ))))
  (h6 : (forall (x : ℝ), (∃ L : ℝ, Tendsto (fun x_1 : ℝ => (2 /. ((Real.rpow (((1 /. (x_1 ^ (2 : ℕ))) + (1 /. x_1)) + 1) (((2 : ℝ))⁻¹)) + (Real.rpow (((1 /. (x_1 ^ (2 : ℕ))) - (1 /. x_1)) + 1) (((2 : ℝ))⁻¹))))) atTop (𝓝 L) ∧ ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 0)) ∧ (x = (Real.rpow (x ^ (2 : ℕ)) (((2 : ℝ))⁻¹)))) → (Tendsto (fun x_1 : ℝ => ((Real.rpow ((1 + x_1) + (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) - (Real.rpow ((1 - x_1) + (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) atTop (𝓝 (atTop.limUnder (fun x_1 : ℝ => (2 /. ((Real.rpow (((1 /. (x_1 ^ (2 : ℕ))) + (1 /. x_1)) + 1) (((2 : ℝ))⁻¹)) + (Real.rpow (((1 /. (x_1 ^ (2 : ℕ))) - (1 /. x_1)) + 1) (((2 : ℝ))⁻¹))))))))))))
  : Tendsto (fun x : ℝ => (2 /. ((Real.rpow (((1 /. (x ^ (2 : ℕ))) + (1 /. x)) + 1) (((2 : ℝ))⁻¹)) + (Real.rpow (((1 /. (x ^ (2 : ℕ))) - (1 /. x)) + 1) (((2 : ℝ))⁻¹))))) atTop (𝓝 1) := by
  sorry

theorem proof_gap_exercise_594_7
  (h1 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((Real.rpow ((1 + x) + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) - (Real.rpow ((1 - x) + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) = ((2 * x) /. ((Real.rpow ((1 + x) + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) + (Real.rpow ((1 - x) + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))))
  (h3 : (forall (x : ℝ), (∃ L : ℝ, Tendsto (fun x_1 : ℝ => ((-(2 : ℝ)) /. ((Real.rpow (((1 /. (x_1 ^ (2 : ℕ))) + (1 /. x_1)) + 1) (((2 : ℝ))⁻¹)) + (Real.rpow (((1 /. (x_1 ^ (2 : ℕ))) - (1 /. x_1)) + 1) (((2 : ℝ))⁻¹))))) atBot (𝓝 L) ∧ ((((x ∈ (Set.univ : Set ℝ)) ∧ (x < 0)) ∧ (x = (-(Real.rpow (x ^ (2 : ℕ)) (((2 : ℝ))⁻¹))))) → (Tendsto (fun x_1 : ℝ => ((Real.rpow ((1 + x_1) + (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) - (Real.rpow ((1 - x_1) + (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) atBot (𝓝 (atBot.limUnder (fun x_1 : ℝ => ((-(2 : ℝ)) /. ((Real.rpow (((1 /. (x_1 ^ (2 : ℕ))) + (1 /. x_1)) + 1) (((2 : ℝ))⁻¹)) + (Real.rpow (((1 /. (x_1 ^ (2 : ℕ))) - (1 /. x_1)) + 1) (((2 : ℝ))⁻¹))))))))))))
  (h4 : Tendsto (fun x : ℝ => ((-(2 : ℝ)) /. ((Real.rpow (((1 /. (x ^ (2 : ℕ))) + (1 /. x)) + 1) (((2 : ℝ))⁻¹)) + (Real.rpow (((1 /. (x ^ (2 : ℕ))) - (1 /. x)) + 1) (((2 : ℝ))⁻¹))))) atBot (𝓝 (-(1 : ℝ))))
  (h5 : Tendsto (fun x : ℝ => ((Real.rpow ((1 + x) + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) - (Real.rpow ((1 - x) + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) atBot (𝓝 (-(1 : ℝ))))
  (h6 : (forall (x : ℝ), (∃ L : ℝ, Tendsto (fun x_1 : ℝ => (2 /. ((Real.rpow (((1 /. (x_1 ^ (2 : ℕ))) + (1 /. x_1)) + 1) (((2 : ℝ))⁻¹)) + (Real.rpow (((1 /. (x_1 ^ (2 : ℕ))) - (1 /. x_1)) + 1) (((2 : ℝ))⁻¹))))) atTop (𝓝 L) ∧ ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 0)) ∧ (x = (Real.rpow (x ^ (2 : ℕ)) (((2 : ℝ))⁻¹)))) → (Tendsto (fun x_1 : ℝ => ((Real.rpow ((1 + x_1) + (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) - (Real.rpow ((1 - x_1) + (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) atTop (𝓝 (atTop.limUnder (fun x_1 : ℝ => (2 /. ((Real.rpow (((1 /. (x_1 ^ (2 : ℕ))) + (1 /. x_1)) + 1) (((2 : ℝ))⁻¹)) + (Real.rpow (((1 /. (x_1 ^ (2 : ℕ))) - (1 /. x_1)) + 1) (((2 : ℝ))⁻¹))))))))))))
  (h7 : Tendsto (fun x : ℝ => (2 /. ((Real.rpow (((1 /. (x ^ (2 : ℕ))) + (1 /. x)) + 1) (((2 : ℝ))⁻¹)) + (Real.rpow (((1 /. (x ^ (2 : ℕ))) - (1 /. x)) + 1) (((2 : ℝ))⁻¹))))) atTop (𝓝 1))
  : Tendsto (fun x : ℝ => ((Real.rpow ((1 + x) + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) - (Real.rpow ((1 - x) + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) atTop (𝓝 1) := by
  sorry

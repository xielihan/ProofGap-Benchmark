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

-- exercise: exercise_1328

theorem proof_gap_exercise_1328_1
  (a : ℝ)
  (b : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (b ∈ (Set.univ : Set ℝ)) ∧ (b > 0))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => (((((Real.rpow a (((2 : ℝ))⁻¹)) /. (1 + (x /. a))) * (1 /. ((2 * (Real.rpow a (((2 : ℝ))⁻¹))) * (Real.rpow x (((2 : ℝ))⁻¹))))) - (((Real.rpow b (((2 : ℝ))⁻¹)) /. (1 + (x /. b))) * (1 /. ((2 * (Real.rpow b (((2 : ℝ))⁻¹))) * (Real.rpow x (((2 : ℝ))⁻¹)))))) /. ((3 /. 2) * (Real.rpow x (((2 : ℝ))⁻¹))))) (𝓝[>] 0) (𝓝 L) ∧ (Tendsto (fun x : ℝ => ((1 /. (x * (Real.rpow x (((2 : ℝ))⁻¹)))) * (((Real.rpow a (((2 : ℝ))⁻¹)) * (Real.arctan (Real.rpow (x /. a) (((2 : ℝ))⁻¹)))) - ((Real.rpow b (((2 : ℝ))⁻¹)) * (Real.arctan (Real.rpow (x /. b) (((2 : ℝ))⁻¹))))))) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x : ℝ => (((((Real.rpow a (((2 : ℝ))⁻¹)) /. (1 + (x /. a))) * (1 /. ((2 * (Real.rpow a (((2 : ℝ))⁻¹))) * (Real.rpow x (((2 : ℝ))⁻¹))))) - (((Real.rpow b (((2 : ℝ))⁻¹)) /. (1 + (x /. b))) * (1 /. ((2 * (Real.rpow b (((2 : ℝ))⁻¹))) * (Real.rpow x (((2 : ℝ))⁻¹)))))) /. ((3 /. 2) * (Real.rpow x (((2 : ℝ))⁻¹))))))))) := by
  sorry

theorem proof_gap_exercise_1328_2
  (a : ℝ)
  (b : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (b ∈ (Set.univ : Set ℝ)) ∧ (b > 0))
  (h3 : Tendsto (fun x : ℝ => ((1 /. (x * (Real.rpow x (((2 : ℝ))⁻¹)))) * (((Real.rpow a (((2 : ℝ))⁻¹)) * (Real.arctan (Real.rpow (x /. a) (((2 : ℝ))⁻¹)))) - ((Real.rpow b (((2 : ℝ))⁻¹)) * (Real.arctan (Real.rpow (x /. b) (((2 : ℝ))⁻¹))))))) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x : ℝ => (((((Real.rpow a (((2 : ℝ))⁻¹)) /. (1 + (x /. a))) * (1 /. ((2 * (Real.rpow a (((2 : ℝ))⁻¹))) * (Real.rpow x (((2 : ℝ))⁻¹))))) - (((Real.rpow b (((2 : ℝ))⁻¹)) /. (1 + (x /. b))) * (1 /. ((2 * (Real.rpow b (((2 : ℝ))⁻¹))) * (Real.rpow x (((2 : ℝ))⁻¹)))))) /. ((3 /. 2) * (Real.rpow x (((2 : ℝ))⁻¹))))))))
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((((Real.rpow a (((2 : ℝ))⁻¹)) /. (1 + (x /. a))) * (1 /. ((2 * (Real.rpow a (((2 : ℝ))⁻¹))) * (Real.rpow x (((2 : ℝ))⁻¹))))) - (((Real.rpow b (((2 : ℝ))⁻¹)) /. (1 + (x /. b))) * (1 /. ((2 * (Real.rpow b (((2 : ℝ))⁻¹))) * (Real.rpow x (((2 : ℝ))⁻¹)))))) /. ((3 /. 2) * (Real.rpow x (((2 : ℝ))⁻¹))))) (𝓝[>] 0) (𝓝 L))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => (((a /. (x + a)) - (b /. (x + b))) /. (3 * x))) (𝓝[>] 0) (𝓝 L) ∧ (Tendsto (fun x : ℝ => (((((Real.rpow a (((2 : ℝ))⁻¹)) /. (1 + (x /. a))) * (1 /. ((2 * (Real.rpow a (((2 : ℝ))⁻¹))) * (Real.rpow x (((2 : ℝ))⁻¹))))) - (((Real.rpow b (((2 : ℝ))⁻¹)) /. (1 + (x /. b))) * (1 /. ((2 * (Real.rpow b (((2 : ℝ))⁻¹))) * (Real.rpow x (((2 : ℝ))⁻¹)))))) /. ((3 /. 2) * (Real.rpow x (((2 : ℝ))⁻¹))))) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x : ℝ => (((a /. (x + a)) - (b /. (x + b))) /. (3 * x))))))) := by
  sorry

theorem proof_gap_exercise_1328_3
  (a : ℝ)
  (b : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (b ∈ (Set.univ : Set ℝ)) ∧ (b > 0))
  (h3 : Tendsto (fun x : ℝ => ((1 /. (x * (Real.rpow x (((2 : ℝ))⁻¹)))) * (((Real.rpow a (((2 : ℝ))⁻¹)) * (Real.arctan (Real.rpow (x /. a) (((2 : ℝ))⁻¹)))) - ((Real.rpow b (((2 : ℝ))⁻¹)) * (Real.arctan (Real.rpow (x /. b) (((2 : ℝ))⁻¹))))))) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x : ℝ => (((((Real.rpow a (((2 : ℝ))⁻¹)) /. (1 + (x /. a))) * (1 /. ((2 * (Real.rpow a (((2 : ℝ))⁻¹))) * (Real.rpow x (((2 : ℝ))⁻¹))))) - (((Real.rpow b (((2 : ℝ))⁻¹)) /. (1 + (x /. b))) * (1 /. ((2 * (Real.rpow b (((2 : ℝ))⁻¹))) * (Real.rpow x (((2 : ℝ))⁻¹)))))) /. ((3 /. 2) * (Real.rpow x (((2 : ℝ))⁻¹))))))))
  (h4 : Tendsto (fun x : ℝ => (((((Real.rpow a (((2 : ℝ))⁻¹)) /. (1 + (x /. a))) * (1 /. ((2 * (Real.rpow a (((2 : ℝ))⁻¹))) * (Real.rpow x (((2 : ℝ))⁻¹))))) - (((Real.rpow b (((2 : ℝ))⁻¹)) /. (1 + (x /. b))) * (1 /. ((2 * (Real.rpow b (((2 : ℝ))⁻¹))) * (Real.rpow x (((2 : ℝ))⁻¹)))))) /. ((3 /. 2) * (Real.rpow x (((2 : ℝ))⁻¹))))) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x : ℝ => (((a /. (x + a)) - (b /. (x + b))) /. (3 * x))))))
  (h5 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((((Real.rpow a (((2 : ℝ))⁻¹)) /. (1 + (x /. a))) * (1 /. ((2 * (Real.rpow a (((2 : ℝ))⁻¹))) * (Real.rpow x (((2 : ℝ))⁻¹))))) - (((Real.rpow b (((2 : ℝ))⁻¹)) /. (1 + (x /. b))) * (1 /. ((2 * (Real.rpow b (((2 : ℝ))⁻¹))) * (Real.rpow x (((2 : ℝ))⁻¹)))))) /. ((3 /. 2) * (Real.rpow x (((2 : ℝ))⁻¹))))) (𝓝[>] 0) (𝓝 L))
  (h6 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((a /. (x + a)) - (b /. (x + b))) /. (3 * x))) (𝓝[>] 0) (𝓝 L))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => (((-(a /. ((x + a) ^ (2 : ℕ)))) + (b /. ((x + b) ^ (2 : ℕ)))) /. 3)) (𝓝[>] 0) (𝓝 L) ∧ (Tendsto (fun x : ℝ => (((a /. (x + a)) - (b /. (x + b))) /. (3 * x))) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x : ℝ => (((-(a /. ((x + a) ^ (2 : ℕ)))) + (b /. ((x + b) ^ (2 : ℕ)))) /. 3)))))) := by
  sorry

theorem proof_gap_exercise_1328_4
  (a : ℝ)
  (b : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (b ∈ (Set.univ : Set ℝ)) ∧ (b > 0))
  (h3 : Tendsto (fun x : ℝ => ((1 /. (x * (Real.rpow x (((2 : ℝ))⁻¹)))) * (((Real.rpow a (((2 : ℝ))⁻¹)) * (Real.arctan (Real.rpow (x /. a) (((2 : ℝ))⁻¹)))) - ((Real.rpow b (((2 : ℝ))⁻¹)) * (Real.arctan (Real.rpow (x /. b) (((2 : ℝ))⁻¹))))))) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x : ℝ => (((((Real.rpow a (((2 : ℝ))⁻¹)) /. (1 + (x /. a))) * (1 /. ((2 * (Real.rpow a (((2 : ℝ))⁻¹))) * (Real.rpow x (((2 : ℝ))⁻¹))))) - (((Real.rpow b (((2 : ℝ))⁻¹)) /. (1 + (x /. b))) * (1 /. ((2 * (Real.rpow b (((2 : ℝ))⁻¹))) * (Real.rpow x (((2 : ℝ))⁻¹)))))) /. ((3 /. 2) * (Real.rpow x (((2 : ℝ))⁻¹))))))))
  (h4 : Tendsto (fun x : ℝ => (((((Real.rpow a (((2 : ℝ))⁻¹)) /. (1 + (x /. a))) * (1 /. ((2 * (Real.rpow a (((2 : ℝ))⁻¹))) * (Real.rpow x (((2 : ℝ))⁻¹))))) - (((Real.rpow b (((2 : ℝ))⁻¹)) /. (1 + (x /. b))) * (1 /. ((2 * (Real.rpow b (((2 : ℝ))⁻¹))) * (Real.rpow x (((2 : ℝ))⁻¹)))))) /. ((3 /. 2) * (Real.rpow x (((2 : ℝ))⁻¹))))) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x : ℝ => (((a /. (x + a)) - (b /. (x + b))) /. (3 * x))))))
  (h5 : Tendsto (fun x : ℝ => (((a /. (x + a)) - (b /. (x + b))) /. (3 * x))) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x : ℝ => (((-(a /. ((x + a) ^ (2 : ℕ)))) + (b /. ((x + b) ^ (2 : ℕ)))) /. 3)))))
  (h6 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((((Real.rpow a (((2 : ℝ))⁻¹)) /. (1 + (x /. a))) * (1 /. ((2 * (Real.rpow a (((2 : ℝ))⁻¹))) * (Real.rpow x (((2 : ℝ))⁻¹))))) - (((Real.rpow b (((2 : ℝ))⁻¹)) /. (1 + (x /. b))) * (1 /. ((2 * (Real.rpow b (((2 : ℝ))⁻¹))) * (Real.rpow x (((2 : ℝ))⁻¹)))))) /. ((3 /. 2) * (Real.rpow x (((2 : ℝ))⁻¹))))) (𝓝[>] 0) (𝓝 L))
  (h7 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((a /. (x + a)) - (b /. (x + b))) /. (3 * x))) (𝓝[>] 0) (𝓝 L))
  (h8 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((-(a /. ((x + a) ^ (2 : ℕ)))) + (b /. ((x + b) ^ (2 : ℕ)))) /. 3)) (𝓝[>] 0) (𝓝 L))
  : Tendsto (fun x : ℝ => (((-(a /. ((x + a) ^ (2 : ℕ)))) + (b /. ((x + b) ^ (2 : ℕ)))) /. 3)) (𝓝[>] 0) (𝓝 ((a - b) /. ((3 * a) * b))) := by
  sorry

theorem proof_gap_exercise_1328_5
  (a : ℝ)
  (b : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (b ∈ (Set.univ : Set ℝ)) ∧ (b > 0))
  (h3 : Tendsto (fun x : ℝ => ((1 /. (x * (Real.rpow x (((2 : ℝ))⁻¹)))) * (((Real.rpow a (((2 : ℝ))⁻¹)) * (Real.arctan (Real.rpow (x /. a) (((2 : ℝ))⁻¹)))) - ((Real.rpow b (((2 : ℝ))⁻¹)) * (Real.arctan (Real.rpow (x /. b) (((2 : ℝ))⁻¹))))))) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x : ℝ => (((((Real.rpow a (((2 : ℝ))⁻¹)) /. (1 + (x /. a))) * (1 /. ((2 * (Real.rpow a (((2 : ℝ))⁻¹))) * (Real.rpow x (((2 : ℝ))⁻¹))))) - (((Real.rpow b (((2 : ℝ))⁻¹)) /. (1 + (x /. b))) * (1 /. ((2 * (Real.rpow b (((2 : ℝ))⁻¹))) * (Real.rpow x (((2 : ℝ))⁻¹)))))) /. ((3 /. 2) * (Real.rpow x (((2 : ℝ))⁻¹))))))))
  (h4 : Tendsto (fun x : ℝ => (((((Real.rpow a (((2 : ℝ))⁻¹)) /. (1 + (x /. a))) * (1 /. ((2 * (Real.rpow a (((2 : ℝ))⁻¹))) * (Real.rpow x (((2 : ℝ))⁻¹))))) - (((Real.rpow b (((2 : ℝ))⁻¹)) /. (1 + (x /. b))) * (1 /. ((2 * (Real.rpow b (((2 : ℝ))⁻¹))) * (Real.rpow x (((2 : ℝ))⁻¹)))))) /. ((3 /. 2) * (Real.rpow x (((2 : ℝ))⁻¹))))) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x : ℝ => (((a /. (x + a)) - (b /. (x + b))) /. (3 * x))))))
  (h5 : Tendsto (fun x : ℝ => (((a /. (x + a)) - (b /. (x + b))) /. (3 * x))) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x : ℝ => (((-(a /. ((x + a) ^ (2 : ℕ)))) + (b /. ((x + b) ^ (2 : ℕ)))) /. 3)))))
  (h6 : Tendsto (fun x : ℝ => (((-(a /. ((x + a) ^ (2 : ℕ)))) + (b /. ((x + b) ^ (2 : ℕ)))) /. 3)) (𝓝[>] 0) (𝓝 ((a - b) /. ((3 * a) * b))))
  (h7 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((((Real.rpow a (((2 : ℝ))⁻¹)) /. (1 + (x /. a))) * (1 /. ((2 * (Real.rpow a (((2 : ℝ))⁻¹))) * (Real.rpow x (((2 : ℝ))⁻¹))))) - (((Real.rpow b (((2 : ℝ))⁻¹)) /. (1 + (x /. b))) * (1 /. ((2 * (Real.rpow b (((2 : ℝ))⁻¹))) * (Real.rpow x (((2 : ℝ))⁻¹)))))) /. ((3 /. 2) * (Real.rpow x (((2 : ℝ))⁻¹))))) (𝓝[>] 0) (𝓝 L))
  (h8 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((a /. (x + a)) - (b /. (x + b))) /. (3 * x))) (𝓝[>] 0) (𝓝 L))
  (h9 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((-(a /. ((x + a) ^ (2 : ℕ)))) + (b /. ((x + b) ^ (2 : ℕ)))) /. 3)) (𝓝[>] 0) (𝓝 L))
  : Tendsto (fun x : ℝ => ((1 /. (x * (Real.rpow x (((2 : ℝ))⁻¹)))) * (((Real.rpow a (((2 : ℝ))⁻¹)) * (Real.arctan (Real.rpow (x /. a) (((2 : ℝ))⁻¹)))) - ((Real.rpow b (((2 : ℝ))⁻¹)) * (Real.arctan (Real.rpow (x /. b) (((2 : ℝ))⁻¹))))))) (𝓝[>] 0) (𝓝 ((a - b) /. ((3 * a) * b))) := by
  sorry

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

-- exercise: exercise_451

theorem proof_gap_exercise_451_1
  (h1 : A = (Real.rpow (1 + (5 * x)) (((5 : ℝ))⁻¹)))
  (h2 : B = (1 + x))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => (((x ^ (2 : ℕ)) * (((((A ^ (4 : ℕ)) + ((A ^ (3 : ℕ)) * B)) + ((A ^ (2 : ℕ)) * (B ^ (2 : ℕ)))) + (A * (B ^ (3 : ℕ)))) + (B ^ (4 : ℕ)))) /. ((A ^ (5 : ℕ)) - (B ^ (5 : ℕ))))) (𝓝[≠] 0) (𝓝 L) ∧ (Tendsto (fun x : ℝ => ((x ^ (2 : ℕ)) /. (A - B))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (((x ^ (2 : ℕ)) * (((((A ^ (4 : ℕ)) + ((A ^ (3 : ℕ)) * B)) + ((A ^ (2 : ℕ)) * (B ^ (2 : ℕ)))) + (A * (B ^ (3 : ℕ)))) + (B ^ (4 : ℕ)))) /. ((A ^ (5 : ℕ)) - (B ^ (5 : ℕ))))))))) := by
  sorry

theorem proof_gap_exercise_451_2
  (h1 : A = (Real.rpow (1 + (5 * x)) (((5 : ℝ))⁻¹)))
  (h2 : B = (1 + x))
  (h3 : Tendsto (fun x : ℝ => ((x ^ (2 : ℕ)) /. (A - B))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (((x ^ (2 : ℕ)) * (((((A ^ (4 : ℕ)) + ((A ^ (3 : ℕ)) * B)) + ((A ^ (2 : ℕ)) * (B ^ (2 : ℕ)))) + (A * (B ^ (3 : ℕ)))) + (B ^ (4 : ℕ)))) /. ((A ^ (5 : ℕ)) - (B ^ (5 : ℕ))))))))
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((x ^ (2 : ℕ)) * (((((A ^ (4 : ℕ)) + ((A ^ (3 : ℕ)) * B)) + ((A ^ (2 : ℕ)) * (B ^ (2 : ℕ)))) + (A * (B ^ (3 : ℕ)))) + (B ^ (4 : ℕ)))) /. ((A ^ (5 : ℕ)) - (B ^ (5 : ℕ))))) (𝓝[≠] 0) (𝓝 L))
  : ((A ^ (5 : ℕ)) - (B ^ (5 : ℕ))) = ((1 + (5 * x)) - ((1 + x) ^ (5 : ℕ))) := by
  sorry

theorem proof_gap_exercise_451_3
  (h1 : A = (Real.rpow (1 + (5 * x)) (((5 : ℝ))⁻¹)))
  (h2 : B = (1 + x))
  (h3 : Tendsto (fun x : ℝ => ((x ^ (2 : ℕ)) /. (A - B))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (((x ^ (2 : ℕ)) * (((((A ^ (4 : ℕ)) + ((A ^ (3 : ℕ)) * B)) + ((A ^ (2 : ℕ)) * (B ^ (2 : ℕ)))) + (A * (B ^ (3 : ℕ)))) + (B ^ (4 : ℕ)))) /. ((A ^ (5 : ℕ)) - (B ^ (5 : ℕ))))))))
  (h4 : ((A ^ (5 : ℕ)) - (B ^ (5 : ℕ))) = ((1 + (5 * x)) - ((1 + x) ^ (5 : ℕ))))
  (h5 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((x ^ (2 : ℕ)) * (((((A ^ (4 : ℕ)) + ((A ^ (3 : ℕ)) * B)) + ((A ^ (2 : ℕ)) * (B ^ (2 : ℕ)))) + (A * (B ^ (3 : ℕ)))) + (B ^ (4 : ℕ)))) /. ((A ^ (5 : ℕ)) - (B ^ (5 : ℕ))))) (𝓝[≠] 0) (𝓝 L))
  : ((1 + (5 * x)) - ((1 + x) ^ (5 : ℕ))) = ((x ^ (2 : ℕ)) * ((((-(10 : ℝ)) - (10 * x)) - (5 * (x ^ (2 : ℕ)))) - (x ^ (3 : ℕ)))) := by
  sorry

theorem proof_gap_exercise_451_4
  (h1 : A = (Real.rpow (1 + (5 * x)) (((5 : ℝ))⁻¹)))
  (h2 : B = (1 + x))
  (h3 : Tendsto (fun x : ℝ => ((x ^ (2 : ℕ)) /. (A - B))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (((x ^ (2 : ℕ)) * (((((A ^ (4 : ℕ)) + ((A ^ (3 : ℕ)) * B)) + ((A ^ (2 : ℕ)) * (B ^ (2 : ℕ)))) + (A * (B ^ (3 : ℕ)))) + (B ^ (4 : ℕ)))) /. ((A ^ (5 : ℕ)) - (B ^ (5 : ℕ))))))))
  (h4 : ((A ^ (5 : ℕ)) - (B ^ (5 : ℕ))) = ((1 + (5 * x)) - ((1 + x) ^ (5 : ℕ))))
  (h5 : ((1 + (5 * x)) - ((1 + x) ^ (5 : ℕ))) = ((x ^ (2 : ℕ)) * ((((-(10 : ℝ)) - (10 * x)) - (5 * (x ^ (2 : ℕ)))) - (x ^ (3 : ℕ)))))
  (h6 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((x ^ (2 : ℕ)) * (((((A ^ (4 : ℕ)) + ((A ^ (3 : ℕ)) * B)) + ((A ^ (2 : ℕ)) * (B ^ (2 : ℕ)))) + (A * (B ^ (3 : ℕ)))) + (B ^ (4 : ℕ)))) /. ((A ^ (5 : ℕ)) - (B ^ (5 : ℕ))))) (𝓝[≠] 0) (𝓝 L))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => ((((((Real.rpow ((1 + (5 * x)) ^ (4 : ℕ)) (((5 : ℝ))⁻¹)) + ((Real.rpow ((1 + (5 * x)) ^ (3 : ℕ)) (((5 : ℝ))⁻¹)) * (1 + x))) + ((Real.rpow ((1 + (5 * x)) ^ (2 : ℕ)) (((5 : ℝ))⁻¹)) * ((1 + x) ^ (2 : ℕ)))) + ((Real.rpow (1 + (5 * x)) (((5 : ℝ))⁻¹)) * ((1 + x) ^ (3 : ℕ)))) + ((1 + x) ^ (4 : ℕ))) /. ((((-(10 : ℝ)) - (10 * x)) - (5 * (x ^ (2 : ℕ)))) - (x ^ (3 : ℕ))))) (𝓝[≠] 0) (𝓝 L) ∧ (Tendsto (fun x : ℝ => ((x ^ (2 : ℕ)) /. ((Real.rpow (1 + (5 * x)) (((5 : ℝ))⁻¹)) - (1 + x)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((((Real.rpow ((1 + (5 * x)) ^ (4 : ℕ)) (((5 : ℝ))⁻¹)) + ((Real.rpow ((1 + (5 * x)) ^ (3 : ℕ)) (((5 : ℝ))⁻¹)) * (1 + x))) + ((Real.rpow ((1 + (5 * x)) ^ (2 : ℕ)) (((5 : ℝ))⁻¹)) * ((1 + x) ^ (2 : ℕ)))) + ((Real.rpow (1 + (5 * x)) (((5 : ℝ))⁻¹)) * ((1 + x) ^ (3 : ℕ)))) + ((1 + x) ^ (4 : ℕ))) /. ((((-(10 : ℝ)) - (10 * x)) - (5 * (x ^ (2 : ℕ)))) - (x ^ (3 : ℕ))))))))) := by
  sorry

theorem proof_gap_exercise_451_5
  (h1 : A = (Real.rpow (1 + (5 * x)) (((5 : ℝ))⁻¹)))
  (h2 : B = (1 + x))
  (h3 : Tendsto (fun x : ℝ => ((x ^ (2 : ℕ)) /. (A - B))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (((x ^ (2 : ℕ)) * (((((A ^ (4 : ℕ)) + ((A ^ (3 : ℕ)) * B)) + ((A ^ (2 : ℕ)) * (B ^ (2 : ℕ)))) + (A * (B ^ (3 : ℕ)))) + (B ^ (4 : ℕ)))) /. ((A ^ (5 : ℕ)) - (B ^ (5 : ℕ))))))))
  (h4 : ((A ^ (5 : ℕ)) - (B ^ (5 : ℕ))) = ((1 + (5 * x)) - ((1 + x) ^ (5 : ℕ))))
  (h5 : ((1 + (5 * x)) - ((1 + x) ^ (5 : ℕ))) = ((x ^ (2 : ℕ)) * ((((-(10 : ℝ)) - (10 * x)) - (5 * (x ^ (2 : ℕ)))) - (x ^ (3 : ℕ)))))
  (h6 : Tendsto (fun x : ℝ => ((x ^ (2 : ℕ)) /. ((Real.rpow (1 + (5 * x)) (((5 : ℝ))⁻¹)) - (1 + x)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((((Real.rpow ((1 + (5 * x)) ^ (4 : ℕ)) (((5 : ℝ))⁻¹)) + ((Real.rpow ((1 + (5 * x)) ^ (3 : ℕ)) (((5 : ℝ))⁻¹)) * (1 + x))) + ((Real.rpow ((1 + (5 * x)) ^ (2 : ℕ)) (((5 : ℝ))⁻¹)) * ((1 + x) ^ (2 : ℕ)))) + ((Real.rpow (1 + (5 * x)) (((5 : ℝ))⁻¹)) * ((1 + x) ^ (3 : ℕ)))) + ((1 + x) ^ (4 : ℕ))) /. ((((-(10 : ℝ)) - (10 * x)) - (5 * (x ^ (2 : ℕ)))) - (x ^ (3 : ℕ))))))))
  (h7 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((x ^ (2 : ℕ)) * (((((A ^ (4 : ℕ)) + ((A ^ (3 : ℕ)) * B)) + ((A ^ (2 : ℕ)) * (B ^ (2 : ℕ)))) + (A * (B ^ (3 : ℕ)))) + (B ^ (4 : ℕ)))) /. ((A ^ (5 : ℕ)) - (B ^ (5 : ℕ))))) (𝓝[≠] 0) (𝓝 L))
  (h8 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((((((Real.rpow ((1 + (5 * x)) ^ (4 : ℕ)) (((5 : ℝ))⁻¹)) + ((Real.rpow ((1 + (5 * x)) ^ (3 : ℕ)) (((5 : ℝ))⁻¹)) * (1 + x))) + ((Real.rpow ((1 + (5 * x)) ^ (2 : ℕ)) (((5 : ℝ))⁻¹)) * ((1 + x) ^ (2 : ℕ)))) + ((Real.rpow (1 + (5 * x)) (((5 : ℝ))⁻¹)) * ((1 + x) ^ (3 : ℕ)))) + ((1 + x) ^ (4 : ℕ))) /. ((((-(10 : ℝ)) - (10 * x)) - (5 * (x ^ (2 : ℕ)))) - (x ^ (3 : ℕ))))) (𝓝[≠] 0) (𝓝 L))
  : Tendsto (fun x : ℝ => ((x ^ (2 : ℕ)) /. ((Real.rpow (1 + (5 * x)) (((5 : ℝ))⁻¹)) - (1 + x)))) (𝓝[≠] 0) (𝓝 (-(1 /. 2))) := by
  sorry

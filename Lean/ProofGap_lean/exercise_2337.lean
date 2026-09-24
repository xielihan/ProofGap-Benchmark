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

-- exercise: exercise_2337

theorem proof_gap_exercise_2337_1
  : (∃ L : ℝ, Tendsto (fun v_uCE_uB5 : ℝ => (∫ x in ((-(1 : ℝ)) + v_uCE_uB5)..(0 : ℝ), (((1 : ℝ) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ)))) (𝓝[>] 0) (𝓝 L) ∧ ∃ L : ℝ, Tendsto (fun v_uCE_uB5_' : ℝ => (∫ x in (0 : ℝ)..(1 - v_uCE_uB5_'), (((1 : ℝ) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ)))) (𝓝[>] 0) (𝓝 L) ∧ ∃ L : ℝ, Tendsto (fun v_uCE_uB5 : ℝ => (-(Real.arcsin ((-(1 : ℝ)) + v_uCE_uB5)))) (𝓝[>] 0) (𝓝 L) ∧ ∃ L : ℝ, Tendsto (fun v_uCE_uB5_' : ℝ => (Real.arcsin (1 - v_uCE_uB5_'))) (𝓝[>] 0) (𝓝 L) ∧ (((𝓝[>] 0).limUnder (fun v_uCE_uB5 : ℝ => (∫ x in ((-(1 : ℝ)) + v_uCE_uB5)..(0 : ℝ), (((1 : ℝ) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ)))) + (𝓝[>] 0).limUnder (fun v_uCE_uB5_' : ℝ => (∫ x in (0 : ℝ)..(1 - v_uCE_uB5_'), (((1 : ℝ) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))))) = ((𝓝[>] 0).limUnder (fun v_uCE_uB5 : ℝ => (-(Real.arcsin ((-(1 : ℝ)) + v_uCE_uB5)))) + (𝓝[>] 0).limUnder (fun v_uCE_uB5_' : ℝ => (Real.arcsin (1 - v_uCE_uB5_')))))) := by
  sorry

theorem proof_gap_exercise_2337_2
  (h1 : ((𝓝[>] 0).limUnder (fun v_uCE_uB5 : ℝ => (∫ x in ((-(1 : ℝ)) + v_uCE_uB5)..(0 : ℝ), (((1 : ℝ) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ)))) + (𝓝[>] 0).limUnder (fun v_uCE_uB5_' : ℝ => (∫ x in (0 : ℝ)..(1 - v_uCE_uB5_'), (((1 : ℝ) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))))) = ((𝓝[>] 0).limUnder (fun v_uCE_uB5 : ℝ => (-(Real.arcsin ((-(1 : ℝ)) + v_uCE_uB5)))) + (𝓝[>] 0).limUnder (fun v_uCE_uB5_' : ℝ => (Real.arcsin (1 - v_uCE_uB5_')))))
  (h2 : ∃ L : ℝ, Tendsto (fun v_uCE_uB5 : ℝ => (∫ x in ((-(1 : ℝ)) + v_uCE_uB5)..(0 : ℝ), (((1 : ℝ) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ)))) (𝓝[>] 0) (𝓝 L))
  (h3 : ∃ L : ℝ, Tendsto (fun v_uCE_uB5_' : ℝ => (∫ x in (0 : ℝ)..(1 - v_uCE_uB5_'), (((1 : ℝ) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ)))) (𝓝[>] 0) (𝓝 L))
  (h4 : ∃ L : ℝ, Tendsto (fun v_uCE_uB5 : ℝ => (-(Real.arcsin ((-(1 : ℝ)) + v_uCE_uB5)))) (𝓝[>] 0) (𝓝 L))
  (h5 : ∃ L : ℝ, Tendsto (fun v_uCE_uB5_' : ℝ => (Real.arcsin (1 - v_uCE_uB5_'))) (𝓝[>] 0) (𝓝 L))
  : ((𝓝[>] 0).limUnder (fun v_uCE_uB5 : ℝ => (-(Real.arcsin ((-(1 : ℝ)) + v_uCE_uB5)))) + (𝓝[>] 0).limUnder (fun v_uCE_uB5_' : ℝ => (Real.arcsin (1 - v_uCE_uB5_')))) = Real.pi := by
  sorry

theorem proof_gap_exercise_2337_3
  (h1 : ((𝓝[>] 0).limUnder (fun v_uCE_uB5 : ℝ => (∫ x in ((-(1 : ℝ)) + v_uCE_uB5)..(0 : ℝ), (((1 : ℝ) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ)))) + (𝓝[>] 0).limUnder (fun v_uCE_uB5_' : ℝ => (∫ x in (0 : ℝ)..(1 - v_uCE_uB5_'), (((1 : ℝ) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))))) = ((𝓝[>] 0).limUnder (fun v_uCE_uB5 : ℝ => (-(Real.arcsin ((-(1 : ℝ)) + v_uCE_uB5)))) + (𝓝[>] 0).limUnder (fun v_uCE_uB5_' : ℝ => (Real.arcsin (1 - v_uCE_uB5_')))))
  (h2 : ((𝓝[>] 0).limUnder (fun v_uCE_uB5 : ℝ => (-(Real.arcsin ((-(1 : ℝ)) + v_uCE_uB5)))) + (𝓝[>] 0).limUnder (fun v_uCE_uB5_' : ℝ => (Real.arcsin (1 - v_uCE_uB5_')))) = Real.pi)
  (h3 : ∃ L : ℝ, Tendsto (fun v_uCE_uB5 : ℝ => (∫ x in ((-(1 : ℝ)) + v_uCE_uB5)..(0 : ℝ), (((1 : ℝ) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ)))) (𝓝[>] 0) (𝓝 L))
  (h4 : ∃ L : ℝ, Tendsto (fun v_uCE_uB5_' : ℝ => (∫ x in (0 : ℝ)..(1 - v_uCE_uB5_'), (((1 : ℝ) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ)))) (𝓝[>] 0) (𝓝 L))
  (h5 : ∃ L : ℝ, Tendsto (fun v_uCE_uB5 : ℝ => (-(Real.arcsin ((-(1 : ℝ)) + v_uCE_uB5)))) (𝓝[>] 0) (𝓝 L))
  (h6 : ∃ L : ℝ, Tendsto (fun v_uCE_uB5_' : ℝ => (Real.arcsin (1 - v_uCE_uB5_'))) (𝓝[>] 0) (𝓝 L))
  : ((𝓝[>] 0).limUnder (fun v_uCE_uB5 : ℝ => (∫ x in ((-(1 : ℝ)) + v_uCE_uB5)..(0 : ℝ), (((1 : ℝ) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ)))) + (𝓝[>] 0).limUnder (fun v_uCE_uB5_' : ℝ => (∫ x in (0 : ℝ)..(1 - v_uCE_uB5_'), (((1 : ℝ) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))))) = Real.pi := by
  sorry

theorem proof_gap_exercise_2337_4
  (h1 : ((𝓝[>] 0).limUnder (fun v_uCE_uB5 : ℝ => (∫ x in ((-(1 : ℝ)) + v_uCE_uB5)..(0 : ℝ), (((1 : ℝ) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ)))) + (𝓝[>] 0).limUnder (fun v_uCE_uB5_' : ℝ => (∫ x in (0 : ℝ)..(1 - v_uCE_uB5_'), (((1 : ℝ) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))))) = ((𝓝[>] 0).limUnder (fun v_uCE_uB5 : ℝ => (-(Real.arcsin ((-(1 : ℝ)) + v_uCE_uB5)))) + (𝓝[>] 0).limUnder (fun v_uCE_uB5_' : ℝ => (Real.arcsin (1 - v_uCE_uB5_')))))
  (h2 : ((𝓝[>] 0).limUnder (fun v_uCE_uB5 : ℝ => (-(Real.arcsin ((-(1 : ℝ)) + v_uCE_uB5)))) + (𝓝[>] 0).limUnder (fun v_uCE_uB5_' : ℝ => (Real.arcsin (1 - v_uCE_uB5_')))) = Real.pi)
  (h3 : ((𝓝[>] 0).limUnder (fun v_uCE_uB5 : ℝ => (∫ x in ((-(1 : ℝ)) + v_uCE_uB5)..(0 : ℝ), (((1 : ℝ) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ)))) + (𝓝[>] 0).limUnder (fun v_uCE_uB5_' : ℝ => (∫ x in (0 : ℝ)..(1 - v_uCE_uB5_'), (((1 : ℝ) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))))) = Real.pi)
  (h4 : ∃ L : ℝ, Tendsto (fun v_uCE_uB5 : ℝ => (∫ x in ((-(1 : ℝ)) + v_uCE_uB5)..(0 : ℝ), (((1 : ℝ) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ)))) (𝓝[>] 0) (𝓝 L))
  (h5 : ∃ L : ℝ, Tendsto (fun v_uCE_uB5_' : ℝ => (∫ x in (0 : ℝ)..(1 - v_uCE_uB5_'), (((1 : ℝ) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ)))) (𝓝[>] 0) (𝓝 L))
  (h6 : ∃ L : ℝ, Tendsto (fun v_uCE_uB5 : ℝ => (-(Real.arcsin ((-(1 : ℝ)) + v_uCE_uB5)))) (𝓝[>] 0) (𝓝 L))
  (h7 : ∃ L : ℝ, Tendsto (fun v_uCE_uB5_' : ℝ => (Real.arcsin (1 - v_uCE_uB5_'))) (𝓝[>] 0) (𝓝 L))
  : (∫ x in (-(1 : ℝ))..(1 : ℝ), (((1 : ℝ) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = Real.pi := by
  sorry

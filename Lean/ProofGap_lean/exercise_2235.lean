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

-- exercise: exercise_2235

theorem proof_gap_exercise_2235_1
  (h1 : (exists (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < (Real.pi /. 2)))))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => (((Real.rpow (Real.tan (Real.sin x)) (((2 : ℝ))⁻¹)) * (iteratedDeriv 1 (fun t_1 => (Real.sin t_1)) x)) /. ((Real.rpow (Real.sin (Real.tan x)) (((2 : ℝ))⁻¹)) * (iteratedDeriv 1 (fun t_1 => (Real.tan t_1)) x)))) (𝓝[>] 0) (𝓝 L) ∧ (Tendsto (fun x : ℝ => ((∫ t in (0 : ℝ)..(Real.sin x), ((Real.rpow (Real.tan t) (((2 : ℝ))⁻¹)) * (1 : ℝ))) /. (∫ t in (0 : ℝ)..(Real.tan x), ((Real.rpow (Real.sin t) (((2 : ℝ))⁻¹)) * (1 : ℝ))))) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x : ℝ => (((Real.rpow (Real.tan (Real.sin x)) (((2 : ℝ))⁻¹)) * (iteratedDeriv 1 (fun t_1 => (Real.sin t_1)) x)) /. ((Real.rpow (Real.sin (Real.tan x)) (((2 : ℝ))⁻¹)) * (iteratedDeriv 1 (fun t_1 => (Real.tan t_1)) x)))))))) := by
  sorry

theorem proof_gap_exercise_2235_2
  (h1 : (exists (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < (Real.pi /. 2)))))
  (h2 : Tendsto (fun x : ℝ => ((∫ t in (0 : ℝ)..(Real.sin x), ((Real.rpow (Real.tan t) (((2 : ℝ))⁻¹)) * (1 : ℝ))) /. (∫ t in (0 : ℝ)..(Real.tan x), ((Real.rpow (Real.sin t) (((2 : ℝ))⁻¹)) * (1 : ℝ))))) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x : ℝ => (((Real.rpow (Real.tan (Real.sin x)) (((2 : ℝ))⁻¹)) * (iteratedDeriv 1 (fun t_1 => (Real.sin t_1)) x)) /. ((Real.rpow (Real.sin (Real.tan x)) (((2 : ℝ))⁻¹)) * (iteratedDeriv 1 (fun t_1 => (Real.tan t_1)) x)))))))
  (h3 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((Real.rpow (Real.tan (Real.sin x)) (((2 : ℝ))⁻¹)) * (iteratedDeriv 1 (fun t_1 => (Real.sin t_1)) x)) /. ((Real.rpow (Real.sin (Real.tan x)) (((2 : ℝ))⁻¹)) * (iteratedDeriv 1 (fun t_1 => (Real.tan t_1)) x)))) (𝓝[>] 0) (𝓝 L))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => ((Real.rpow ((((Real.tan (Real.sin x)) /. (Real.sin x)) * ((Real.sin x) /. (Real.tan x))) * ((Real.tan x) /. (Real.sin (Real.tan x)))) (((2 : ℝ))⁻¹)) * ((Real.cos x) ^ (3 : ℕ)))) (𝓝[>] 0) (𝓝 L) ∧ (Tendsto (fun x : ℝ => (((Real.rpow (Real.tan (Real.sin x)) (((2 : ℝ))⁻¹)) * (iteratedDeriv 1 (fun t_1 => (Real.sin t_1)) x)) /. ((Real.rpow (Real.sin (Real.tan x)) (((2 : ℝ))⁻¹)) * (iteratedDeriv 1 (fun t_1 => (Real.tan t_1)) x)))) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x : ℝ => ((Real.rpow ((((Real.tan (Real.sin x)) /. (Real.sin x)) * ((Real.sin x) /. (Real.tan x))) * ((Real.tan x) /. (Real.sin (Real.tan x)))) (((2 : ℝ))⁻¹)) * ((Real.cos x) ^ (3 : ℕ)))))))) := by
  sorry

theorem proof_gap_exercise_2235_3
  (h1 : (exists (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < (Real.pi /. 2)))))
  (h2 : Tendsto (fun x : ℝ => ((∫ t in (0 : ℝ)..(Real.sin x), ((Real.rpow (Real.tan t) (((2 : ℝ))⁻¹)) * (1 : ℝ))) /. (∫ t in (0 : ℝ)..(Real.tan x), ((Real.rpow (Real.sin t) (((2 : ℝ))⁻¹)) * (1 : ℝ))))) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x : ℝ => (((Real.rpow (Real.tan (Real.sin x)) (((2 : ℝ))⁻¹)) * (iteratedDeriv 1 (fun t_1 => (Real.sin t_1)) x)) /. ((Real.rpow (Real.sin (Real.tan x)) (((2 : ℝ))⁻¹)) * (iteratedDeriv 1 (fun t_1 => (Real.tan t_1)) x)))))))
  (h3 : Tendsto (fun x : ℝ => (((Real.rpow (Real.tan (Real.sin x)) (((2 : ℝ))⁻¹)) * (iteratedDeriv 1 (fun t_1 => (Real.sin t_1)) x)) /. ((Real.rpow (Real.sin (Real.tan x)) (((2 : ℝ))⁻¹)) * (iteratedDeriv 1 (fun t_1 => (Real.tan t_1)) x)))) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x : ℝ => ((Real.rpow ((((Real.tan (Real.sin x)) /. (Real.sin x)) * ((Real.sin x) /. (Real.tan x))) * ((Real.tan x) /. (Real.sin (Real.tan x)))) (((2 : ℝ))⁻¹)) * ((Real.cos x) ^ (3 : ℕ)))))))
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((Real.rpow (Real.tan (Real.sin x)) (((2 : ℝ))⁻¹)) * (iteratedDeriv 1 (fun t_1 => (Real.sin t_1)) x)) /. ((Real.rpow (Real.sin (Real.tan x)) (((2 : ℝ))⁻¹)) * (iteratedDeriv 1 (fun t_1 => (Real.tan t_1)) x)))) (𝓝[>] 0) (𝓝 L))
  (h5 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((Real.rpow ((((Real.tan (Real.sin x)) /. (Real.sin x)) * ((Real.sin x) /. (Real.tan x))) * ((Real.tan x) /. (Real.sin (Real.tan x)))) (((2 : ℝ))⁻¹)) * ((Real.cos x) ^ (3 : ℕ)))) (𝓝[>] 0) (𝓝 L))
  : Tendsto (fun x : ℝ => ((Real.rpow ((((Real.tan (Real.sin x)) /. (Real.sin x)) * ((Real.sin x) /. (Real.tan x))) * ((Real.tan x) /. (Real.sin (Real.tan x)))) (((2 : ℝ))⁻¹)) * ((Real.cos x) ^ (3 : ℕ)))) (𝓝[>] 0) (𝓝 1) := by
  sorry

theorem proof_gap_exercise_2235_4
  (h1 : (exists (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < (Real.pi /. 2)))))
  (h2 : Tendsto (fun x : ℝ => ((∫ t in (0 : ℝ)..(Real.sin x), ((Real.rpow (Real.tan t) (((2 : ℝ))⁻¹)) * (1 : ℝ))) /. (∫ t in (0 : ℝ)..(Real.tan x), ((Real.rpow (Real.sin t) (((2 : ℝ))⁻¹)) * (1 : ℝ))))) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x : ℝ => (((Real.rpow (Real.tan (Real.sin x)) (((2 : ℝ))⁻¹)) * (iteratedDeriv 1 (fun t_1 => (Real.sin t_1)) x)) /. ((Real.rpow (Real.sin (Real.tan x)) (((2 : ℝ))⁻¹)) * (iteratedDeriv 1 (fun t_1 => (Real.tan t_1)) x)))))))
  (h3 : Tendsto (fun x : ℝ => (((Real.rpow (Real.tan (Real.sin x)) (((2 : ℝ))⁻¹)) * (iteratedDeriv 1 (fun t_1 => (Real.sin t_1)) x)) /. ((Real.rpow (Real.sin (Real.tan x)) (((2 : ℝ))⁻¹)) * (iteratedDeriv 1 (fun t_1 => (Real.tan t_1)) x)))) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x : ℝ => ((Real.rpow ((((Real.tan (Real.sin x)) /. (Real.sin x)) * ((Real.sin x) /. (Real.tan x))) * ((Real.tan x) /. (Real.sin (Real.tan x)))) (((2 : ℝ))⁻¹)) * ((Real.cos x) ^ (3 : ℕ)))))))
  (h4 : Tendsto (fun x : ℝ => ((Real.rpow ((((Real.tan (Real.sin x)) /. (Real.sin x)) * ((Real.sin x) /. (Real.tan x))) * ((Real.tan x) /. (Real.sin (Real.tan x)))) (((2 : ℝ))⁻¹)) * ((Real.cos x) ^ (3 : ℕ)))) (𝓝[>] 0) (𝓝 1))
  (h5 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((Real.rpow (Real.tan (Real.sin x)) (((2 : ℝ))⁻¹)) * (iteratedDeriv 1 (fun t_1 => (Real.sin t_1)) x)) /. ((Real.rpow (Real.sin (Real.tan x)) (((2 : ℝ))⁻¹)) * (iteratedDeriv 1 (fun t_1 => (Real.tan t_1)) x)))) (𝓝[>] 0) (𝓝 L))
  (h6 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((Real.rpow ((((Real.tan (Real.sin x)) /. (Real.sin x)) * ((Real.sin x) /. (Real.tan x))) * ((Real.tan x) /. (Real.sin (Real.tan x)))) (((2 : ℝ))⁻¹)) * ((Real.cos x) ^ (3 : ℕ)))) (𝓝[>] 0) (𝓝 L))
  : Tendsto (fun x : ℝ => ((∫ t in (0 : ℝ)..(Real.sin x), ((Real.rpow (Real.tan t) (((2 : ℝ))⁻¹)) * (1 : ℝ))) /. (∫ t in (0 : ℝ)..(Real.tan x), ((Real.rpow (Real.sin t) (((2 : ℝ))⁻¹)) * (1 : ℝ))))) (𝓝[>] 0) (𝓝 1) := by
  sorry

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

-- exercise: exercise_462

theorem proof_gap_exercise_462_1
  : (∃ L : ℝ, Tendsto (fun x : ℝ => (((((x ^ (3 : ℕ)) + (3 * (x ^ (2 : ℕ)))) ^ (2 : ℕ)) - (((x ^ (2 : ℕ)) - (2 * x)) ^ (3 : ℕ))) /. (∑ k ∈ Finset.Icc (0 : ℕ) (5 : ℕ), ((Real.rpow ((x ^ (3 : ℕ)) + (3 * (x ^ (2 : ℕ)))) ((5 - k) /. 3)) * (Real.rpow ((x ^ (2 : ℕ)) - (2 * x)) (k /. 2)))))) atTop (𝓝 L) ∧ (Tendsto (fun x : ℝ => ((Real.rpow ((x ^ (3 : ℕ)) + (3 * (x ^ (2 : ℕ)))) (((3 : ℝ))⁻¹)) - (Real.rpow ((x ^ (2 : ℕ)) - (2 * x)) (((2 : ℝ))⁻¹)))) atTop (𝓝 (atTop.limUnder (fun x : ℝ => (((((x ^ (3 : ℕ)) + (3 * (x ^ (2 : ℕ)))) ^ (2 : ℕ)) - (((x ^ (2 : ℕ)) - (2 * x)) ^ (3 : ℕ))) /. (∑ k ∈ Finset.Icc (0 : ℕ) (5 : ℕ), ((Real.rpow ((x ^ (3 : ℕ)) + (3 * (x ^ (2 : ℕ)))) ((5 - k) /. 3)) * (Real.rpow ((x ^ (2 : ℕ)) - (2 * x)) (k /. 2)))))))))) := by
  sorry

theorem proof_gap_exercise_462_2
  (h1 : Tendsto (fun x : ℝ => ((Real.rpow ((x ^ (3 : ℕ)) + (3 * (x ^ (2 : ℕ)))) (((3 : ℝ))⁻¹)) - (Real.rpow ((x ^ (2 : ℕ)) - (2 * x)) (((2 : ℝ))⁻¹)))) atTop (𝓝 (atTop.limUnder (fun x : ℝ => (((((x ^ (3 : ℕ)) + (3 * (x ^ (2 : ℕ)))) ^ (2 : ℕ)) - (((x ^ (2 : ℕ)) - (2 * x)) ^ (3 : ℕ))) /. (∑ k ∈ Finset.Icc (0 : ℕ) (5 : ℕ), ((Real.rpow ((x ^ (3 : ℕ)) + (3 * (x ^ (2 : ℕ)))) ((5 - k) /. 3)) * (Real.rpow ((x ^ (2 : ℕ)) - (2 * x)) (k /. 2)))))))))
  (h2 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((((x ^ (3 : ℕ)) + (3 * (x ^ (2 : ℕ)))) ^ (2 : ℕ)) - (((x ^ (2 : ℕ)) - (2 * x)) ^ (3 : ℕ))) /. (∑ k ∈ Finset.Icc (0 : ℕ) (5 : ℕ), ((Real.rpow ((x ^ (3 : ℕ)) + (3 * (x ^ (2 : ℕ)))) ((5 - k) /. 3)) * (Real.rpow ((x ^ (2 : ℕ)) - (2 * x)) (k /. 2)))))) atTop (𝓝 L))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => (((x ^ (5 : ℕ)) * ((12 - (3 /. x)) + (8 /. (x ^ (2 : ℕ))))) /. (∑ k ∈ Finset.Icc (0 : ℕ) (5 : ℕ), ((Real.rpow ((x ^ (3 : ℕ)) + (3 * (x ^ (2 : ℕ)))) ((5 - k) /. 3)) * (Real.rpow ((x ^ (2 : ℕ)) - (2 * x)) (k /. 2)))))) atTop (𝓝 L) ∧ (Tendsto (fun x : ℝ => (((((x ^ (3 : ℕ)) + (3 * (x ^ (2 : ℕ)))) ^ (2 : ℕ)) - (((x ^ (2 : ℕ)) - (2 * x)) ^ (3 : ℕ))) /. (∑ k ∈ Finset.Icc (0 : ℕ) (5 : ℕ), ((Real.rpow ((x ^ (3 : ℕ)) + (3 * (x ^ (2 : ℕ)))) ((5 - k) /. 3)) * (Real.rpow ((x ^ (2 : ℕ)) - (2 * x)) (k /. 2)))))) atTop (𝓝 (atTop.limUnder (fun x : ℝ => (((x ^ (5 : ℕ)) * ((12 - (3 /. x)) + (8 /. (x ^ (2 : ℕ))))) /. (∑ k ∈ Finset.Icc (0 : ℕ) (5 : ℕ), ((Real.rpow ((x ^ (3 : ℕ)) + (3 * (x ^ (2 : ℕ)))) ((5 - k) /. 3)) * (Real.rpow ((x ^ (2 : ℕ)) - (2 * x)) (k /. 2)))))))))) := by
  sorry

theorem proof_gap_exercise_462_3
  (h1 : Tendsto (fun x : ℝ => ((Real.rpow ((x ^ (3 : ℕ)) + (3 * (x ^ (2 : ℕ)))) (((3 : ℝ))⁻¹)) - (Real.rpow ((x ^ (2 : ℕ)) - (2 * x)) (((2 : ℝ))⁻¹)))) atTop (𝓝 (atTop.limUnder (fun x : ℝ => (((((x ^ (3 : ℕ)) + (3 * (x ^ (2 : ℕ)))) ^ (2 : ℕ)) - (((x ^ (2 : ℕ)) - (2 * x)) ^ (3 : ℕ))) /. (∑ k ∈ Finset.Icc (0 : ℕ) (5 : ℕ), ((Real.rpow ((x ^ (3 : ℕ)) + (3 * (x ^ (2 : ℕ)))) ((5 - k) /. 3)) * (Real.rpow ((x ^ (2 : ℕ)) - (2 * x)) (k /. 2)))))))))
  (h2 : Tendsto (fun x : ℝ => (((((x ^ (3 : ℕ)) + (3 * (x ^ (2 : ℕ)))) ^ (2 : ℕ)) - (((x ^ (2 : ℕ)) - (2 * x)) ^ (3 : ℕ))) /. (∑ k ∈ Finset.Icc (0 : ℕ) (5 : ℕ), ((Real.rpow ((x ^ (3 : ℕ)) + (3 * (x ^ (2 : ℕ)))) ((5 - k) /. 3)) * (Real.rpow ((x ^ (2 : ℕ)) - (2 * x)) (k /. 2)))))) atTop (𝓝 (atTop.limUnder (fun x : ℝ => (((x ^ (5 : ℕ)) * ((12 - (3 /. x)) + (8 /. (x ^ (2 : ℕ))))) /. (∑ k ∈ Finset.Icc (0 : ℕ) (5 : ℕ), ((Real.rpow ((x ^ (3 : ℕ)) + (3 * (x ^ (2 : ℕ)))) ((5 - k) /. 3)) * (Real.rpow ((x ^ (2 : ℕ)) - (2 * x)) (k /. 2)))))))))
  (h3 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((((x ^ (3 : ℕ)) + (3 * (x ^ (2 : ℕ)))) ^ (2 : ℕ)) - (((x ^ (2 : ℕ)) - (2 * x)) ^ (3 : ℕ))) /. (∑ k ∈ Finset.Icc (0 : ℕ) (5 : ℕ), ((Real.rpow ((x ^ (3 : ℕ)) + (3 * (x ^ (2 : ℕ)))) ((5 - k) /. 3)) * (Real.rpow ((x ^ (2 : ℕ)) - (2 * x)) (k /. 2)))))) atTop (𝓝 L))
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((x ^ (5 : ℕ)) * ((12 - (3 /. x)) + (8 /. (x ^ (2 : ℕ))))) /. (∑ k ∈ Finset.Icc (0 : ℕ) (5 : ℕ), ((Real.rpow ((x ^ (3 : ℕ)) + (3 * (x ^ (2 : ℕ)))) ((5 - k) /. 3)) * (Real.rpow ((x ^ (2 : ℕ)) - (2 * x)) (k /. 2)))))) atTop (𝓝 L))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => (((12 - (3 /. x)) + (8 /. (x ^ (2 : ℕ)))) /. (∑ k ∈ Finset.Icc (0 : ℕ) (5 : ℕ), ((Real.rpow (1 + (3 /. x)) ((5 - k) /. 3)) * (Real.rpow (1 - (2 /. x)) (k /. 2)))))) atTop (𝓝 L) ∧ (Tendsto (fun x : ℝ => (((x ^ (5 : ℕ)) * ((12 - (3 /. x)) + (8 /. (x ^ (2 : ℕ))))) /. (∑ k ∈ Finset.Icc (0 : ℕ) (5 : ℕ), ((Real.rpow ((x ^ (3 : ℕ)) + (3 * (x ^ (2 : ℕ)))) ((5 - k) /. 3)) * (Real.rpow ((x ^ (2 : ℕ)) - (2 * x)) (k /. 2)))))) atTop (𝓝 (atTop.limUnder (fun x : ℝ => (((12 - (3 /. x)) + (8 /. (x ^ (2 : ℕ)))) /. (∑ k ∈ Finset.Icc (0 : ℕ) (5 : ℕ), ((Real.rpow (1 + (3 /. x)) ((5 - k) /. 3)) * (Real.rpow (1 - (2 /. x)) (k /. 2)))))))))) := by
  sorry

theorem proof_gap_exercise_462_4
  (h1 : Tendsto (fun x : ℝ => ((Real.rpow ((x ^ (3 : ℕ)) + (3 * (x ^ (2 : ℕ)))) (((3 : ℝ))⁻¹)) - (Real.rpow ((x ^ (2 : ℕ)) - (2 * x)) (((2 : ℝ))⁻¹)))) atTop (𝓝 (atTop.limUnder (fun x : ℝ => (((((x ^ (3 : ℕ)) + (3 * (x ^ (2 : ℕ)))) ^ (2 : ℕ)) - (((x ^ (2 : ℕ)) - (2 * x)) ^ (3 : ℕ))) /. (∑ k ∈ Finset.Icc (0 : ℕ) (5 : ℕ), ((Real.rpow ((x ^ (3 : ℕ)) + (3 * (x ^ (2 : ℕ)))) ((5 - k) /. 3)) * (Real.rpow ((x ^ (2 : ℕ)) - (2 * x)) (k /. 2)))))))))
  (h2 : Tendsto (fun x : ℝ => (((((x ^ (3 : ℕ)) + (3 * (x ^ (2 : ℕ)))) ^ (2 : ℕ)) - (((x ^ (2 : ℕ)) - (2 * x)) ^ (3 : ℕ))) /. (∑ k ∈ Finset.Icc (0 : ℕ) (5 : ℕ), ((Real.rpow ((x ^ (3 : ℕ)) + (3 * (x ^ (2 : ℕ)))) ((5 - k) /. 3)) * (Real.rpow ((x ^ (2 : ℕ)) - (2 * x)) (k /. 2)))))) atTop (𝓝 (atTop.limUnder (fun x : ℝ => (((x ^ (5 : ℕ)) * ((12 - (3 /. x)) + (8 /. (x ^ (2 : ℕ))))) /. (∑ k ∈ Finset.Icc (0 : ℕ) (5 : ℕ), ((Real.rpow ((x ^ (3 : ℕ)) + (3 * (x ^ (2 : ℕ)))) ((5 - k) /. 3)) * (Real.rpow ((x ^ (2 : ℕ)) - (2 * x)) (k /. 2)))))))))
  (h3 : Tendsto (fun x : ℝ => (((x ^ (5 : ℕ)) * ((12 - (3 /. x)) + (8 /. (x ^ (2 : ℕ))))) /. (∑ k ∈ Finset.Icc (0 : ℕ) (5 : ℕ), ((Real.rpow ((x ^ (3 : ℕ)) + (3 * (x ^ (2 : ℕ)))) ((5 - k) /. 3)) * (Real.rpow ((x ^ (2 : ℕ)) - (2 * x)) (k /. 2)))))) atTop (𝓝 (atTop.limUnder (fun x : ℝ => (((12 - (3 /. x)) + (8 /. (x ^ (2 : ℕ)))) /. (∑ k ∈ Finset.Icc (0 : ℕ) (5 : ℕ), ((Real.rpow (1 + (3 /. x)) ((5 - k) /. 3)) * (Real.rpow (1 - (2 /. x)) (k /. 2)))))))))
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((((x ^ (3 : ℕ)) + (3 * (x ^ (2 : ℕ)))) ^ (2 : ℕ)) - (((x ^ (2 : ℕ)) - (2 * x)) ^ (3 : ℕ))) /. (∑ k ∈ Finset.Icc (0 : ℕ) (5 : ℕ), ((Real.rpow ((x ^ (3 : ℕ)) + (3 * (x ^ (2 : ℕ)))) ((5 - k) /. 3)) * (Real.rpow ((x ^ (2 : ℕ)) - (2 * x)) (k /. 2)))))) atTop (𝓝 L))
  (h5 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((x ^ (5 : ℕ)) * ((12 - (3 /. x)) + (8 /. (x ^ (2 : ℕ))))) /. (∑ k ∈ Finset.Icc (0 : ℕ) (5 : ℕ), ((Real.rpow ((x ^ (3 : ℕ)) + (3 * (x ^ (2 : ℕ)))) ((5 - k) /. 3)) * (Real.rpow ((x ^ (2 : ℕ)) - (2 * x)) (k /. 2)))))) atTop (𝓝 L))
  (h6 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((12 - (3 /. x)) + (8 /. (x ^ (2 : ℕ)))) /. (∑ k ∈ Finset.Icc (0 : ℕ) (5 : ℕ), ((Real.rpow (1 + (3 /. x)) ((5 - k) /. 3)) * (Real.rpow (1 - (2 /. x)) (k /. 2)))))) atTop (𝓝 L))
  : Tendsto (fun x : ℝ => (((12 - (3 /. x)) + (8 /. (x ^ (2 : ℕ)))) /. (∑ k ∈ Finset.Icc (0 : ℕ) (5 : ℕ), ((Real.rpow (1 + (3 /. x)) ((5 - k) /. 3)) * (Real.rpow (1 - (2 /. x)) (k /. 2)))))) atTop (𝓝 2) := by
  sorry

theorem proof_gap_exercise_462_5
  (h1 : Tendsto (fun x : ℝ => ((Real.rpow ((x ^ (3 : ℕ)) + (3 * (x ^ (2 : ℕ)))) (((3 : ℝ))⁻¹)) - (Real.rpow ((x ^ (2 : ℕ)) - (2 * x)) (((2 : ℝ))⁻¹)))) atTop (𝓝 (atTop.limUnder (fun x : ℝ => (((((x ^ (3 : ℕ)) + (3 * (x ^ (2 : ℕ)))) ^ (2 : ℕ)) - (((x ^ (2 : ℕ)) - (2 * x)) ^ (3 : ℕ))) /. (∑ k ∈ Finset.Icc (0 : ℕ) (5 : ℕ), ((Real.rpow ((x ^ (3 : ℕ)) + (3 * (x ^ (2 : ℕ)))) ((5 - k) /. 3)) * (Real.rpow ((x ^ (2 : ℕ)) - (2 * x)) (k /. 2)))))))))
  (h2 : Tendsto (fun x : ℝ => (((((x ^ (3 : ℕ)) + (3 * (x ^ (2 : ℕ)))) ^ (2 : ℕ)) - (((x ^ (2 : ℕ)) - (2 * x)) ^ (3 : ℕ))) /. (∑ k ∈ Finset.Icc (0 : ℕ) (5 : ℕ), ((Real.rpow ((x ^ (3 : ℕ)) + (3 * (x ^ (2 : ℕ)))) ((5 - k) /. 3)) * (Real.rpow ((x ^ (2 : ℕ)) - (2 * x)) (k /. 2)))))) atTop (𝓝 (atTop.limUnder (fun x : ℝ => (((x ^ (5 : ℕ)) * ((12 - (3 /. x)) + (8 /. (x ^ (2 : ℕ))))) /. (∑ k ∈ Finset.Icc (0 : ℕ) (5 : ℕ), ((Real.rpow ((x ^ (3 : ℕ)) + (3 * (x ^ (2 : ℕ)))) ((5 - k) /. 3)) * (Real.rpow ((x ^ (2 : ℕ)) - (2 * x)) (k /. 2)))))))))
  (h3 : Tendsto (fun x : ℝ => (((x ^ (5 : ℕ)) * ((12 - (3 /. x)) + (8 /. (x ^ (2 : ℕ))))) /. (∑ k ∈ Finset.Icc (0 : ℕ) (5 : ℕ), ((Real.rpow ((x ^ (3 : ℕ)) + (3 * (x ^ (2 : ℕ)))) ((5 - k) /. 3)) * (Real.rpow ((x ^ (2 : ℕ)) - (2 * x)) (k /. 2)))))) atTop (𝓝 (atTop.limUnder (fun x : ℝ => (((12 - (3 /. x)) + (8 /. (x ^ (2 : ℕ)))) /. (∑ k ∈ Finset.Icc (0 : ℕ) (5 : ℕ), ((Real.rpow (1 + (3 /. x)) ((5 - k) /. 3)) * (Real.rpow (1 - (2 /. x)) (k /. 2)))))))))
  (h4 : Tendsto (fun x : ℝ => (((12 - (3 /. x)) + (8 /. (x ^ (2 : ℕ)))) /. (∑ k ∈ Finset.Icc (0 : ℕ) (5 : ℕ), ((Real.rpow (1 + (3 /. x)) ((5 - k) /. 3)) * (Real.rpow (1 - (2 /. x)) (k /. 2)))))) atTop (𝓝 2))
  (h5 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((((x ^ (3 : ℕ)) + (3 * (x ^ (2 : ℕ)))) ^ (2 : ℕ)) - (((x ^ (2 : ℕ)) - (2 * x)) ^ (3 : ℕ))) /. (∑ k ∈ Finset.Icc (0 : ℕ) (5 : ℕ), ((Real.rpow ((x ^ (3 : ℕ)) + (3 * (x ^ (2 : ℕ)))) ((5 - k) /. 3)) * (Real.rpow ((x ^ (2 : ℕ)) - (2 * x)) (k /. 2)))))) atTop (𝓝 L))
  (h6 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((x ^ (5 : ℕ)) * ((12 - (3 /. x)) + (8 /. (x ^ (2 : ℕ))))) /. (∑ k ∈ Finset.Icc (0 : ℕ) (5 : ℕ), ((Real.rpow ((x ^ (3 : ℕ)) + (3 * (x ^ (2 : ℕ)))) ((5 - k) /. 3)) * (Real.rpow ((x ^ (2 : ℕ)) - (2 * x)) (k /. 2)))))) atTop (𝓝 L))
  (h7 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((12 - (3 /. x)) + (8 /. (x ^ (2 : ℕ)))) /. (∑ k ∈ Finset.Icc (0 : ℕ) (5 : ℕ), ((Real.rpow (1 + (3 /. x)) ((5 - k) /. 3)) * (Real.rpow (1 - (2 /. x)) (k /. 2)))))) atTop (𝓝 L))
  : Tendsto (fun x : ℝ => ((Real.rpow ((x ^ (3 : ℕ)) + (3 * (x ^ (2 : ℕ)))) (((3 : ℝ))⁻¹)) - (Real.rpow ((x ^ (2 : ℕ)) - (2 * x)) (((2 : ℝ))⁻¹)))) atTop (𝓝 2) := by
  sorry

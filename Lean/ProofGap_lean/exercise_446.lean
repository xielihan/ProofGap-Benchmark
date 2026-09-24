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

-- exercise: exercise_446

theorem proof_gap_exercise_446_1
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < |(x)|)) ∧ (|(x)| < (1 /. 2))) → ((x + (x ^ (2 : ℕ))) ≠ 0))) := by
  sorry

theorem proof_gap_exercise_446_2
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < |(x)|)) ∧ (|(x)| < (1 /. 2))) → ((x + (x ^ (2 : ℕ))) ≠ 0))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < |(x)|)) ∧ (|(x)| < (1 /. 2))) → ((((Real.rpow (((8 + (3 * x)) - (x ^ (2 : ℕ))) ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)))) + 4) ≠ 0))) := by
  sorry

theorem proof_gap_exercise_446_3
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < |(x)|)) ∧ (|(x)| < (1 /. 2))) → ((x + (x ^ (2 : ℕ))) ≠ 0))))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < |(x)|)) ∧ (|(x)| < (1 /. 2))) → ((((Real.rpow (((8 + (3 * x)) - (x ^ (2 : ℕ))) ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)))) + 4) ≠ 0))))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => ((((Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)) - 2) /. (x + (x ^ (2 : ℕ)))) * ((((Real.rpow (((8 + (3 * x)) - (x ^ (2 : ℕ))) ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)))) + 4) /. (((Real.rpow (((8 + (3 * x)) - (x ^ (2 : ℕ))) ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)))) + 4)))) (𝓝[≠] 0) (𝓝 L) ∧ (Tendsto (fun x : ℝ => (((Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)) - 2) /. (x + (x ^ (2 : ℕ))))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)) - 2) /. (x + (x ^ (2 : ℕ)))) * ((((Real.rpow (((8 + (3 * x)) - (x ^ (2 : ℕ))) ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)))) + 4) /. (((Real.rpow (((8 + (3 * x)) - (x ^ (2 : ℕ))) ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)))) + 4)))))))) := by
  sorry

theorem proof_gap_exercise_446_4
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < |(x)|)) ∧ (|(x)| < (1 /. 2))) → ((x + (x ^ (2 : ℕ))) ≠ 0))))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < |(x)|)) ∧ (|(x)| < (1 /. 2))) → ((((Real.rpow (((8 + (3 * x)) - (x ^ (2 : ℕ))) ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)))) + 4) ≠ 0))))
  (h3 : Tendsto (fun x : ℝ => (((Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)) - 2) /. (x + (x ^ (2 : ℕ))))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)) - 2) /. (x + (x ^ (2 : ℕ)))) * ((((Real.rpow (((8 + (3 * x)) - (x ^ (2 : ℕ))) ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)))) + 4) /. (((Real.rpow (((8 + (3 * x)) - (x ^ (2 : ℕ))) ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)))) + 4)))))))
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((((Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)) - 2) /. (x + (x ^ (2 : ℕ)))) * ((((Real.rpow (((8 + (3 * x)) - (x ^ (2 : ℕ))) ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)))) + 4) /. (((Real.rpow (((8 + (3 * x)) - (x ^ (2 : ℕ))) ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)))) + 4)))) (𝓝[≠] 0) (𝓝 L))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => ((3 - x) /. ((1 + x) * (((Real.rpow (((8 + (3 * x)) - (x ^ (2 : ℕ))) ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)))) + 4)))) (𝓝[≠] 0) (𝓝 L) ∧ (Tendsto (fun x : ℝ => ((((Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)) - 2) /. (x + (x ^ (2 : ℕ)))) * ((((Real.rpow (((8 + (3 * x)) - (x ^ (2 : ℕ))) ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)))) + 4) /. (((Real.rpow (((8 + (3 * x)) - (x ^ (2 : ℕ))) ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)))) + 4)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((3 - x) /. ((1 + x) * (((Real.rpow (((8 + (3 * x)) - (x ^ (2 : ℕ))) ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)))) + 4)))))))) := by
  sorry

theorem proof_gap_exercise_446_5
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < |(x)|)) ∧ (|(x)| < (1 /. 2))) → ((x + (x ^ (2 : ℕ))) ≠ 0))))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < |(x)|)) ∧ (|(x)| < (1 /. 2))) → ((((Real.rpow (((8 + (3 * x)) - (x ^ (2 : ℕ))) ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)))) + 4) ≠ 0))))
  (h3 : Tendsto (fun x : ℝ => (((Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)) - 2) /. (x + (x ^ (2 : ℕ))))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)) - 2) /. (x + (x ^ (2 : ℕ)))) * ((((Real.rpow (((8 + (3 * x)) - (x ^ (2 : ℕ))) ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)))) + 4) /. (((Real.rpow (((8 + (3 * x)) - (x ^ (2 : ℕ))) ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)))) + 4)))))))
  (h4 : Tendsto (fun x : ℝ => ((((Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)) - 2) /. (x + (x ^ (2 : ℕ)))) * ((((Real.rpow (((8 + (3 * x)) - (x ^ (2 : ℕ))) ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)))) + 4) /. (((Real.rpow (((8 + (3 * x)) - (x ^ (2 : ℕ))) ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)))) + 4)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((3 - x) /. ((1 + x) * (((Real.rpow (((8 + (3 * x)) - (x ^ (2 : ℕ))) ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)))) + 4)))))))
  (h5 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((((Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)) - 2) /. (x + (x ^ (2 : ℕ)))) * ((((Real.rpow (((8 + (3 * x)) - (x ^ (2 : ℕ))) ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)))) + 4) /. (((Real.rpow (((8 + (3 * x)) - (x ^ (2 : ℕ))) ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)))) + 4)))) (𝓝[≠] 0) (𝓝 L))
  (h6 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((3 - x) /. ((1 + x) * (((Real.rpow (((8 + (3 * x)) - (x ^ (2 : ℕ))) ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)))) + 4)))) (𝓝[≠] 0) (𝓝 L))
  : Tendsto (fun x : ℝ => ((3 - x) /. ((1 + x) * (((Real.rpow (((8 + (3 * x)) - (x ^ (2 : ℕ))) ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)))) + 4)))) (𝓝[≠] 0) (𝓝 (1 /. 4)) := by
  sorry

theorem proof_gap_exercise_446_6
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < |(x)|)) ∧ (|(x)| < (1 /. 2))) → ((x + (x ^ (2 : ℕ))) ≠ 0))))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < |(x)|)) ∧ (|(x)| < (1 /. 2))) → ((((Real.rpow (((8 + (3 * x)) - (x ^ (2 : ℕ))) ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)))) + 4) ≠ 0))))
  (h3 : Tendsto (fun x : ℝ => (((Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)) - 2) /. (x + (x ^ (2 : ℕ))))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)) - 2) /. (x + (x ^ (2 : ℕ)))) * ((((Real.rpow (((8 + (3 * x)) - (x ^ (2 : ℕ))) ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)))) + 4) /. (((Real.rpow (((8 + (3 * x)) - (x ^ (2 : ℕ))) ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)))) + 4)))))))
  (h4 : Tendsto (fun x : ℝ => ((((Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)) - 2) /. (x + (x ^ (2 : ℕ)))) * ((((Real.rpow (((8 + (3 * x)) - (x ^ (2 : ℕ))) ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)))) + 4) /. (((Real.rpow (((8 + (3 * x)) - (x ^ (2 : ℕ))) ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)))) + 4)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((3 - x) /. ((1 + x) * (((Real.rpow (((8 + (3 * x)) - (x ^ (2 : ℕ))) ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)))) + 4)))))))
  (h5 : Tendsto (fun x : ℝ => ((3 - x) /. ((1 + x) * (((Real.rpow (((8 + (3 * x)) - (x ^ (2 : ℕ))) ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)))) + 4)))) (𝓝[≠] 0) (𝓝 (1 /. 4)))
  (h6 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((((Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)) - 2) /. (x + (x ^ (2 : ℕ)))) * ((((Real.rpow (((8 + (3 * x)) - (x ^ (2 : ℕ))) ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)))) + 4) /. (((Real.rpow (((8 + (3 * x)) - (x ^ (2 : ℕ))) ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)))) + 4)))) (𝓝[≠] 0) (𝓝 L))
  (h7 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((3 - x) /. ((1 + x) * (((Real.rpow (((8 + (3 * x)) - (x ^ (2 : ℕ))) ^ (2 : ℕ)) (((3 : ℝ))⁻¹)) + (2 * (Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)))) + 4)))) (𝓝[≠] 0) (𝓝 L))
  : Tendsto (fun x : ℝ => (((Real.rpow ((8 + (3 * x)) - (x ^ (2 : ℕ))) (((3 : ℝ))⁻¹)) - 2) /. (x + (x ^ (2 : ℕ))))) (𝓝[≠] 0) (𝓝 (1 /. 4)) := by
  sorry

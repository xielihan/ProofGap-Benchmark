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

-- exercise: exercise_450

theorem proof_gap_exercise_450_1
  (h1 : A = (1 + (x /. 3)))
  (h2 : B = (1 + (x /. 4)))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => ((((Real.rpow (A ^ (4 : ℕ)) (((12 : ℝ))⁻¹)) - (Real.rpow (B ^ (3 : ℕ)) (((12 : ℝ))⁻¹))) * (1 + (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹)))) /. ((1 - (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹))) * (1 + (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹)))))) (𝓝[≠] 0) (𝓝 L) ∧ (Tendsto (fun x : ℝ => (((Real.rpow A (((3 : ℝ))⁻¹)) - (Real.rpow B (((4 : ℝ))⁻¹))) /. (1 - (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹))))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((Real.rpow (A ^ (4 : ℕ)) (((12 : ℝ))⁻¹)) - (Real.rpow (B ^ (3 : ℕ)) (((12 : ℝ))⁻¹))) * (1 + (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹)))) /. ((1 - (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹))) * (1 + (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹)))))))))) := by
  sorry

theorem proof_gap_exercise_450_2
  (h1 : A = (1 + (x /. 3)))
  (h2 : B = (1 + (x /. 4)))
  (h3 : Tendsto (fun x : ℝ => (((Real.rpow A (((3 : ℝ))⁻¹)) - (Real.rpow B (((4 : ℝ))⁻¹))) /. (1 - (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹))))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((Real.rpow (A ^ (4 : ℕ)) (((12 : ℝ))⁻¹)) - (Real.rpow (B ^ (3 : ℕ)) (((12 : ℝ))⁻¹))) * (1 + (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹)))) /. ((1 - (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹))) * (1 + (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹)))))))))
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((((Real.rpow (A ^ (4 : ℕ)) (((12 : ℝ))⁻¹)) - (Real.rpow (B ^ (3 : ℕ)) (((12 : ℝ))⁻¹))) * (1 + (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹)))) /. ((1 - (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹))) * (1 + (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹)))))) (𝓝[≠] 0) (𝓝 L))
  : ((1 - (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹))) * (1 + (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹)))) = (x /. 2) := by
  sorry

theorem proof_gap_exercise_450_3
  (h1 : A = (1 + (x /. 3)))
  (h2 : B = (1 + (x /. 4)))
  (h3 : Tendsto (fun x : ℝ => (((Real.rpow A (((3 : ℝ))⁻¹)) - (Real.rpow B (((4 : ℝ))⁻¹))) /. (1 - (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹))))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((Real.rpow (A ^ (4 : ℕ)) (((12 : ℝ))⁻¹)) - (Real.rpow (B ^ (3 : ℕ)) (((12 : ℝ))⁻¹))) * (1 + (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹)))) /. ((1 - (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹))) * (1 + (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹)))))))))
  (h4 : ((1 - (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹))) * (1 + (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹)))) = (x /. 2))
  (h5 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((((Real.rpow (A ^ (4 : ℕ)) (((12 : ℝ))⁻¹)) - (Real.rpow (B ^ (3 : ℕ)) (((12 : ℝ))⁻¹))) * (1 + (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹)))) /. ((1 - (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹))) * (1 + (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹)))))) (𝓝[≠] 0) (𝓝 L))
  : ((A ^ (4 : ℕ)) - (B ^ (3 : ℕ))) = (x * ((((7 /. 12) + ((23 * x) /. 48)) + ((229 * (x ^ (2 : ℕ))) /. 1728)) + ((x ^ (3 : ℕ)) /. 81))) := by
  sorry

theorem proof_gap_exercise_450_4
  (h1 : A = (1 + (x /. 3)))
  (h2 : B = (1 + (x /. 4)))
  (h3 : Tendsto (fun x : ℝ => (((Real.rpow A (((3 : ℝ))⁻¹)) - (Real.rpow B (((4 : ℝ))⁻¹))) /. (1 - (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹))))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((Real.rpow (A ^ (4 : ℕ)) (((12 : ℝ))⁻¹)) - (Real.rpow (B ^ (3 : ℕ)) (((12 : ℝ))⁻¹))) * (1 + (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹)))) /. ((1 - (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹))) * (1 + (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹)))))))))
  (h4 : ((1 - (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹))) * (1 + (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹)))) = (x /. 2))
  (h5 : ((A ^ (4 : ℕ)) - (B ^ (3 : ℕ))) = (x * ((((7 /. 12) + ((23 * x) /. 48)) + ((229 * (x ^ (2 : ℕ))) /. 1728)) + ((x ^ (3 : ℕ)) /. 81))))
  (h6 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((((Real.rpow (A ^ (4 : ℕ)) (((12 : ℝ))⁻¹)) - (Real.rpow (B ^ (3 : ℕ)) (((12 : ℝ))⁻¹))) * (1 + (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹)))) /. ((1 - (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹))) * (1 + (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹)))))) (𝓝[≠] 0) (𝓝 L))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => (((x * ((((7 /. 12) + ((23 * x) /. 48)) + ((229 * (x ^ (2 : ℕ))) /. 1728)) + ((x ^ (3 : ℕ)) /. 81))) * (1 + (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹)))) /. ((x /. 2) * ((((((((((((Real.rpow (A ^ (44 : ℕ)) (((12 : ℝ))⁻¹)) + (Real.rpow ((A ^ (40 : ℕ)) * (B ^ (3 : ℕ))) (((12 : ℝ))⁻¹))) + (Real.rpow ((A ^ (36 : ℕ)) * (B ^ (6 : ℕ))) (((12 : ℝ))⁻¹))) + (Real.rpow ((A ^ (32 : ℕ)) * (B ^ (9 : ℕ))) (((12 : ℝ))⁻¹))) + (Real.rpow ((A ^ (28 : ℕ)) * (B ^ (12 : ℕ))) (((12 : ℝ))⁻¹))) + (Real.rpow ((A ^ (24 : ℕ)) * (B ^ (15 : ℕ))) (((12 : ℝ))⁻¹))) + (Real.rpow ((A ^ (20 : ℕ)) * (B ^ (18 : ℕ))) (((12 : ℝ))⁻¹))) + (Real.rpow ((A ^ (16 : ℕ)) * (B ^ (21 : ℕ))) (((12 : ℝ))⁻¹))) + (Real.rpow ((A ^ (12 : ℕ)) * (B ^ (24 : ℕ))) (((12 : ℝ))⁻¹))) + (Real.rpow ((A ^ (8 : ℕ)) * (B ^ (27 : ℕ))) (((12 : ℝ))⁻¹))) + (Real.rpow ((A ^ (4 : ℕ)) * (B ^ (30 : ℕ))) (((12 : ℝ))⁻¹))) + (Real.rpow (B ^ (33 : ℕ)) (((12 : ℝ))⁻¹)))))) (𝓝[≠] 0) (𝓝 L) ∧ (Tendsto (fun x : ℝ => (((Real.rpow A (((3 : ℝ))⁻¹)) - (Real.rpow B (((4 : ℝ))⁻¹))) /. (1 - (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹))))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (((x * ((((7 /. 12) + ((23 * x) /. 48)) + ((229 * (x ^ (2 : ℕ))) /. 1728)) + ((x ^ (3 : ℕ)) /. 81))) * (1 + (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹)))) /. ((x /. 2) * ((((((((((((Real.rpow (A ^ (44 : ℕ)) (((12 : ℝ))⁻¹)) + (Real.rpow ((A ^ (40 : ℕ)) * (B ^ (3 : ℕ))) (((12 : ℝ))⁻¹))) + (Real.rpow ((A ^ (36 : ℕ)) * (B ^ (6 : ℕ))) (((12 : ℝ))⁻¹))) + (Real.rpow ((A ^ (32 : ℕ)) * (B ^ (9 : ℕ))) (((12 : ℝ))⁻¹))) + (Real.rpow ((A ^ (28 : ℕ)) * (B ^ (12 : ℕ))) (((12 : ℝ))⁻¹))) + (Real.rpow ((A ^ (24 : ℕ)) * (B ^ (15 : ℕ))) (((12 : ℝ))⁻¹))) + (Real.rpow ((A ^ (20 : ℕ)) * (B ^ (18 : ℕ))) (((12 : ℝ))⁻¹))) + (Real.rpow ((A ^ (16 : ℕ)) * (B ^ (21 : ℕ))) (((12 : ℝ))⁻¹))) + (Real.rpow ((A ^ (12 : ℕ)) * (B ^ (24 : ℕ))) (((12 : ℝ))⁻¹))) + (Real.rpow ((A ^ (8 : ℕ)) * (B ^ (27 : ℕ))) (((12 : ℝ))⁻¹))) + (Real.rpow ((A ^ (4 : ℕ)) * (B ^ (30 : ℕ))) (((12 : ℝ))⁻¹))) + (Real.rpow (B ^ (33 : ℕ)) (((12 : ℝ))⁻¹)))))))))) := by
  sorry

theorem proof_gap_exercise_450_5
  (h1 : A = (1 + (x /. 3)))
  (h2 : B = (1 + (x /. 4)))
  (h3 : Tendsto (fun x : ℝ => (((Real.rpow A (((3 : ℝ))⁻¹)) - (Real.rpow B (((4 : ℝ))⁻¹))) /. (1 - (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹))))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((Real.rpow (A ^ (4 : ℕ)) (((12 : ℝ))⁻¹)) - (Real.rpow (B ^ (3 : ℕ)) (((12 : ℝ))⁻¹))) * (1 + (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹)))) /. ((1 - (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹))) * (1 + (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹)))))))))
  (h4 : ((1 - (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹))) * (1 + (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹)))) = (x /. 2))
  (h5 : ((A ^ (4 : ℕ)) - (B ^ (3 : ℕ))) = (x * ((((7 /. 12) + ((23 * x) /. 48)) + ((229 * (x ^ (2 : ℕ))) /. 1728)) + ((x ^ (3 : ℕ)) /. 81))))
  (h6 : Tendsto (fun x : ℝ => (((Real.rpow A (((3 : ℝ))⁻¹)) - (Real.rpow B (((4 : ℝ))⁻¹))) /. (1 - (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹))))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (((x * ((((7 /. 12) + ((23 * x) /. 48)) + ((229 * (x ^ (2 : ℕ))) /. 1728)) + ((x ^ (3 : ℕ)) /. 81))) * (1 + (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹)))) /. ((x /. 2) * ((((((((((((Real.rpow (A ^ (44 : ℕ)) (((12 : ℝ))⁻¹)) + (Real.rpow ((A ^ (40 : ℕ)) * (B ^ (3 : ℕ))) (((12 : ℝ))⁻¹))) + (Real.rpow ((A ^ (36 : ℕ)) * (B ^ (6 : ℕ))) (((12 : ℝ))⁻¹))) + (Real.rpow ((A ^ (32 : ℕ)) * (B ^ (9 : ℕ))) (((12 : ℝ))⁻¹))) + (Real.rpow ((A ^ (28 : ℕ)) * (B ^ (12 : ℕ))) (((12 : ℝ))⁻¹))) + (Real.rpow ((A ^ (24 : ℕ)) * (B ^ (15 : ℕ))) (((12 : ℝ))⁻¹))) + (Real.rpow ((A ^ (20 : ℕ)) * (B ^ (18 : ℕ))) (((12 : ℝ))⁻¹))) + (Real.rpow ((A ^ (16 : ℕ)) * (B ^ (21 : ℕ))) (((12 : ℝ))⁻¹))) + (Real.rpow ((A ^ (12 : ℕ)) * (B ^ (24 : ℕ))) (((12 : ℝ))⁻¹))) + (Real.rpow ((A ^ (8 : ℕ)) * (B ^ (27 : ℕ))) (((12 : ℝ))⁻¹))) + (Real.rpow ((A ^ (4 : ℕ)) * (B ^ (30 : ℕ))) (((12 : ℝ))⁻¹))) + (Real.rpow (B ^ (33 : ℕ)) (((12 : ℝ))⁻¹)))))))))
  (h7 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((((Real.rpow (A ^ (4 : ℕ)) (((12 : ℝ))⁻¹)) - (Real.rpow (B ^ (3 : ℕ)) (((12 : ℝ))⁻¹))) * (1 + (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹)))) /. ((1 - (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹))) * (1 + (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹)))))) (𝓝[≠] 0) (𝓝 L))
  (h8 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((x * ((((7 /. 12) + ((23 * x) /. 48)) + ((229 * (x ^ (2 : ℕ))) /. 1728)) + ((x ^ (3 : ℕ)) /. 81))) * (1 + (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹)))) /. ((x /. 2) * ((((((((((((Real.rpow (A ^ (44 : ℕ)) (((12 : ℝ))⁻¹)) + (Real.rpow ((A ^ (40 : ℕ)) * (B ^ (3 : ℕ))) (((12 : ℝ))⁻¹))) + (Real.rpow ((A ^ (36 : ℕ)) * (B ^ (6 : ℕ))) (((12 : ℝ))⁻¹))) + (Real.rpow ((A ^ (32 : ℕ)) * (B ^ (9 : ℕ))) (((12 : ℝ))⁻¹))) + (Real.rpow ((A ^ (28 : ℕ)) * (B ^ (12 : ℕ))) (((12 : ℝ))⁻¹))) + (Real.rpow ((A ^ (24 : ℕ)) * (B ^ (15 : ℕ))) (((12 : ℝ))⁻¹))) + (Real.rpow ((A ^ (20 : ℕ)) * (B ^ (18 : ℕ))) (((12 : ℝ))⁻¹))) + (Real.rpow ((A ^ (16 : ℕ)) * (B ^ (21 : ℕ))) (((12 : ℝ))⁻¹))) + (Real.rpow ((A ^ (12 : ℕ)) * (B ^ (24 : ℕ))) (((12 : ℝ))⁻¹))) + (Real.rpow ((A ^ (8 : ℕ)) * (B ^ (27 : ℕ))) (((12 : ℝ))⁻¹))) + (Real.rpow ((A ^ (4 : ℕ)) * (B ^ (30 : ℕ))) (((12 : ℝ))⁻¹))) + (Real.rpow (B ^ (33 : ℕ)) (((12 : ℝ))⁻¹)))))) (𝓝[≠] 0) (𝓝 L))
  : Tendsto (fun x : ℝ => (((Real.rpow (1 + (x /. 3)) (((3 : ℝ))⁻¹)) - (Real.rpow (1 + (x /. 4)) (((4 : ℝ))⁻¹))) /. (1 - (Real.rpow (1 - (x /. 2)) (((2 : ℝ))⁻¹))))) (𝓝[≠] 0) (𝓝 (7 /. 36)) := by
  sorry

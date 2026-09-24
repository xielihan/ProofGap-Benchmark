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

-- exercise: exercise_2866

theorem proof_gap_exercise_2866_1
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (1 - (x ^ (2 : ℕ))) > 0)
  : ((1 - (x ^ (2 : ℕ))) > 0) → ((1 /. ((1 - (x ^ (2 : ℕ))) * (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) = (Real.rpow (1 - (x ^ (2 : ℕ))) (-(3 /. 2)))) := by
  sorry

theorem proof_gap_exercise_2866_2
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (1 - (x ^ (2 : ℕ))) > 0)
  (h3 : ((1 - (x ^ (2 : ℕ))) > 0) → ((1 /. ((1 - (x ^ (2 : ℕ))) * (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) = (Real.rpow (1 - (x ^ (2 : ℕ))) (-(3 /. 2)))))
  : (Real.rpow (1 - (x ^ (2 : ℕ))) (-(3 /. 2))) = (∑' n, if (0 : ℕ) ≤ n then (((∏ k ∈ Finset.Icc (0 : ℕ) (n - 1), ((-(3 /. 2)) - k)) /. (n)!) * ((-(x ^ (2 : ℕ))) ^ n)) else 0) := by
  sorry

theorem proof_gap_exercise_2866_3
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (1 - (x ^ (2 : ℕ))) > 0)
  (h3 : ((1 - (x ^ (2 : ℕ))) > 0) → ((1 /. ((1 - (x ^ (2 : ℕ))) * (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) = (Real.rpow (1 - (x ^ (2 : ℕ))) (-(3 /. 2)))))
  (h4 : (Real.rpow (1 - (x ^ (2 : ℕ))) (-(3 /. 2))) = (∑' n, if (0 : ℕ) ≤ n then (((∏ k ∈ Finset.Icc (0 : ℕ) (n - 1), ((-(3 /. 2)) - k)) /. (n)!) * ((-(x ^ (2 : ℕ))) ^ n)) else 0))
  : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((((∏ k ∈ Finset.Icc (0 : ℕ) (n - 1), ((-(3 /. 2)) - k)) /. (n)!) * ((-(x ^ (2 : ℕ))) ^ n)) = (((∏ k ∈ Finset.Icc (0 : ℕ) n, ((2 * k) + 1)) /. (∏ k ∈ Finset.Icc (1 : ℕ) n, (2 * k))) * (x ^ (2 * n)))))) := by
  sorry

theorem proof_gap_exercise_2866_4
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (1 - (x ^ (2 : ℕ))) > 0)
  (h3 : ((1 - (x ^ (2 : ℕ))) > 0) → ((1 /. ((1 - (x ^ (2 : ℕ))) * (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) = (Real.rpow (1 - (x ^ (2 : ℕ))) (-(3 /. 2)))))
  (h4 : (Real.rpow (1 - (x ^ (2 : ℕ))) (-(3 /. 2))) = (∑' n, if (0 : ℕ) ≤ n then (((∏ k ∈ Finset.Icc (0 : ℕ) (n - 1), ((-(3 /. 2)) - k)) /. (n)!) * ((-(x ^ (2 : ℕ))) ^ n)) else 0))
  (h5 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((((∏ k ∈ Finset.Icc (0 : ℕ) (n - 1), ((-(3 /. 2)) - k)) /. (n)!) * ((-(x ^ (2 : ℕ))) ^ n)) = (((∏ k ∈ Finset.Icc (0 : ℕ) n, ((2 * k) + 1)) /. (∏ k ∈ Finset.Icc (1 : ℕ) n, (2 * k))) * (x ^ (2 * n)))))))
  : |(x)| < 1 := by
  sorry

theorem proof_gap_exercise_2866_5
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (1 - (x ^ (2 : ℕ))) > 0)
  (h3 : ((1 - (x ^ (2 : ℕ))) > 0) → ((1 /. ((1 - (x ^ (2 : ℕ))) * (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) = (Real.rpow (1 - (x ^ (2 : ℕ))) (-(3 /. 2)))))
  (h4 : (Real.rpow (1 - (x ^ (2 : ℕ))) (-(3 /. 2))) = (∑' n, if (0 : ℕ) ≤ n then (((∏ k ∈ Finset.Icc (0 : ℕ) (n - 1), ((-(3 /. 2)) - k)) /. (n)!) * ((-(x ^ (2 : ℕ))) ^ n)) else 0))
  (h5 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((((∏ k ∈ Finset.Icc (0 : ℕ) (n - 1), ((-(3 /. 2)) - k)) /. (n)!) * ((-(x ^ (2 : ℕ))) ^ n)) = (((∏ k ∈ Finset.Icc (0 : ℕ) n, ((2 * k) + 1)) /. (∏ k ∈ Finset.Icc (1 : ℕ) n, (2 * k))) * (x ^ (2 * n)))))))
  (h6 : |(x)| < 1)
  : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (|(x_1)| < 1)) → ((1 /. ((1 - (x_1 ^ (2 : ℕ))) * (Real.rpow (1 - (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) = (∑' n, if (0 : ℕ) ≤ n then (((∏ k ∈ Finset.Icc (0 : ℕ) n, ((2 * k) + 1)) /. (∏ k ∈ Finset.Icc (1 : ℕ) n, (2 * k))) * (x_1 ^ (2 * n))) else 0)))) := by
  sorry

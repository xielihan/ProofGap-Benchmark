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

-- exercise: exercise_456

theorem proof_gap_exercise_456_1
  (n : ℤ)
  (h1 : n ∈ (Set.univ : Set ℤ))
  (h2 : n ≥ 2)
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t > 0)) ∧ (x = (t ^ ((Int.toNat n))!))) → (t > 0))))) := by
  sorry

theorem proof_gap_exercise_456_2
  (n : ℤ)
  (h1 : n ∈ (Set.univ : Set ℤ))
  (h2 : n ≥ 2)
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t > 0)) ∧ (x = (t ^ ((Int.toNat n))!))) → (t > 0))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t > 0)) ∧ (x = (t ^ ((Int.toNat n))!))) → (((∏ k ∈ Finset.Icc (2 : ℤ) n, (1 - (Real.rpow x (((k : ℝ))⁻¹)))) /. ((1 - x) ^ (n - 1))) = ((∏ k ∈ Finset.Icc (2 : ℤ) n, (1 - (Real.rpow t (((Int.toNat n))! /. k)))) /. ((1 - (t ^ ((Int.toNat n))!)) ^ (n - 1)))))))) := by
  sorry

theorem proof_gap_exercise_456_3
  (n : ℤ)
  (h1 : n ∈ (Set.univ : Set ℤ))
  (h2 : n ≥ 2)
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t > 0)) ∧ (x = (t ^ ((Int.toNat n))!))) → (t > 0))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t > 0)) ∧ (x = (t ^ ((Int.toNat n))!))) → (((∏ k ∈ Finset.Icc (2 : ℤ) n, (1 - (Real.rpow x (((k : ℝ))⁻¹)))) /. ((1 - x) ^ (n - 1))) = ((∏ k ∈ Finset.Icc (2 : ℤ) n, (1 - (Real.rpow t (((Int.toNat n))! /. k)))) /. ((1 - (t ^ ((Int.toNat n))!)) ^ (n - 1)))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t > 0)) ∧ (x = (t ^ ((Int.toNat n))!))) → ((∃ n_div : ℕ, (n_div : ℝ) = (((((Int.toNat n))! /. k) - 1) : ℝ)) ∧ (((∏ k ∈ Finset.Icc (2 : ℤ) n, (1 - (Real.rpow t (((Int.toNat n))! /. k)))) /. ((1 - (t ^ ((Int.toNat n))!)) ^ (n - 1))) = ((∏ k ∈ Finset.Icc (2 : ℤ) n, (∑ j ∈ Finset.Icc (0 : ℕ) ⌊(((((Int.toNat n))! /. k) - 1) : ℝ)⌋₊, (t ^ j))) /. ((∑ j ∈ Finset.Icc (0 : ℕ) (((Int.toNat n))! - 1), (t ^ j)) ^ (n - 1))))))))) := by
  sorry

theorem proof_gap_exercise_456_4
  (n : ℤ)
  (h1 : n ∈ (Set.univ : Set ℤ))
  (h2 : n ≥ 2)
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t > 0)) ∧ (x = (t ^ ((Int.toNat n))!))) → (t > 0))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t > 0)) ∧ (x = (t ^ ((Int.toNat n))!))) → (((∏ k ∈ Finset.Icc (2 : ℤ) n, (1 - (Real.rpow x (((k : ℝ))⁻¹)))) /. ((1 - x) ^ (n - 1))) = ((∏ k ∈ Finset.Icc (2 : ℤ) n, (1 - (Real.rpow t (((Int.toNat n))! /. k)))) /. ((1 - (t ^ ((Int.toNat n))!)) ^ (n - 1)))))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t > 0)) ∧ (x = (t ^ ((Int.toNat n))!))) → (((∏ k ∈ Finset.Icc (2 : ℤ) n, (1 - (Real.rpow t (((Int.toNat n))! /. k)))) /. ((1 - (t ^ ((Int.toNat n))!)) ^ (n - 1))) = ((∏ k ∈ Finset.Icc (2 : ℤ) n, (∑ j ∈ Finset.Icc (0 : ℕ) ⌊(((((Int.toNat n))! /. k) - 1) : ℝ)⌋₊, (t ^ j))) /. ((∑ j ∈ Finset.Icc (0 : ℕ) (((Int.toNat n))! - 1), (t ^ j)) ^ (n - 1)))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), (((((t ∈ (Set.univ : Set ℝ)) ∧ (t > 0)) ∧ (x = (t ^ ((Int.toNat n))!))) ∧ (Tendsto (fun x_1 : ℝ => x_1) (𝓝[≠] 1) (𝓝 1))) → (Tendsto (fun t_1 : ℝ => t_1) (𝓝[≠] 1) (𝓝 1)))))) := by
  sorry

theorem proof_gap_exercise_456_5
  (n : ℤ)
  (h1 : n ∈ (Set.univ : Set ℤ))
  (h2 : n ≥ 2)
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t > 0)) ∧ (x = (t ^ ((Int.toNat n))!))) → (t > 0))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t > 0)) ∧ (x = (t ^ ((Int.toNat n))!))) → (((∏ k ∈ Finset.Icc (2 : ℤ) n, (1 - (Real.rpow x (((k : ℝ))⁻¹)))) /. ((1 - x) ^ (n - 1))) = ((∏ k ∈ Finset.Icc (2 : ℤ) n, (1 - (Real.rpow t (((Int.toNat n))! /. k)))) /. ((1 - (t ^ ((Int.toNat n))!)) ^ (n - 1)))))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), (((((t ∈ (Set.univ : Set ℝ)) ∧ (t > 0)) ∧ (t ≠ 1)) ∧ (x = (t ^ ((Int.toNat n))!))) → (((∏ k ∈ Finset.Icc (2 : ℤ) n, (1 - (Real.rpow t (((Int.toNat n))! /. k)))) /. ((1 - (t ^ ((Int.toNat n))!)) ^ (n - 1))) = ((∏ k ∈ Finset.Icc (2 : ℤ) n, (∑ j ∈ Finset.Icc (0 : ℕ) ⌊(((((Int.toNat n))! /. k) - 1) : ℝ)⌋₊, (t ^ j))) /. ((∑ j ∈ Finset.Icc (0 : ℕ) (((Int.toNat n))! - 1), (t ^ j)) ^ (n - 1)))))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), (((((t ∈ (Set.univ : Set ℝ)) ∧ (t > 0)) ∧ (x = (t ^ ((Int.toNat n))!))) ∧ (Tendsto (fun x_1 : ℝ => x_1) (𝓝[≠] 1) (𝓝 1))) → (Tendsto (fun t_1 : ℝ => t_1) (𝓝[≠] 1) (𝓝 1)))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), (((((t ∈ (Set.univ : Set ℝ)) ∧ (t > 0)) ∧ (x = (t ^ ((Int.toNat n))!))) ∧ (Tendsto (fun x_1 : ℝ => x_1) (𝓝[≠] 1) (𝓝 1))) → ((∃ n_div : ℕ, (n_div : ℝ) = (((((Int.toNat n))! /. k) - 1) : ℝ)) ∧ (Tendsto (fun t_1 : ℝ => ((∏ k ∈ Finset.Icc (2 : ℤ) n, (∑ j ∈ Finset.Icc (0 : ℕ) ⌊(((((Int.toNat n))! /. k) - 1) : ℝ)⌋₊, (t_1 ^ j))) /. ((∑ j ∈ Finset.Icc (0 : ℕ) (((Int.toNat n))! - 1), (t_1 ^ j)) ^ (n - 1)))) (𝓝[≠] 1) (𝓝 ((∏ k ∈ Finset.Icc (2 : ℤ) n, (((Int.toNat n))! /. k)) /. ((((Int.toNat n))! : ℝ) ^ (n - 1)))))))))) := by
  sorry

theorem proof_gap_exercise_456_6
  (n : ℤ)
  (h1 : n ∈ (Set.univ : Set ℤ))
  (h2 : n ≥ 2)
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t > 0)) ∧ (x = (t ^ ((Int.toNat n))!))) → (t > 0))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t > 0)) ∧ (x = (t ^ ((Int.toNat n))!))) → (((∏ k ∈ Finset.Icc (2 : ℤ) n, (1 - (Real.rpow x (((k : ℝ))⁻¹)))) /. ((1 - x) ^ (n - 1))) = ((∏ k ∈ Finset.Icc (2 : ℤ) n, (1 - (Real.rpow t (((Int.toNat n))! /. k)))) /. ((1 - (t ^ ((Int.toNat n))!)) ^ (n - 1)))))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), (((((t ∈ (Set.univ : Set ℝ)) ∧ (t > 0)) ∧ (t ≠ 1)) ∧ (x = (t ^ ((Int.toNat n))!))) → (((∏ k ∈ Finset.Icc (2 : ℤ) n, (1 - (Real.rpow t (((Int.toNat n))! /. k)))) /. ((1 - (t ^ ((Int.toNat n))!)) ^ (n - 1))) = ((∏ k ∈ Finset.Icc (2 : ℤ) n, (∑ j ∈ Finset.Icc (0 : ℕ) ⌊(((((Int.toNat n))! /. k) - 1) : ℝ)⌋₊, (t ^ j))) /. ((∑ j ∈ Finset.Icc (0 : ℕ) (((Int.toNat n))! - 1), (t ^ j)) ^ (n - 1)))))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), (((((t ∈ (Set.univ : Set ℝ)) ∧ (t > 0)) ∧ (x = (t ^ ((Int.toNat n))!))) ∧ (Tendsto (fun x_1 : ℝ => x_1) (𝓝[≠] 1) (𝓝 1))) → (Tendsto (fun t_1 : ℝ => t_1) (𝓝[≠] 1) (𝓝 1)))))))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), (((((t ∈ (Set.univ : Set ℝ)) ∧ (t > 0)) ∧ (x = (t ^ ((Int.toNat n))!))) ∧ (Tendsto (fun x_1 : ℝ => x_1) (𝓝[≠] 1) (𝓝 1))) → (Tendsto (fun t_1 : ℝ => ((∏ k ∈ Finset.Icc (2 : ℤ) n, (∑ j ∈ Finset.Icc (0 : ℕ) ⌊(((((Int.toNat n))! /. k) - 1) : ℝ)⌋₊, (t_1 ^ j))) /. ((∑ j ∈ Finset.Icc (0 : ℕ) (((Int.toNat n))! - 1), (t_1 ^ j)) ^ (n - 1)))) (𝓝[≠] 1) (𝓝 ((∏ k ∈ Finset.Icc (2 : ℤ) n, (((Int.toNat n))! /. k)) /. ((((Int.toNat n))! : ℝ) ^ (n - 1))))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), (((((t ∈ (Set.univ : Set ℝ)) ∧ (t > 0)) ∧ (x = (t ^ ((Int.toNat n))!))) ∧ (Tendsto (fun x_1 : ℝ => x_1) (𝓝[≠] 1) (𝓝 1))) → (((∏ k ∈ Finset.Icc (2 : ℤ) n, (((Int.toNat n))! /. k)) /. ((((Int.toNat n))! : ℝ) ^ (n - 1))) = (1 /. ((Int.toNat n))!)))))) := by
  sorry

theorem proof_gap_exercise_456_7
  (n : ℤ)
  (h1 : n ∈ (Set.univ : Set ℤ))
  (h2 : n ≥ 2)
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t > 0)) ∧ (x = (t ^ ((Int.toNat n))!))) → (t > 0))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t > 0)) ∧ (x = (t ^ ((Int.toNat n))!))) → (((∏ k ∈ Finset.Icc (2 : ℤ) n, (1 - (Real.rpow x (((k : ℝ))⁻¹)))) /. ((1 - x) ^ (n - 1))) = ((∏ k ∈ Finset.Icc (2 : ℤ) n, (1 - (Real.rpow t (((Int.toNat n))! /. k)))) /. ((1 - (t ^ ((Int.toNat n))!)) ^ (n - 1)))))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t > 0)) ∧ (x = (t ^ ((Int.toNat n))!))) → (((∏ k ∈ Finset.Icc (2 : ℤ) n, (1 - (Real.rpow t (((Int.toNat n))! /. k)))) /. ((1 - (t ^ ((Int.toNat n))!)) ^ (n - 1))) = ((∏ k ∈ Finset.Icc (2 : ℤ) n, (∑ j ∈ Finset.Icc (0 : ℕ) ⌊(((((Int.toNat n))! /. k) - 1) : ℝ)⌋₊, (t ^ j))) /. ((∑ j ∈ Finset.Icc (0 : ℕ) (((Int.toNat n))! - 1), (t ^ j)) ^ (n - 1)))))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), (((((t ∈ (Set.univ : Set ℝ)) ∧ (t > 0)) ∧ (x = (t ^ ((Int.toNat n))!))) ∧ (Tendsto (fun x_1 : ℝ => x_1) (𝓝[≠] 1) (𝓝 1))) → (Tendsto (fun t_1 : ℝ => t_1) (𝓝[≠] 1) (𝓝 1)))))))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), (((((t ∈ (Set.univ : Set ℝ)) ∧ (t > 0)) ∧ (x = (t ^ ((Int.toNat n))!))) ∧ (Tendsto (fun x_1 : ℝ => x_1) (𝓝[≠] 1) (𝓝 1))) → (Tendsto (fun t_1 : ℝ => ((∏ k ∈ Finset.Icc (2 : ℤ) n, (∑ j ∈ Finset.Icc (0 : ℕ) ⌊(((((Int.toNat n))! /. k) - 1) : ℝ)⌋₊, (t_1 ^ j))) /. ((∑ j ∈ Finset.Icc (0 : ℕ) (((Int.toNat n))! - 1), (t_1 ^ j)) ^ (n - 1)))) (𝓝[≠] 1) (𝓝 ((∏ k ∈ Finset.Icc (2 : ℤ) n, (((Int.toNat n))! /. k)) /. ((((Int.toNat n))! : ℝ) ^ (n - 1))))))))))
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), (((((t ∈ (Set.univ : Set ℝ)) ∧ (t > 0)) ∧ (x = (t ^ ((Int.toNat n))!))) ∧ (Tendsto (fun x_1 : ℝ => x_1) (𝓝[≠] 1) (𝓝 1))) → (((∏ k ∈ Finset.Icc (2 : ℤ) n, (((Int.toNat n))! /. k)) /. ((((Int.toNat n))! : ℝ) ^ (n - 1))) = (1 /. ((Int.toNat n))!)))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), (((((t ∈ (Set.univ : Set ℝ)) ∧ (t > 0)) ∧ (x = (t ^ ((Int.toNat n))!))) ∧ (Tendsto (fun x_1 : ℝ => x_1) (𝓝[≠] 1) (𝓝 1))) → ((∃ n_div : ℕ, (n_div : ℝ) = (((((Int.toNat n))! /. k) - 1) : ℝ)) ∧ (Tendsto (fun t_1 : ℝ => ((∏ k ∈ Finset.Icc (2 : ℤ) n, (∑ j ∈ Finset.Icc (0 : ℕ) ⌊(((((Int.toNat n))! /. k) - 1) : ℝ)⌋₊, (t_1 ^ j))) /. ((∑ j ∈ Finset.Icc (0 : ℕ) (((Int.toNat n))! - 1), (t_1 ^ j)) ^ (n - 1)))) (𝓝[≠] 1) (𝓝 (1 /. ((Int.toNat n))!)))))))) := by
  sorry

theorem proof_gap_exercise_456_8
  (n : ℤ)
  (h1 : n ∈ (Set.univ : Set ℤ))
  (h2 : n ≥ 2)
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t > 0)) ∧ (x = (t ^ ((Int.toNat n))!))) → (t > 0))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t > 0)) ∧ (x = (t ^ ((Int.toNat n))!))) → (((∏ k ∈ Finset.Icc (2 : ℤ) n, (1 - (Real.rpow x (((k : ℝ))⁻¹)))) /. ((1 - x) ^ (n - 1))) = ((∏ k ∈ Finset.Icc (2 : ℤ) n, (1 - (Real.rpow t (((Int.toNat n))! /. k)))) /. ((1 - (t ^ ((Int.toNat n))!)) ^ (n - 1)))))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), (((((t ∈ (Set.univ : Set ℝ)) ∧ (t > 0)) ∧ (t ≠ 1)) ∧ (x = (t ^ ((Int.toNat n))!))) → (((∏ k ∈ Finset.Icc (2 : ℤ) n, (1 - (Real.rpow t (((Int.toNat n))! /. k)))) /. ((1 - (t ^ ((Int.toNat n))!)) ^ (n - 1))) = ((∏ k ∈ Finset.Icc (2 : ℤ) n, (∑ j ∈ Finset.Icc (0 : ℕ) ⌊(((((Int.toNat n))! /. k) - 1) : ℝ)⌋₊, (t ^ j))) /. ((∑ j ∈ Finset.Icc (0 : ℕ) (((Int.toNat n))! - 1), (t ^ j)) ^ (n - 1)))))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), (((((t ∈ (Set.univ : Set ℝ)) ∧ (t > 0)) ∧ (x = (t ^ ((Int.toNat n))!))) ∧ (Tendsto (fun x_1 : ℝ => x_1) (𝓝[≠] 1) (𝓝 1))) → (Tendsto (fun t_1 : ℝ => t_1) (𝓝[≠] 1) (𝓝 1)))))))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), (((((t ∈ (Set.univ : Set ℝ)) ∧ (t > 0)) ∧ (x = (t ^ ((Int.toNat n))!))) ∧ (Tendsto (fun x_1 : ℝ => x_1) (𝓝[≠] 1) (𝓝 1))) → (Tendsto (fun t_1 : ℝ => ((∏ k ∈ Finset.Icc (2 : ℤ) n, (∑ j ∈ Finset.Icc (0 : ℕ) ⌊(((((Int.toNat n))! /. k) - 1) : ℝ)⌋₊, (t_1 ^ j))) /. ((∑ j ∈ Finset.Icc (0 : ℕ) (((Int.toNat n))! - 1), (t_1 ^ j)) ^ (n - 1)))) (𝓝[≠] 1) (𝓝 ((∏ k ∈ Finset.Icc (2 : ℤ) n, (((Int.toNat n))! /. k)) /. ((((Int.toNat n))! : ℝ) ^ (n - 1))))))))))
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), (((((t ∈ (Set.univ : Set ℝ)) ∧ (t > 0)) ∧ (x = (t ^ ((Int.toNat n))!))) ∧ (Tendsto (fun x_1 : ℝ => x_1) (𝓝[≠] 1) (𝓝 1))) → (((∏ k ∈ Finset.Icc (2 : ℤ) n, (((Int.toNat n))! /. k)) /. ((((Int.toNat n))! : ℝ) ^ (n - 1))) = (1 /. ((Int.toNat n))!)))))))
  (h9 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), (((((t ∈ (Set.univ : Set ℝ)) ∧ (t > 0)) ∧ (x = (t ^ ((Int.toNat n))!))) ∧ (Tendsto (fun x_1 : ℝ => x_1) (𝓝[≠] 1) (𝓝 1))) → (Tendsto (fun t_1 : ℝ => ((∏ k ∈ Finset.Icc (2 : ℤ) n, (∑ j ∈ Finset.Icc (0 : ℕ) ⌊(((((Int.toNat n))! /. k) - 1) : ℝ)⌋₊, (t_1 ^ j))) /. ((∑ j ∈ Finset.Icc (0 : ℕ) (((Int.toNat n))! - 1), (t_1 ^ j)) ^ (n - 1)))) (𝓝[≠] 1) (𝓝 (1 /. ((Int.toNat n))!))))))))
  : Tendsto (fun x : ℝ => ((∏ k ∈ Finset.Icc (2 : ℤ) n, (1 - (Real.rpow x (((k : ℝ))⁻¹)))) /. ((1 - x) ^ (n - 1)))) (𝓝[≠] 1) (𝓝 (1 /. ((Int.toNat n))!)) := by
  sorry

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

-- exercise: exercise_628

theorem proof_gap_exercise_628_1
  (x : ℝ)
  (n : ℕ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  : |((∑ k ∈ Finset.Icc (n + 1) (2 * n), ((x ^ k) /. (k)!)))| ≤ (∑ k ∈ Finset.Icc (n + 1) (2 * n), ((|(x)| ^ k) /. (k)!)) := by
  sorry

theorem proof_gap_exercise_628_2
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |((∑ k ∈ Finset.Icc (n + 1) (2 * n), ((x ^ k) /. (k)!)))| ≤ (∑ k ∈ Finset.Icc (n + 1) (2 * n), ((|(x)| ^ k) /. (k)!)))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) → ((∑ k ∈ Finset.Icc (n + 1) (2 * n), ((|(x)| ^ k) /. (k)!)) ≤ (((|(x)| ^ (n + 1)) /. ((n + 1))!) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (|(x)| ^ i)))))) := by
  sorry

theorem proof_gap_exercise_628_3
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |((∑ k ∈ Finset.Icc (n + 1) (2 * n), ((x ^ k) /. (k)!)))| ≤ (∑ k ∈ Finset.Icc (n + 1) (2 * n), ((|(x)| ^ k) /. (k)!)))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) → ((∑ k ∈ Finset.Icc (n + 1) (2 * n), ((|(x)| ^ k) /. (k)!)) ≤ (((|(x)| ^ (n + 1)) /. ((n + 1))!) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (|(x)| ^ i)))))))
  : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (|(x)| = 1)) → ((((|(x)| ^ (n + 1)) /. ((n + 1))!) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (|(x)| ^ i))) = (n /. ((n + 1))!)))) := by
  sorry

theorem proof_gap_exercise_628_4
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |((∑ k ∈ Finset.Icc (n + 1) (2 * n), ((x ^ k) /. (k)!)))| ≤ (∑ k ∈ Finset.Icc (n + 1) (2 * n), ((|(x)| ^ k) /. (k)!)))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) → ((∑ k ∈ Finset.Icc (n + 1) (2 * n), ((|(x)| ^ k) /. (k)!)) ≤ (((|(x)| ^ (n + 1)) /. ((n + 1))!) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (|(x)| ^ i)))))))
  (h4 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (|(x)| = 1)) → ((((|(x)| ^ (n + 1)) /. ((n + 1))!) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (|(x)| ^ i))) = (n /. ((n + 1))!)))))
  : (|(x)| = 1) → (Tendsto (fun n : ℕ => (n /. ((n + 1))!)) atTop (𝓝 0)) := by
  sorry

theorem proof_gap_exercise_628_5
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |((∑ k ∈ Finset.Icc (n + 1) (2 * n), ((x ^ k) /. (k)!)))| ≤ (∑ k ∈ Finset.Icc (n + 1) (2 * n), ((|(x)| ^ k) /. (k)!)))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) → ((∑ k ∈ Finset.Icc (n + 1) (2 * n), ((|(x)| ^ k) /. (k)!)) ≤ (((|(x)| ^ (n + 1)) /. ((n + 1))!) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (|(x)| ^ i)))))))
  (h4 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (|(x)| = 1)) → ((((|(x)| ^ (n + 1)) /. ((n + 1))!) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (|(x)| ^ i))) = (n /. ((n + 1))!)))))
  (h5 : (|(x)| = 1) → (Tendsto (fun n : ℕ => (n /. ((n + 1))!)) atTop (𝓝 0)))
  : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (|(x)| ≠ 1)) → ((((|(x)| ^ (n + 1)) /. ((n + 1))!) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (|(x)| ^ i))) = ((1 /. (1 - |(x)|)) * (((|(x)| ^ (n + 1)) /. ((n + 1))!) - ((|(x)| /. (n + 1)) * (((|(x)| ^ (2 : ℕ)) ^ n) /. (n)!))))))) := by
  sorry

theorem proof_gap_exercise_628_6
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |((∑ k ∈ Finset.Icc (n + 1) (2 * n), ((x ^ k) /. (k)!)))| ≤ (∑ k ∈ Finset.Icc (n + 1) (2 * n), ((|(x)| ^ k) /. (k)!)))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) → ((∑ k ∈ Finset.Icc (n + 1) (2 * n), ((|(x)| ^ k) /. (k)!)) ≤ (((|(x)| ^ (n + 1)) /. ((n + 1))!) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (|(x)| ^ i)))))))
  (h4 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (|(x)| = 1)) → ((((|(x)| ^ (n + 1)) /. ((n + 1))!) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (|(x)| ^ i))) = (n /. ((n + 1))!)))))
  (h5 : (|(x)| = 1) → (Tendsto (fun n : ℕ => (n /. ((n + 1))!)) atTop (𝓝 0)))
  (h6 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (|(x)| ≠ 1)) → ((((|(x)| ^ (n + 1)) /. ((n + 1))!) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (|(x)| ^ i))) = ((1 /. (1 - |(x)|)) * (((|(x)| ^ (n + 1)) /. ((n + 1))!) - ((|(x)| /. (n + 1)) * (((|(x)| ^ (2 : ℕ)) ^ n) /. (n)!))))))))
  : (|(x)| ≠ 1) → (Tendsto (fun n : ℕ => ((Real.rpow |(x)| (n + 1)) /. ((n + 1))!)) atTop (𝓝 0)) := by
  sorry

theorem proof_gap_exercise_628_7
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |((∑ k ∈ Finset.Icc (n + 1) (2 * n), ((x ^ k) /. (k)!)))| ≤ (∑ k ∈ Finset.Icc (n + 1) (2 * n), ((|(x)| ^ k) /. (k)!)))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) → ((∑ k ∈ Finset.Icc (n + 1) (2 * n), ((|(x)| ^ k) /. (k)!)) ≤ (((|(x)| ^ (n + 1)) /. ((n + 1))!) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (|(x)| ^ i)))))))
  (h4 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (|(x)| = 1)) → ((((|(x)| ^ (n + 1)) /. ((n + 1))!) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (|(x)| ^ i))) = (n /. ((n + 1))!)))))
  (h5 : (|(x)| = 1) → (Tendsto (fun n : ℕ => (n /. ((n + 1))!)) atTop (𝓝 0)))
  (h6 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (|(x)| ≠ 1)) → ((((|(x)| ^ (n + 1)) /. ((n + 1))!) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (|(x)| ^ i))) = ((1 /. (1 - |(x)|)) * (((|(x)| ^ (n + 1)) /. ((n + 1))!) - ((|(x)| /. (n + 1)) * (((|(x)| ^ (2 : ℕ)) ^ n) /. (n)!))))))))
  (h7 : (|(x)| ≠ 1) → (Tendsto (fun n : ℕ => ((Real.rpow |(x)| (n + 1)) /. ((n + 1))!)) atTop (𝓝 0)))
  : (|(x)| ≠ 1) → (Tendsto (fun n : ℕ => ((Real.rpow (|(x)| ^ (2 : ℕ)) n) /. (n)!)) atTop (𝓝 0)) := by
  sorry

theorem proof_gap_exercise_628_8
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |((∑ k ∈ Finset.Icc (n + 1) (2 * n), ((x ^ k) /. (k)!)))| ≤ (∑ k ∈ Finset.Icc (n + 1) (2 * n), ((|(x)| ^ k) /. (k)!)))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) → ((∑ k ∈ Finset.Icc (n + 1) (2 * n), ((|(x)| ^ k) /. (k)!)) ≤ (((|(x)| ^ (n + 1)) /. ((n + 1))!) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (|(x)| ^ i)))))))
  (h4 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (|(x)| = 1)) → ((((|(x)| ^ (n + 1)) /. ((n + 1))!) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (|(x)| ^ i))) = (n /. ((n + 1))!)))))
  (h5 : (|(x)| = 1) → (Tendsto (fun n : ℕ => (n /. ((n + 1))!)) atTop (𝓝 0)))
  (h6 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (|(x)| ≠ 1)) → ((((|(x)| ^ (n + 1)) /. ((n + 1))!) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (|(x)| ^ i))) = ((1 /. (1 - |(x)|)) * (((|(x)| ^ (n + 1)) /. ((n + 1))!) - ((|(x)| /. (n + 1)) * (((|(x)| ^ (2 : ℕ)) ^ n) /. (n)!))))))))
  (h7 : (|(x)| ≠ 1) → (Tendsto (fun n : ℕ => ((Real.rpow |(x)| (n + 1)) /. ((n + 1))!)) atTop (𝓝 0)))
  (h8 : (|(x)| ≠ 1) → (Tendsto (fun n : ℕ => ((Real.rpow (|(x)| ^ (2 : ℕ)) n) /. (n)!)) atTop (𝓝 0)))
  : (|(x)| ≠ 1) → (Tendsto (fun n : ℕ => (((Real.rpow |(x)| (n + 1)) /. ((n + 1))!) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (|(x)| ^ i)))) atTop (𝓝 0)) := by
  sorry

theorem proof_gap_exercise_628_9
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |((∑ k ∈ Finset.Icc (n + 1) (2 * n), ((x ^ k) /. (k)!)))| ≤ (∑ k ∈ Finset.Icc (n + 1) (2 * n), ((|(x)| ^ k) /. (k)!)))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) → ((∑ k ∈ Finset.Icc (n + 1) (2 * n), ((|(x)| ^ k) /. (k)!)) ≤ (((|(x)| ^ (n + 1)) /. ((n + 1))!) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (|(x)| ^ i)))))))
  (h4 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (|(x)| = 1)) → ((((|(x)| ^ (n + 1)) /. ((n + 1))!) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (|(x)| ^ i))) = (n /. ((n + 1))!)))))
  (h5 : (|(x)| = 1) → (Tendsto (fun n : ℕ => (n /. ((n + 1))!)) atTop (𝓝 0)))
  (h6 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (|(x)| ≠ 1)) → ((((|(x)| ^ (n + 1)) /. ((n + 1))!) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (|(x)| ^ i))) = ((1 /. (1 - |(x)|)) * (((|(x)| ^ (n + 1)) /. ((n + 1))!) - ((|(x)| /. (n + 1)) * (((|(x)| ^ (2 : ℕ)) ^ n) /. (n)!))))))))
  (h7 : (|(x)| ≠ 1) → (Tendsto (fun n : ℕ => ((Real.rpow |(x)| (n + 1)) /. ((n + 1))!)) atTop (𝓝 0)))
  (h8 : (|(x)| ≠ 1) → (Tendsto (fun n : ℕ => ((Real.rpow (|(x)| ^ (2 : ℕ)) n) /. (n)!)) atTop (𝓝 0)))
  (h9 : (|(x)| ≠ 1) → (Tendsto (fun n : ℕ => (((Real.rpow |(x)| (n + 1)) /. ((n + 1))!) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (|(x)| ^ i)))) atTop (𝓝 0)))
  : Tendsto (fun n : ℕ => (∑ k ∈ Finset.Icc (n + 1) (2 * n), ((x ^ k) /. (k)!))) atTop (𝓝 0) := by
  sorry

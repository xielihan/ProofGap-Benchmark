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

-- exercise: exercise_430

theorem proof_gap_exercise_430_1
  (x : ℝ)
  (a : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : a ∈ (Set.univ : Set ℝ))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 1)) → (((1 /. n) * (∑ i ∈ Finset.Icc (1 : ℕ) (n - 1), ((x + ((i * a) /. n)) ^ (2 : ℕ)))) = ((1 /. n) * ((((n - 1) * (x ^ (2 : ℕ))) + ((((2 * a) * x) /. n) * (∑ i ∈ Finset.Icc (1 : ℕ) (n - 1), i))) + (((a ^ (2 : ℕ)) /. (n ^ (2 : ℕ))) * (∑ i ∈ Finset.Icc (1 : ℕ) (n - 1), (i ^ (2 : ℕ))))))))) := by
  sorry

theorem proof_gap_exercise_430_2
  (x : ℝ)
  (a : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 1)) → (((1 /. n) * (∑ i ∈ Finset.Icc (1 : ℕ) (n - 1), ((x + ((i * a) /. n)) ^ (2 : ℕ)))) = ((1 /. n) * ((((n - 1) * (x ^ (2 : ℕ))) + ((((2 * a) * x) /. n) * (∑ i ∈ Finset.Icc (1 : ℕ) (n - 1), i))) + (((a ^ (2 : ℕ)) /. (n ^ (2 : ℕ))) * (∑ i ∈ Finset.Icc (1 : ℕ) (n - 1), (i ^ (2 : ℕ))))))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 1)) → ((∑ i ∈ Finset.Icc (1 : ℕ) (n - 1), i) = ((n * (n - 1)) /. 2)))) := by
  sorry

theorem proof_gap_exercise_430_3
  (x : ℝ)
  (a : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 1)) → (((1 /. n) * (∑ i ∈ Finset.Icc (1 : ℕ) (n - 1), ((x + ((i * a) /. n)) ^ (2 : ℕ)))) = ((1 /. n) * ((((n - 1) * (x ^ (2 : ℕ))) + ((((2 * a) * x) /. n) * (∑ i ∈ Finset.Icc (1 : ℕ) (n - 1), i))) + (((a ^ (2 : ℕ)) /. (n ^ (2 : ℕ))) * (∑ i ∈ Finset.Icc (1 : ℕ) (n - 1), (i ^ (2 : ℕ))))))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 1)) → ((∑ i ∈ Finset.Icc (1 : ℕ) (n - 1), i) = ((n * (n - 1)) /. 2)))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 1)) → ((∑ i ∈ Finset.Icc (1 : ℕ) (n - 1), (i ^ (2 : ℕ))) = ((((n - 1) * n) * ((2 * n) - 1)) /. 6)))) := by
  sorry

theorem proof_gap_exercise_430_4
  (x : ℝ)
  (a : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 1)) → (((1 /. n) * (∑ i ∈ Finset.Icc (1 : ℕ) (n - 1), ((x + ((i * a) /. n)) ^ (2 : ℕ)))) = ((1 /. n) * ((((n - 1) * (x ^ (2 : ℕ))) + ((((2 * a) * x) /. n) * (∑ i ∈ Finset.Icc (1 : ℕ) (n - 1), i))) + (((a ^ (2 : ℕ)) /. (n ^ (2 : ℕ))) * (∑ i ∈ Finset.Icc (1 : ℕ) (n - 1), (i ^ (2 : ℕ))))))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 1)) → ((∑ i ∈ Finset.Icc (1 : ℕ) (n - 1), i) = ((n * (n - 1)) /. 2)))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 1)) → ((∑ i ∈ Finset.Icc (1 : ℕ) (n - 1), (i ^ (2 : ℕ))) = ((((n - 1) * n) * ((2 * n) - 1)) /. 6)))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 1)) → (((1 /. n) * (∑ i ∈ Finset.Icc (1 : ℕ) (n - 1), ((x + ((i * a) /. n)) ^ (2 : ℕ)))) = ((1 /. n) * ((((n - 1) * (x ^ (2 : ℕ))) + (((n - 1) * a) * x)) + ((((n - 1) * ((2 * n) - 1)) /. (6 * n)) * (a ^ (2 : ℕ)))))))) := by
  sorry

theorem proof_gap_exercise_430_5
  (x : ℝ)
  (a : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 1)) → (((1 /. n) * (∑ i ∈ Finset.Icc (1 : ℕ) (n - 1), ((x + ((i * a) /. n)) ^ (2 : ℕ)))) = ((1 /. n) * ((((n - 1) * (x ^ (2 : ℕ))) + ((((2 * a) * x) /. n) * (∑ i ∈ Finset.Icc (1 : ℕ) (n - 1), i))) + (((a ^ (2 : ℕ)) /. (n ^ (2 : ℕ))) * (∑ i ∈ Finset.Icc (1 : ℕ) (n - 1), (i ^ (2 : ℕ))))))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 1)) → ((∑ i ∈ Finset.Icc (1 : ℕ) (n - 1), i) = ((n * (n - 1)) /. 2)))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 1)) → ((∑ i ∈ Finset.Icc (1 : ℕ) (n - 1), (i ^ (2 : ℕ))) = ((((n - 1) * n) * ((2 * n) - 1)) /. 6)))))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 1)) → (((1 /. n) * (∑ i ∈ Finset.Icc (1 : ℕ) (n - 1), ((x + ((i * a) /. n)) ^ (2 : ℕ)))) = ((1 /. n) * ((((n - 1) * (x ^ (2 : ℕ))) + (((n - 1) * a) * x)) + ((((n - 1) * ((2 * n) - 1)) /. (6 * n)) * (a ^ (2 : ℕ)))))))))
  : Tendsto (fun n : ℕ => ((1 /. n) * ((((n - 1) * (x ^ (2 : ℕ))) + (((n - 1) * a) * x)) + ((((n - 1) * ((2 * n) - 1)) /. (6 * n)) * (a ^ (2 : ℕ)))))) atTop (𝓝 (((x ^ (2 : ℕ)) + (a * x)) + ((a ^ (2 : ℕ)) /. 3))) := by
  sorry

theorem proof_gap_exercise_430_6
  (x : ℝ)
  (a : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 1)) → (((1 /. n) * (∑ i ∈ Finset.Icc (1 : ℕ) (n - 1), ((x + ((i * a) /. n)) ^ (2 : ℕ)))) = ((1 /. n) * ((((n - 1) * (x ^ (2 : ℕ))) + ((((2 * a) * x) /. n) * (∑ i ∈ Finset.Icc (1 : ℕ) (n - 1), i))) + (((a ^ (2 : ℕ)) /. (n ^ (2 : ℕ))) * (∑ i ∈ Finset.Icc (1 : ℕ) (n - 1), (i ^ (2 : ℕ))))))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 1)) → ((∑ i ∈ Finset.Icc (1 : ℕ) (n - 1), i) = ((n * (n - 1)) /. 2)))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 1)) → ((∑ i ∈ Finset.Icc (1 : ℕ) (n - 1), (i ^ (2 : ℕ))) = ((((n - 1) * n) * ((2 * n) - 1)) /. 6)))))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 1)) → (((1 /. n) * (∑ i ∈ Finset.Icc (1 : ℕ) (n - 1), ((x + ((i * a) /. n)) ^ (2 : ℕ)))) = ((1 /. n) * ((((n - 1) * (x ^ (2 : ℕ))) + (((n - 1) * a) * x)) + ((((n - 1) * ((2 * n) - 1)) /. (6 * n)) * (a ^ (2 : ℕ)))))))))
  (h7 : Tendsto (fun n : ℕ => ((1 /. n) * ((((n - 1) * (x ^ (2 : ℕ))) + (((n - 1) * a) * x)) + ((((n - 1) * ((2 * n) - 1)) /. (6 * n)) * (a ^ (2 : ℕ)))))) atTop (𝓝 (((x ^ (2 : ℕ)) + (a * x)) + ((a ^ (2 : ℕ)) /. 3))))
  : Tendsto (fun n : ℕ => ((1 /. n) * (∑ i ∈ Finset.Icc (1 : ℕ) (n - 1), ((x + ((i * a) /. n)) ^ (2 : ℕ))))) atTop (𝓝 (((x ^ (2 : ℕ)) + (a * x)) + ((a ^ (2 : ℕ)) /. 3))) := by
  sorry

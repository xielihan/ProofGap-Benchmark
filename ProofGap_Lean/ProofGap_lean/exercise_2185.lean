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

-- exercise: exercise_2185

theorem proof_gap_exercise_2185_1
  (f : (ℝ -> ℝ))
  (S : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(1 : ℝ)) 2))) → ((f x) = (x ^ (2 : ℕ))))))
  : ContinuousOn f (Set.Icc (-(1 : ℝ)) 2) := by
  sorry

theorem proof_gap_exercise_2185_2
  (f : (ℝ -> ℝ))
  (S : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(1 : ℝ)) 2))) → ((f x) = (x ^ (2 : ℕ))))))
  (h3 : ContinuousOn f (Set.Icc (-(1 : ℝ)) 2))
  (h4 : h = (3 /. n))
  : (exists (v_uCE_uBE : (ℕ -> ℝ)), (forall (i : ℕ), (((i ∈ (Set.univ : Set ℕ)) ∧ (i ≤ (n - 1))) → ((v_uCE_uBE i) = ((-(1 : ℝ)) + (i * h)))))) := by
  sorry

theorem proof_gap_exercise_2185_3
  (f : (ℝ -> ℝ))
  (S : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(1 : ℝ)) 2))) → ((f x) = (x ^ (2 : ℕ))))))
  (h3 : ContinuousOn f (Set.Icc (-(1 : ℝ)) 2))
  (h4 : h = (3 /. n))
  (h5 : (exists (v_uCE_uBE : (ℕ -> ℝ)), (forall (i : ℕ), (((i ∈ (Set.univ : Set ℕ)) ∧ (i ≤ (n - 1))) → ((v_uCE_uBE i) = ((-(1 : ℝ)) + (i * h)))))))
  : (S n) = (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), ((((-(1 : ℝ)) + (i * h)) ^ (2 : ℕ)) * h)) := by
  sorry

theorem proof_gap_exercise_2185_4
  (f : (ℝ -> ℝ))
  (S : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(1 : ℝ)) 2))) → ((f x) = (x ^ (2 : ℕ))))))
  (h3 : ContinuousOn f (Set.Icc (-(1 : ℝ)) 2))
  (h4 : h = (3 /. n))
  (h5 : (exists (v_uCE_uBE : (ℕ -> ℝ)), (forall (i : ℕ), (((i ∈ (Set.univ : Set ℕ)) ∧ (i ≤ (n - 1))) → ((v_uCE_uBE i) = ((-(1 : ℝ)) + (i * h)))))))
  (h6 : (S n) = (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), ((((-(1 : ℝ)) + (i * h)) ^ (2 : ℕ)) * h)))
  : (S n) = (((n * h) - ((2 * (h ^ (2 : ℕ))) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), i))) + ((h ^ (3 : ℕ)) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (i ^ (2 : ℕ))))) := by
  sorry

theorem proof_gap_exercise_2185_5
  (f : (ℝ -> ℝ))
  (S : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(1 : ℝ)) 2))) → ((f x) = (x ^ (2 : ℕ))))))
  (h3 : ContinuousOn f (Set.Icc (-(1 : ℝ)) 2))
  (h4 : h = (3 /. n))
  (h5 : (exists (v_uCE_uBE : (ℕ -> ℝ)), (forall (i : ℕ), (((i ∈ (Set.univ : Set ℕ)) ∧ (i ≤ (n - 1))) → ((v_uCE_uBE i) = ((-(1 : ℝ)) + (i * h)))))))
  (h6 : (S n) = (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), ((((-(1 : ℝ)) + (i * h)) ^ (2 : ℕ)) * h)))
  (h7 : (S n) = (((n * h) - ((2 * (h ^ (2 : ℕ))) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), i))) + ((h ^ (3 : ℕ)) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (i ^ (2 : ℕ))))))
  : (S n) = (3 + ((9 - (9 * n)) /. (2 * (n ^ (2 : ℕ))))) := by
  sorry

theorem proof_gap_exercise_2185_6
  (f : (ℝ -> ℝ))
  (S : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(1 : ℝ)) 2))) → ((f x) = (x ^ (2 : ℕ))))))
  (h3 : ContinuousOn f (Set.Icc (-(1 : ℝ)) 2))
  (h4 : h = (3 /. n))
  (h5 : (exists (v_uCE_uBE : (ℕ -> ℝ)), (forall (i : ℕ), (((i ∈ (Set.univ : Set ℕ)) ∧ (i ≤ (n - 1))) → ((v_uCE_uBE i) = ((-(1 : ℝ)) + (i * h)))))))
  (h6 : (S n) = (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), ((((-(1 : ℝ)) + (i * h)) ^ (2 : ℕ)) * h)))
  (h7 : (S n) = (((n * h) - ((2 * (h ^ (2 : ℕ))) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), i))) + ((h ^ (3 : ℕ)) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (i ^ (2 : ℕ))))))
  (h8 : (S n) = (3 + ((9 - (9 * n)) /. (2 * (n ^ (2 : ℕ))))))
  : Tendsto (fun n_1 : ℕ => (S n_1)) atTop (𝓝 3) := by
  sorry

theorem proof_gap_exercise_2185_7
  (f : (ℝ -> ℝ))
  (S : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(1 : ℝ)) 2))) → ((f x) = (x ^ (2 : ℕ))))))
  (h3 : ContinuousOn f (Set.Icc (-(1 : ℝ)) 2))
  (h4 : h = (3 /. n))
  (h5 : (exists (v_uCE_uBE : (ℕ -> ℝ)), (forall (i : ℕ), (((i ∈ (Set.univ : Set ℕ)) ∧ (i ≤ (n - 1))) → ((v_uCE_uBE i) = ((-(1 : ℝ)) + (i * h)))))))
  (h6 : (S n) = (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), ((((-(1 : ℝ)) + (i * h)) ^ (2 : ℕ)) * h)))
  (h7 : (S n) = (((n * h) - ((2 * (h ^ (2 : ℕ))) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), i))) + ((h ^ (3 : ℕ)) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (i ^ (2 : ℕ))))))
  (h8 : (S n) = (3 + ((9 - (9 * n)) /. (2 * (n ^ (2 : ℕ))))))
  (h9 : Tendsto (fun n_1 : ℕ => (S n_1)) atTop (𝓝 3))
  : Tendsto (fun n_1 : ℕ => (S n_1)) atTop (𝓝 (∫ x in (-(1 : ℝ))..(2 : ℝ), ((x ^ (2 : ℕ)) * (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_2185_8
  (f : (ℝ -> ℝ))
  (S : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(1 : ℝ)) 2))) → ((f x) = (x ^ (2 : ℕ))))))
  (h3 : ContinuousOn f (Set.Icc (-(1 : ℝ)) 2))
  (h4 : h = (3 /. n))
  (h5 : (exists (v_uCE_uBE : (ℕ -> ℝ)), (forall (i : ℕ), (((i ∈ (Set.univ : Set ℕ)) ∧ (i ≤ (n - 1))) → ((v_uCE_uBE i) = ((-(1 : ℝ)) + (i * h)))))))
  (h6 : (S n) = (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), ((((-(1 : ℝ)) + (i * h)) ^ (2 : ℕ)) * h)))
  (h7 : (S n) = (((n * h) - ((2 * (h ^ (2 : ℕ))) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), i))) + ((h ^ (3 : ℕ)) * (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (i ^ (2 : ℕ))))))
  (h8 : (S n) = (3 + ((9 - (9 * n)) /. (2 * (n ^ (2 : ℕ))))))
  (h9 : Tendsto (fun n_1 : ℕ => (S n_1)) atTop (𝓝 3))
  (h10 : Tendsto (fun n_1 : ℕ => (S n_1)) atTop (𝓝 (∫ x in (-(1 : ℝ))..(2 : ℝ), ((x ^ (2 : ℕ)) * (1 : ℝ)))))
  : (∫ x in (-(1 : ℝ))..(2 : ℝ), ((x ^ (2 : ℕ)) * (1 : ℝ))) = 3 := by
  sorry

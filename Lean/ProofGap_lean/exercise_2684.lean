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

-- exercise: exercise_2684

theorem proof_gap_exercise_2684_1
  (a : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((Real.rpow (-(1 : ℝ)) ((n * (n - 1)) /. 2)) * ((n ^ (100 : ℕ)) /. ((2 : ℕ) ^ n)))))))
  : (∑' n, if (1 : ℕ) ≤ n then |((a n))| else 0) = (∑' n, if (1 : ℕ) ≤ n then ((n ^ (100 : ℕ)) /. ((2 : ℕ) ^ n)) else 0) := by
  sorry

theorem proof_gap_exercise_2684_2
  (a : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((Real.rpow (-(1 : ℝ)) ((n * (n - 1)) /. 2)) * ((n ^ (100 : ℕ)) /. ((2 : ℕ) ^ n)))))))
  (h2 : (∑' n, if (1 : ℕ) ≤ n then |((a n))| else 0) = (∑' n, if (1 : ℕ) ≤ n then ((n ^ (100 : ℕ)) /. ((2 : ℕ) ^ n)) else 0))
  : (∃ L : ℝ, Tendsto (fun n : ℕ => ((1 /. 2) * ((1 + (1 /. n)) ^ (100 : ℕ)))) atTop (𝓝 L) ∧ (Tendsto (fun n : ℕ => ((((n + 1) ^ (100 : ℕ)) /. (Real.rpow (2 : ℝ) (n + 1))) /. ((n ^ (100 : ℕ)) /. (Real.rpow (2 : ℝ) n)))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => ((1 /. 2) * ((1 + (1 /. n)) ^ (100 : ℕ)))))))) := by
  sorry

theorem proof_gap_exercise_2684_3
  (a : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((Real.rpow (-(1 : ℝ)) ((n * (n - 1)) /. 2)) * ((n ^ (100 : ℕ)) /. ((2 : ℕ) ^ n)))))))
  (h2 : (∑' n, if (1 : ℕ) ≤ n then |((a n))| else 0) = (∑' n, if (1 : ℕ) ≤ n then ((n ^ (100 : ℕ)) /. ((2 : ℕ) ^ n)) else 0))
  (h3 : Tendsto (fun n : ℕ => ((((n + 1) ^ (100 : ℕ)) /. (Real.rpow (2 : ℝ) (n + 1))) /. ((n ^ (100 : ℕ)) /. (Real.rpow (2 : ℝ) n)))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => ((1 /. 2) * ((1 + (1 /. n)) ^ (100 : ℕ)))))))
  (h4 : ∃ L : ℝ, Tendsto (fun n : ℕ => ((1 /. 2) * ((1 + (1 /. n)) ^ (100 : ℕ)))) atTop (𝓝 L))
  : Tendsto (fun n : ℕ => ((1 /. 2) * ((1 + (1 /. n)) ^ (100 : ℕ)))) atTop (𝓝 (1 /. 2)) := by
  sorry

theorem proof_gap_exercise_2684_4
  (a : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((Real.rpow (-(1 : ℝ)) ((n * (n - 1)) /. 2)) * ((n ^ (100 : ℕ)) /. ((2 : ℕ) ^ n)))))))
  (h2 : (∑' n, if (1 : ℕ) ≤ n then |((a n))| else 0) = (∑' n, if (1 : ℕ) ≤ n then ((n ^ (100 : ℕ)) /. ((2 : ℕ) ^ n)) else 0))
  (h3 : Tendsto (fun n : ℕ => ((((n + 1) ^ (100 : ℕ)) /. (Real.rpow (2 : ℝ) (n + 1))) /. ((n ^ (100 : ℕ)) /. (Real.rpow (2 : ℝ) n)))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => ((1 /. 2) * ((1 + (1 /. n)) ^ (100 : ℕ)))))))
  (h4 : Tendsto (fun n : ℕ => ((1 /. 2) * ((1 + (1 /. n)) ^ (100 : ℕ)))) atTop (𝓝 (1 /. 2)))
  (h5 : ∃ L : ℝ, Tendsto (fun n : ℕ => ((1 /. 2) * ((1 + (1 /. n)) ^ (100 : ℕ)))) atTop (𝓝 L))
  : Tendsto (fun n : ℕ => ((((n + 1) ^ (100 : ℕ)) /. (Real.rpow (2 : ℝ) (n + 1))) /. ((n ^ (100 : ℕ)) /. (Real.rpow (2 : ℝ) n)))) atTop (𝓝 (1 /. 2)) := by
  sorry

theorem proof_gap_exercise_2684_5
  (a : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((Real.rpow (-(1 : ℝ)) ((n * (n - 1)) /. 2)) * ((n ^ (100 : ℕ)) /. ((2 : ℕ) ^ n)))))))
  (h2 : (∑' n, if (1 : ℕ) ≤ n then |((a n))| else 0) = (∑' n, if (1 : ℕ) ≤ n then ((n ^ (100 : ℕ)) /. ((2 : ℕ) ^ n)) else 0))
  (h3 : Tendsto (fun n : ℕ => ((((n + 1) ^ (100 : ℕ)) /. (Real.rpow (2 : ℝ) (n + 1))) /. ((n ^ (100 : ℕ)) /. (Real.rpow (2 : ℝ) n)))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => ((1 /. 2) * ((1 + (1 /. n)) ^ (100 : ℕ)))))))
  (h4 : Tendsto (fun n : ℕ => ((1 /. 2) * ((1 + (1 /. n)) ^ (100 : ℕ)))) atTop (𝓝 (1 /. 2)))
  (h5 : Tendsto (fun n : ℕ => ((((n + 1) ^ (100 : ℕ)) /. (Real.rpow (2 : ℝ) (n + 1))) /. ((n ^ (100 : ℕ)) /. (Real.rpow (2 : ℝ) n)))) atTop (𝓝 (1 /. 2)))
  (h6 : ∃ L : ℝ, Tendsto (fun n : ℕ => ((1 /. 2) * ((1 + (1 /. n)) ^ (100 : ℕ)))) atTop (𝓝 L))
  : (1 /. 2) < 1 := by
  sorry

theorem proof_gap_exercise_2684_6
  (a : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((Real.rpow (-(1 : ℝ)) ((n * (n - 1)) /. 2)) * ((n ^ (100 : ℕ)) /. ((2 : ℕ) ^ n)))))))
  (h2 : (∑' n, if (1 : ℕ) ≤ n then |((a n))| else 0) = (∑' n, if (1 : ℕ) ≤ n then ((n ^ (100 : ℕ)) /. ((2 : ℕ) ^ n)) else 0))
  (h3 : Tendsto (fun n : ℕ => ((((n + 1) ^ (100 : ℕ)) /. (Real.rpow (2 : ℝ) (n + 1))) /. ((n ^ (100 : ℕ)) /. (Real.rpow (2 : ℝ) n)))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => ((1 /. 2) * ((1 + (1 /. n)) ^ (100 : ℕ)))))))
  (h4 : Tendsto (fun n : ℕ => ((1 /. 2) * ((1 + (1 /. n)) ^ (100 : ℕ)))) atTop (𝓝 (1 /. 2)))
  (h5 : Tendsto (fun n : ℕ => ((((n + 1) ^ (100 : ℕ)) /. (Real.rpow (2 : ℝ) (n + 1))) /. ((n ^ (100 : ℕ)) /. (Real.rpow (2 : ℝ) n)))) atTop (𝓝 (1 /. 2)))
  (h6 : (1 /. 2) < 1)
  (h7 : ∃ L : ℝ, Tendsto (fun n : ℕ => ((1 /. 2) * ((1 + (1 /. n)) ^ (100 : ℕ)))) atTop (𝓝 L))
  : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((n ^ (100 : ℕ)) /. ((2 : ℕ) ^ n)) else 0) := by
  sorry

theorem proof_gap_exercise_2684_7
  (a : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((Real.rpow (-(1 : ℝ)) ((n * (n - 1)) /. 2)) * ((n ^ (100 : ℕ)) /. ((2 : ℕ) ^ n)))))))
  (h2 : (∑' n, if (1 : ℕ) ≤ n then |((a n))| else 0) = (∑' n, if (1 : ℕ) ≤ n then ((n ^ (100 : ℕ)) /. ((2 : ℕ) ^ n)) else 0))
  (h3 : Tendsto (fun n : ℕ => ((((n + 1) ^ (100 : ℕ)) /. (Real.rpow (2 : ℝ) (n + 1))) /. ((n ^ (100 : ℕ)) /. (Real.rpow (2 : ℝ) n)))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => ((1 /. 2) * ((1 + (1 /. n)) ^ (100 : ℕ)))))))
  (h4 : Tendsto (fun n : ℕ => ((1 /. 2) * ((1 + (1 /. n)) ^ (100 : ℕ)))) atTop (𝓝 (1 /. 2)))
  (h5 : Tendsto (fun n : ℕ => ((((n + 1) ^ (100 : ℕ)) /. (Real.rpow (2 : ℝ) (n + 1))) /. ((n ^ (100 : ℕ)) /. (Real.rpow (2 : ℝ) n)))) atTop (𝓝 (1 /. 2)))
  (h6 : (1 /. 2) < 1)
  (h7 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((n ^ (100 : ℕ)) /. ((2 : ℕ) ^ n)) else 0))
  (h8 : ∃ L : ℝ, Tendsto (fun n : ℕ => ((1 /. 2) * ((1 + (1 /. n)) ^ (100 : ℕ)))) atTop (𝓝 L))
  : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0) := by
  sorry

theorem proof_gap_exercise_2684_8
  (a : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((Real.rpow (-(1 : ℝ)) ((n * (n - 1)) /. 2)) * ((n ^ (100 : ℕ)) /. ((2 : ℕ) ^ n)))))))
  (h2 : (∑' n, if (1 : ℕ) ≤ n then |((a n))| else 0) = (∑' n, if (1 : ℕ) ≤ n then ((n ^ (100 : ℕ)) /. ((2 : ℕ) ^ n)) else 0))
  (h3 : Tendsto (fun n : ℕ => ((((n + 1) ^ (100 : ℕ)) /. (Real.rpow (2 : ℝ) (n + 1))) /. ((n ^ (100 : ℕ)) /. (Real.rpow (2 : ℝ) n)))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => ((1 /. 2) * ((1 + (1 /. n)) ^ (100 : ℕ)))))))
  (h4 : Tendsto (fun n : ℕ => ((1 /. 2) * ((1 + (1 /. n)) ^ (100 : ℕ)))) atTop (𝓝 (1 /. 2)))
  (h5 : Tendsto (fun n : ℕ => ((((n + 1) ^ (100 : ℕ)) /. (Real.rpow (2 : ℝ) (n + 1))) /. ((n ^ (100 : ℕ)) /. (Real.rpow (2 : ℝ) n)))) atTop (𝓝 (1 /. 2)))
  (h6 : (1 /. 2) < 1)
  (h7 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((n ^ (100 : ℕ)) /. ((2 : ℕ) ^ n)) else 0))
  (h8 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0))
  (h9 : ∃ L : ℝ, Tendsto (fun n : ℕ => ((1 /. 2) * ((1 + (1 /. n)) ^ (100 : ℕ)))) atTop (𝓝 L))
  : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0) := by
  sorry

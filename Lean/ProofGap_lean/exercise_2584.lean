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

-- exercise: exercise_2584

theorem proof_gap_exercise_2584_1
  (a : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ) (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (n ∈ (Set.univ : Set ℕ))) → ((a n) = (∏ k_1 ∈ Finset.Icc (0 : ℕ) n, (((3 * k_1) + 4) /. ((4 * k_1) + 2)))))))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((a n) ≠ 0))))
  : (∃ L : ℝ, Tendsto (fun n : ℕ => (((3 * n) + 4) /. ((4 * n) + 2))) atTop (𝓝 L) ∧ (Tendsto (fun n : ℕ => ((a (n + 1)) /. (a n))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (((3 * n) + 4) /. ((4 * n) + 2))))))) := by
  sorry

theorem proof_gap_exercise_2584_2
  (a : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ) (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (n ∈ (Set.univ : Set ℕ))) → ((a n) = (∏ k_1 ∈ Finset.Icc (0 : ℕ) n, (((3 * k_1) + 4) /. ((4 * k_1) + 2)))))))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((a n) ≠ 0))))
  (h3 : Tendsto (fun n : ℕ => ((a (n + 1)) /. (a n))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (((3 * n) + 4) /. ((4 * n) + 2))))))
  (h4 : ∃ L : ℝ, Tendsto (fun n : ℕ => (((3 * n) + 4) /. ((4 * n) + 2))) atTop (𝓝 L))
  : Tendsto (fun n : ℕ => (((3 * n) + 4) /. ((4 * n) + 2))) atTop (𝓝 (3 /. 4)) := by
  sorry

theorem proof_gap_exercise_2584_3
  (a : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ) (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (n ∈ (Set.univ : Set ℕ))) → ((a n) = (∏ k_1 ∈ Finset.Icc (0 : ℕ) n, (((3 * k_1) + 4) /. ((4 * k_1) + 2)))))))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((a n) ≠ 0))))
  (h3 : Tendsto (fun n : ℕ => ((a (n + 1)) /. (a n))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (((3 * n) + 4) /. ((4 * n) + 2))))))
  (h4 : Tendsto (fun n : ℕ => (((3 * n) + 4) /. ((4 * n) + 2))) atTop (𝓝 (3 /. 4)))
  (h5 : ∃ L : ℝ, Tendsto (fun n : ℕ => (((3 * n) + 4) /. ((4 * n) + 2))) atTop (𝓝 L))
  : Tendsto (fun n : ℕ => ((a (n + 1)) /. (a n))) atTop (𝓝 (3 /. 4)) := by
  sorry

theorem proof_gap_exercise_2584_4
  (a : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ) (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (n ∈ (Set.univ : Set ℕ))) → ((a n) = (∏ k_1 ∈ Finset.Icc (0 : ℕ) n, (((3 * k_1) + 4) /. ((4 * k_1) + 2)))))))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((a n) ≠ 0))))
  (h3 : Tendsto (fun n : ℕ => ((a (n + 1)) /. (a n))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (((3 * n) + 4) /. ((4 * n) + 2))))))
  (h4 : Tendsto (fun n : ℕ => (((3 * n) + 4) /. ((4 * n) + 2))) atTop (𝓝 (3 /. 4)))
  (h5 : Tendsto (fun n : ℕ => ((a (n + 1)) /. (a n))) atTop (𝓝 (3 /. 4)))
  (h6 : ∃ L : ℝ, Tendsto (fun n : ℕ => (((3 * n) + 4) /. ((4 * n) + 2))) atTop (𝓝 L))
  : (3 /. 4) < 1 := by
  sorry

theorem proof_gap_exercise_2584_5
  (a : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ) (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (n ∈ (Set.univ : Set ℕ))) → ((a n) = (∏ k_1 ∈ Finset.Icc (0 : ℕ) n, (((3 * k_1) + 4) /. ((4 * k_1) + 2)))))))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((a n) ≠ 0))))
  (h3 : Tendsto (fun n : ℕ => ((a (n + 1)) /. (a n))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (((3 * n) + 4) /. ((4 * n) + 2))))))
  (h4 : Tendsto (fun n : ℕ => (((3 * n) + 4) /. ((4 * n) + 2))) atTop (𝓝 (3 /. 4)))
  (h5 : Tendsto (fun n : ℕ => ((a (n + 1)) /. (a n))) atTop (𝓝 (3 /. 4)))
  (h6 : (3 /. 4) < 1)
  (h7 : ∃ L : ℝ, Tendsto (fun n : ℕ => (((3 * n) + 4) /. ((4 * n) + 2))) atTop (𝓝 L))
  : Summable (fun (n : ℕ) => if (0 : ℕ) ≤ n then (a n) else 0) := by
  sorry

theorem proof_gap_exercise_2584_6
  (a : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ) (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (n ∈ (Set.univ : Set ℕ))) → ((a n) = (∏ k_1 ∈ Finset.Icc (0 : ℕ) n, (((3 * k_1) + 4) /. ((4 * k_1) + 2)))))))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((a n) ≠ 0))))
  (h3 : Tendsto (fun n : ℕ => ((a (n + 1)) /. (a n))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (((3 * n) + 4) /. ((4 * n) + 2))))))
  (h4 : Tendsto (fun n : ℕ => (((3 * n) + 4) /. ((4 * n) + 2))) atTop (𝓝 (3 /. 4)))
  (h5 : Tendsto (fun n : ℕ => ((a (n + 1)) /. (a n))) atTop (𝓝 (3 /. 4)))
  (h6 : (3 /. 4) < 1)
  (h7 : Summable (fun (n : ℕ) => if (0 : ℕ) ≤ n then (a n) else 0))
  (h8 : ∃ L : ℝ, Tendsto (fun n : ℕ => (((3 * n) + 4) /. ((4 * n) + 2))) atTop (𝓝 L))
  : Summable (fun (n : ℕ) => if (0 : ℕ) ≤ n then (a n) else 0) := by
  sorry

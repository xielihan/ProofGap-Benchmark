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

-- exercise: exercise_2579

theorem proof_gap_exercise_2579_1
  (a : (ℕ -> ℝ))
  (h1 : True)
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (((n)! ^ (2 : ℕ)) /. ((2 * n))!)))))
  : (∃ L : ℝ, Tendsto (fun n : ℕ => (((((n + 1))! ^ (2 : ℕ)) /. (((2 * n) + 2))!) /. (((n)! ^ (2 : ℕ)) /. ((2 * n))!))) atTop (𝓝 L) ∧ (Tendsto (fun n : ℕ => ((a (n + 1)) /. (a n))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (((((n + 1))! ^ (2 : ℕ)) /. (((2 * n) + 2))!) /. (((n)! ^ (2 : ℕ)) /. ((2 * n))!))))))) := by
  sorry

theorem proof_gap_exercise_2579_2
  (a : (ℕ -> ℝ))
  (h1 : True)
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (((n)! ^ (2 : ℕ)) /. ((2 * n))!)))))
  (h3 : Tendsto (fun n : ℕ => ((a (n + 1)) /. (a n))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (((((n + 1))! ^ (2 : ℕ)) /. (((2 * n) + 2))!) /. (((n)! ^ (2 : ℕ)) /. ((2 * n))!))))))
  (h4 : ∃ L : ℝ, Tendsto (fun n : ℕ => (((((n + 1))! ^ (2 : ℕ)) /. (((2 * n) + 2))!) /. (((n)! ^ (2 : ℕ)) /. ((2 * n))!))) atTop (𝓝 L))
  : (∃ L : ℝ, Tendsto (fun n : ℕ => ((n + 1) /. (2 * ((2 * n) + 1)))) atTop (𝓝 L) ∧ (Tendsto (fun n : ℕ => (((((n + 1))! ^ (2 : ℕ)) /. (((2 * n) + 2))!) /. (((n)! ^ (2 : ℕ)) /. ((2 * n))!))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => ((n + 1) /. (2 * ((2 * n) + 1)))))))) := by
  sorry

theorem proof_gap_exercise_2579_3
  (a : (ℕ -> ℝ))
  (h1 : True)
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (((n)! ^ (2 : ℕ)) /. ((2 * n))!)))))
  (h3 : Tendsto (fun n : ℕ => ((a (n + 1)) /. (a n))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (((((n + 1))! ^ (2 : ℕ)) /. (((2 * n) + 2))!) /. (((n)! ^ (2 : ℕ)) /. ((2 * n))!))))))
  (h4 : Tendsto (fun n : ℕ => (((((n + 1))! ^ (2 : ℕ)) /. (((2 * n) + 2))!) /. (((n)! ^ (2 : ℕ)) /. ((2 * n))!))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => ((n + 1) /. (2 * ((2 * n) + 1)))))))
  (h5 : ∃ L : ℝ, Tendsto (fun n : ℕ => (((((n + 1))! ^ (2 : ℕ)) /. (((2 * n) + 2))!) /. (((n)! ^ (2 : ℕ)) /. ((2 * n))!))) atTop (𝓝 L))
  (h6 : ∃ L : ℝ, Tendsto (fun n : ℕ => ((n + 1) /. (2 * ((2 * n) + 1)))) atTop (𝓝 L))
  : Tendsto (fun n : ℕ => ((n + 1) /. (2 * ((2 * n) + 1)))) atTop (𝓝 (1 /. 4)) := by
  sorry

theorem proof_gap_exercise_2579_4
  (a : (ℕ -> ℝ))
  (h1 : True)
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (((n)! ^ (2 : ℕ)) /. ((2 * n))!)))))
  (h3 : Tendsto (fun n : ℕ => ((a (n + 1)) /. (a n))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (((((n + 1))! ^ (2 : ℕ)) /. (((2 * n) + 2))!) /. (((n)! ^ (2 : ℕ)) /. ((2 * n))!))))))
  (h4 : Tendsto (fun n : ℕ => (((((n + 1))! ^ (2 : ℕ)) /. (((2 * n) + 2))!) /. (((n)! ^ (2 : ℕ)) /. ((2 * n))!))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => ((n + 1) /. (2 * ((2 * n) + 1)))))))
  (h5 : Tendsto (fun n : ℕ => ((n + 1) /. (2 * ((2 * n) + 1)))) atTop (𝓝 (1 /. 4)))
  (h6 : ∃ L : ℝ, Tendsto (fun n : ℕ => (((((n + 1))! ^ (2 : ℕ)) /. (((2 * n) + 2))!) /. (((n)! ^ (2 : ℕ)) /. ((2 * n))!))) atTop (𝓝 L))
  (h7 : ∃ L : ℝ, Tendsto (fun n : ℕ => ((n + 1) /. (2 * ((2 * n) + 1)))) atTop (𝓝 L))
  : Tendsto (fun n : ℕ => ((a (n + 1)) /. (a n))) atTop (𝓝 (1 /. 4)) := by
  sorry

theorem proof_gap_exercise_2579_5
  (a : (ℕ -> ℝ))
  (h1 : True)
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (((n)! ^ (2 : ℕ)) /. ((2 * n))!)))))
  (h3 : Tendsto (fun n : ℕ => ((a (n + 1)) /. (a n))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (((((n + 1))! ^ (2 : ℕ)) /. (((2 * n) + 2))!) /. (((n)! ^ (2 : ℕ)) /. ((2 * n))!))))))
  (h4 : Tendsto (fun n : ℕ => (((((n + 1))! ^ (2 : ℕ)) /. (((2 * n) + 2))!) /. (((n)! ^ (2 : ℕ)) /. ((2 * n))!))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => ((n + 1) /. (2 * ((2 * n) + 1)))))))
  (h5 : Tendsto (fun n : ℕ => ((n + 1) /. (2 * ((2 * n) + 1)))) atTop (𝓝 (1 /. 4)))
  (h6 : Tendsto (fun n : ℕ => ((a (n + 1)) /. (a n))) atTop (𝓝 (1 /. 4)))
  (h7 : ∃ L : ℝ, Tendsto (fun n : ℕ => (((((n + 1))! ^ (2 : ℕ)) /. (((2 * n) + 2))!) /. (((n)! ^ (2 : ℕ)) /. ((2 * n))!))) atTop (𝓝 L))
  (h8 : ∃ L : ℝ, Tendsto (fun n : ℕ => ((n + 1) /. (2 * ((2 * n) + 1)))) atTop (𝓝 L))
  : (1 /. 4) < 1 := by
  sorry

theorem proof_gap_exercise_2579_6
  (a : (ℕ -> ℝ))
  (h1 : True)
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (((n)! ^ (2 : ℕ)) /. ((2 * n))!)))))
  (h3 : Tendsto (fun n : ℕ => ((a (n + 1)) /. (a n))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (((((n + 1))! ^ (2 : ℕ)) /. (((2 * n) + 2))!) /. (((n)! ^ (2 : ℕ)) /. ((2 * n))!))))))
  (h4 : Tendsto (fun n : ℕ => (((((n + 1))! ^ (2 : ℕ)) /. (((2 * n) + 2))!) /. (((n)! ^ (2 : ℕ)) /. ((2 * n))!))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => ((n + 1) /. (2 * ((2 * n) + 1)))))))
  (h5 : Tendsto (fun n : ℕ => ((n + 1) /. (2 * ((2 * n) + 1)))) atTop (𝓝 (1 /. 4)))
  (h6 : Tendsto (fun n : ℕ => ((a (n + 1)) /. (a n))) atTop (𝓝 (1 /. 4)))
  (h7 : (1 /. 4) < 1)
  (h8 : ∃ L : ℝ, Tendsto (fun n : ℕ => (((((n + 1))! ^ (2 : ℕ)) /. (((2 * n) + 2))!) /. (((n)! ^ (2 : ℕ)) /. ((2 * n))!))) atTop (𝓝 L))
  (h9 : ∃ L : ℝ, Tendsto (fun n : ℕ => ((n + 1) /. (2 * ((2 * n) + 1)))) atTop (𝓝 L))
  : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0) := by
  sorry

theorem proof_gap_exercise_2579_7
  (a : (ℕ -> ℝ))
  (h1 : True)
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (((n)! ^ (2 : ℕ)) /. ((2 * n))!)))))
  (h3 : Tendsto (fun n : ℕ => ((a (n + 1)) /. (a n))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (((((n + 1))! ^ (2 : ℕ)) /. (((2 * n) + 2))!) /. (((n)! ^ (2 : ℕ)) /. ((2 * n))!))))))
  (h4 : Tendsto (fun n : ℕ => (((((n + 1))! ^ (2 : ℕ)) /. (((2 * n) + 2))!) /. (((n)! ^ (2 : ℕ)) /. ((2 * n))!))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => ((n + 1) /. (2 * ((2 * n) + 1)))))))
  (h5 : Tendsto (fun n : ℕ => ((n + 1) /. (2 * ((2 * n) + 1)))) atTop (𝓝 (1 /. 4)))
  (h6 : Tendsto (fun n : ℕ => ((a (n + 1)) /. (a n))) atTop (𝓝 (1 /. 4)))
  (h7 : (1 /. 4) < 1)
  (h8 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0))
  (h9 : ∃ L : ℝ, Tendsto (fun n : ℕ => (((((n + 1))! ^ (2 : ℕ)) /. (((2 * n) + 2))!) /. (((n)! ^ (2 : ℕ)) /. ((2 * n))!))) atTop (𝓝 L))
  (h10 : ∃ L : ℝ, Tendsto (fun n : ℕ => ((n + 1) /. (2 * ((2 * n) + 1)))) atTop (𝓝 L))
  : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0) := by
  sorry

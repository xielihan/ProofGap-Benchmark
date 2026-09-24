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

-- exercise: exercise_600

theorem proof_gap_exercise_600_1
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (x + ⌊(x ^ (2 : ℕ))⌋)))))
  : (f (1 : ℝ)) = 2 := by
  sorry

theorem proof_gap_exercise_600_2
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (x + ⌊(x ^ (2 : ℕ))⌋)))))
  (h2 : (f (1 : ℝ)) = 2)
  : (∃ L : ℝ, Tendsto (fun x : ℝ => (x + ⌊(x ^ (2 : ℕ))⌋)) (𝓝[<] 1) (𝓝 L) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[<] 1) (𝓝 ((𝓝[<] 1).limUnder (fun x : ℝ => (x + ⌊(x ^ (2 : ℕ))⌋)))))) := by
  sorry

theorem proof_gap_exercise_600_3
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (x + ⌊(x ^ (2 : ℕ))⌋)))))
  (h2 : (f (1 : ℝ)) = 2)
  (h3 : Tendsto (fun x : ℝ => (f x)) (𝓝[<] 1) (𝓝 ((𝓝[<] 1).limUnder (fun x : ℝ => (x + ⌊(x ^ (2 : ℕ))⌋)))))
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => (x + ⌊(x ^ (2 : ℕ))⌋)) (𝓝[<] 1) (𝓝 L))
  : Tendsto (fun x : ℝ => (x + ⌊(x ^ (2 : ℕ))⌋)) (𝓝[<] 1) (𝓝 1) := by
  sorry

theorem proof_gap_exercise_600_4
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (x + ⌊(x ^ (2 : ℕ))⌋)))))
  (h2 : (f (1 : ℝ)) = 2)
  (h3 : Tendsto (fun x : ℝ => (f x)) (𝓝[<] 1) (𝓝 ((𝓝[<] 1).limUnder (fun x : ℝ => (x + ⌊(x ^ (2 : ℕ))⌋)))))
  (h4 : Tendsto (fun x : ℝ => (x + ⌊(x ^ (2 : ℕ))⌋)) (𝓝[<] 1) (𝓝 1))
  (h5 : ∃ L : ℝ, Tendsto (fun x : ℝ => (x + ⌊(x ^ (2 : ℕ))⌋)) (𝓝[<] 1) (𝓝 L))
  : Tendsto (fun x : ℝ => (f x)) (𝓝[<] 1) (𝓝 1) := by
  sorry

theorem proof_gap_exercise_600_5
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (x + ⌊(x ^ (2 : ℕ))⌋)))))
  (h2 : (f (1 : ℝ)) = 2)
  (h3 : Tendsto (fun x : ℝ => (f x)) (𝓝[<] 1) (𝓝 ((𝓝[<] 1).limUnder (fun x : ℝ => (x + ⌊(x ^ (2 : ℕ))⌋)))))
  (h4 : Tendsto (fun x : ℝ => (x + ⌊(x ^ (2 : ℕ))⌋)) (𝓝[<] 1) (𝓝 1))
  (h5 : Tendsto (fun x : ℝ => (f x)) (𝓝[<] 1) (𝓝 1))
  (h6 : ∃ L : ℝ, Tendsto (fun x : ℝ => (x + ⌊(x ^ (2 : ℕ))⌋)) (𝓝[<] 1) (𝓝 L))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => (x + ⌊(x ^ (2 : ℕ))⌋)) (𝓝[>] 1) (𝓝 L) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[>] 1) (𝓝 ((𝓝[>] 1).limUnder (fun x : ℝ => (x + ⌊(x ^ (2 : ℕ))⌋)))))) := by
  sorry

theorem proof_gap_exercise_600_6
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (x + ⌊(x ^ (2 : ℕ))⌋)))))
  (h2 : (f (1 : ℝ)) = 2)
  (h3 : Tendsto (fun x : ℝ => (f x)) (𝓝[<] 1) (𝓝 ((𝓝[<] 1).limUnder (fun x : ℝ => (x + ⌊(x ^ (2 : ℕ))⌋)))))
  (h4 : Tendsto (fun x : ℝ => (x + ⌊(x ^ (2 : ℕ))⌋)) (𝓝[<] 1) (𝓝 1))
  (h5 : Tendsto (fun x : ℝ => (f x)) (𝓝[<] 1) (𝓝 1))
  (h6 : Tendsto (fun x : ℝ => (f x)) (𝓝[>] 1) (𝓝 ((𝓝[>] 1).limUnder (fun x : ℝ => (x + ⌊(x ^ (2 : ℕ))⌋)))))
  (h7 : ∃ L : ℝ, Tendsto (fun x : ℝ => (x + ⌊(x ^ (2 : ℕ))⌋)) (𝓝[<] 1) (𝓝 L))
  (h8 : ∃ L : ℝ, Tendsto (fun x : ℝ => (x + ⌊(x ^ (2 : ℕ))⌋)) (𝓝[>] 1) (𝓝 L))
  : Tendsto (fun x : ℝ => (x + ⌊(x ^ (2 : ℕ))⌋)) (𝓝[>] 1) (𝓝 2) := by
  sorry

theorem proof_gap_exercise_600_7
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (x + ⌊(x ^ (2 : ℕ))⌋)))))
  (h2 : (f (1 : ℝ)) = 2)
  (h3 : Tendsto (fun x : ℝ => (f x)) (𝓝[<] 1) (𝓝 ((𝓝[<] 1).limUnder (fun x : ℝ => (x + ⌊(x ^ (2 : ℕ))⌋)))))
  (h4 : Tendsto (fun x : ℝ => (x + ⌊(x ^ (2 : ℕ))⌋)) (𝓝[<] 1) (𝓝 1))
  (h5 : Tendsto (fun x : ℝ => (f x)) (𝓝[<] 1) (𝓝 1))
  (h6 : Tendsto (fun x : ℝ => (f x)) (𝓝[>] 1) (𝓝 ((𝓝[>] 1).limUnder (fun x : ℝ => (x + ⌊(x ^ (2 : ℕ))⌋)))))
  (h7 : Tendsto (fun x : ℝ => (x + ⌊(x ^ (2 : ℕ))⌋)) (𝓝[>] 1) (𝓝 2))
  (h8 : ∃ L : ℝ, Tendsto (fun x : ℝ => (x + ⌊(x ^ (2 : ℕ))⌋)) (𝓝[<] 1) (𝓝 L))
  (h9 : ∃ L : ℝ, Tendsto (fun x : ℝ => (x + ⌊(x ^ (2 : ℕ))⌋)) (𝓝[>] 1) (𝓝 L))
  : Tendsto (fun x : ℝ => (f x)) (𝓝[>] 1) (𝓝 2) := by
  sorry

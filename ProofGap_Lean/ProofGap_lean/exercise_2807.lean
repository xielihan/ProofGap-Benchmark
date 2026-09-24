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

-- exercise: exercise_2807

theorem proof_gap_exercise_2807_1
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x < 1)) → ((∑' n, if (1 : ℕ) ≤ n then ((x ^ n) - (x ^ (n + 1))) else 0) = (∑' n, if (1 : ℕ) ≤ n then ((x ^ n) * (1 - x)) else 0)))) := by
  sorry

theorem proof_gap_exercise_2807_2
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x < 1)) → ((∑' n, if (1 : ℕ) ≤ n then ((x ^ n) - (x ^ (n + 1))) else 0) = (∑' n, if (1 : ℕ) ≤ n then ((x ^ n) * (1 - x)) else 0)))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x < 1)) → ((∑' n, if (1 : ℕ) ≤ n then ((x ^ n) * (1 - x)) else 0) = ((x * (1 - x)) /. (1 - x))))) := by
  sorry

theorem proof_gap_exercise_2807_3
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x < 1)) → ((∑' n, if (1 : ℕ) ≤ n then ((x ^ n) - (x ^ (n + 1))) else 0) = (∑' n, if (1 : ℕ) ≤ n then ((x ^ n) * (1 - x)) else 0)))))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x < 1)) → ((∑' n, if (1 : ℕ) ≤ n then ((x ^ n) * (1 - x)) else 0) = ((x * (1 - x)) /. (1 - x))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x < 1)) → (((x * (1 - x)) /. (1 - x)) = x))) := by
  sorry

theorem proof_gap_exercise_2807_4
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x < 1)) → ((∑' n, if (1 : ℕ) ≤ n then ((x ^ n) - (x ^ (n + 1))) else 0) = (∑' n, if (1 : ℕ) ≤ n then ((x ^ n) * (1 - x)) else 0)))))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x < 1)) → ((∑' n, if (1 : ℕ) ≤ n then ((x ^ n) * (1 - x)) else 0) = ((x * (1 - x)) /. (1 - x))))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x < 1)) → (((x * (1 - x)) /. (1 - x)) = x))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x < 1)) → ((∑' n, if (1 : ℕ) ≤ n then ((x ^ n) - (x ^ (n + 1))) else 0) = x))) := by
  sorry

theorem proof_gap_exercise_2807_5
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x < 1)) → ((∑' n, if (1 : ℕ) ≤ n then ((x ^ n) - (x ^ (n + 1))) else 0) = (∑' n, if (1 : ℕ) ≤ n then ((x ^ n) * (1 - x)) else 0)))))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x < 1)) → ((∑' n, if (1 : ℕ) ≤ n then ((x ^ n) * (1 - x)) else 0) = ((x * (1 - x)) /. (1 - x))))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x < 1)) → (((x * (1 - x)) /. (1 - x)) = x))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x < 1)) → ((∑' n, if (1 : ℕ) ≤ n then ((x ^ n) - (x ^ (n + 1))) else 0) = x))))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝 L) ∧ (Tendsto (fun x : ℝ => (∑' n, if (1 : ℕ) ≤ n then ((x ^ n) - (x ^ (n + 1))) else 0)) (𝓝[<] 1) (𝓝 ((𝓝[<] 1).limUnder (fun x : ℝ => x))))) := by
  sorry

theorem proof_gap_exercise_2807_6
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x < 1)) → ((∑' n, if (1 : ℕ) ≤ n then ((x ^ n) - (x ^ (n + 1))) else 0) = (∑' n, if (1 : ℕ) ≤ n then ((x ^ n) * (1 - x)) else 0)))))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x < 1)) → ((∑' n, if (1 : ℕ) ≤ n then ((x ^ n) * (1 - x)) else 0) = ((x * (1 - x)) /. (1 - x))))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x < 1)) → (((x * (1 - x)) /. (1 - x)) = x))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x < 1)) → ((∑' n, if (1 : ℕ) ≤ n then ((x ^ n) - (x ^ (n + 1))) else 0) = x))))
  (h5 : Tendsto (fun x : ℝ => (∑' n, if (1 : ℕ) ≤ n then ((x ^ n) - (x ^ (n + 1))) else 0)) (𝓝[<] 1) (𝓝 ((𝓝[<] 1).limUnder (fun x : ℝ => x))))
  (h6 : ∃ L : ℝ, Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝 L))
  : Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝 1) := by
  sorry

theorem proof_gap_exercise_2807_7
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x < 1)) → ((∑' n, if (1 : ℕ) ≤ n then ((x ^ n) - (x ^ (n + 1))) else 0) = (∑' n, if (1 : ℕ) ≤ n then ((x ^ n) * (1 - x)) else 0)))))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x < 1)) → ((∑' n, if (1 : ℕ) ≤ n then ((x ^ n) * (1 - x)) else 0) = ((x * (1 - x)) /. (1 - x))))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x < 1)) → (((x * (1 - x)) /. (1 - x)) = x))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x < 1)) → ((∑' n, if (1 : ℕ) ≤ n then ((x ^ n) - (x ^ (n + 1))) else 0) = x))))
  (h5 : Tendsto (fun x : ℝ => (∑' n, if (1 : ℕ) ≤ n then ((x ^ n) - (x ^ (n + 1))) else 0)) (𝓝[<] 1) (𝓝 ((𝓝[<] 1).limUnder (fun x : ℝ => x))))
  (h6 : Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝 1))
  (h7 : ∃ L : ℝ, Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝 L))
  : Tendsto (fun x : ℝ => (∑' n, if (1 : ℕ) ≤ n then ((x ^ n) - (x ^ (n + 1))) else 0)) (𝓝[<] 1) (𝓝 1) := by
  sorry

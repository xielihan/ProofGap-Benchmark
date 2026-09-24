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

-- exercise: exercise_2726

theorem proof_gap_exercise_2726_1
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((x ^ n) /. (1 + (x ^ (2 * n))))))))
  : (|(x)| < 1) → (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (|((a n))| ≤ (|(x)| ^ n)))) := by
  sorry

theorem proof_gap_exercise_2726_2
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((x ^ n) /. (1 + (x ^ (2 * n))))))))
  (h3 : (|(x)| < 1) → (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (|((a n))| ≤ (|(x)| ^ n)))))
  : (|(x)| < 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (|(x)| ^ n) else 0)) := by
  sorry

theorem proof_gap_exercise_2726_3
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((x ^ n) /. (1 + (x ^ (2 * n))))))))
  (h3 : (|(x)| < 1) → (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (|((a n))| ≤ (|(x)| ^ n)))))
  (h4 : (|(x)| < 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (|(x)| ^ n) else 0)))
  : (|(x)| < 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0)) := by
  sorry

theorem proof_gap_exercise_2726_4
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((x ^ n) /. (1 + (x ^ (2 * n))))))))
  (h3 : (|(x)| < 1) → (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (|((a n))| ≤ (|(x)| ^ n)))))
  (h4 : (|(x)| < 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (|(x)| ^ n) else 0)))
  (h5 : (|(x)| < 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0)))
  : (|(x)| = 1) → (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (|((a n))| = (1 /. 2)))) := by
  sorry

theorem proof_gap_exercise_2726_5
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((x ^ n) /. (1 + (x ^ (2 * n))))))))
  (h3 : (|(x)| < 1) → (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (|((a n))| ≤ (|(x)| ^ n)))))
  (h4 : (|(x)| < 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (|(x)| ^ n) else 0)))
  (h5 : (|(x)| < 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0)))
  (h6 : (|(x)| = 1) → (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (|((a n))| = (1 /. 2)))))
  : (|(x)| = 1) → (Not (Tendsto (fun n : ℕ => |((a n))|) atTop (𝓝 0))) := by
  sorry

theorem proof_gap_exercise_2726_6
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((x ^ n) /. (1 + (x ^ (2 * n))))))))
  (h3 : (|(x)| < 1) → (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (|((a n))| ≤ (|(x)| ^ n)))))
  (h4 : (|(x)| < 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (|(x)| ^ n) else 0)))
  (h5 : (|(x)| < 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0)))
  (h6 : (|(x)| = 1) → (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (|((a n))| = (1 /. 2)))))
  (h7 : (|(x)| = 1) → (Not (Tendsto (fun n : ℕ => |((a n))|) atTop (𝓝 0))))
  : (|(x)| = 1) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)) := by
  sorry

theorem proof_gap_exercise_2726_7
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((x ^ n) /. (1 + (x ^ (2 * n))))))))
  (h3 : (|(x)| < 1) → (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (|((a n))| ≤ (|(x)| ^ n)))))
  (h4 : (|(x)| < 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (|(x)| ^ n) else 0)))
  (h5 : (|(x)| < 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0)))
  (h6 : (|(x)| = 1) → (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (|((a n))| = (1 /. 2)))))
  (h7 : (|(x)| = 1) → (Not (Tendsto (fun n : ℕ => |((a n))|) atTop (𝓝 0))))
  (h8 : (|(x)| = 1) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)))
  : (|(x)| > 1) → (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (((1 /. x) ^ n) /. (1 + ((1 /. x) ^ (2 * n))))))) := by
  sorry

theorem proof_gap_exercise_2726_8
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((x ^ n) /. (1 + (x ^ (2 * n))))))))
  (h3 : (|(x)| < 1) → (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (|((a n))| ≤ (|(x)| ^ n)))))
  (h4 : (|(x)| < 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (|(x)| ^ n) else 0)))
  (h5 : (|(x)| < 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0)))
  (h6 : (|(x)| = 1) → (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (|((a n))| = (1 /. 2)))))
  (h7 : (|(x)| = 1) → (Not (Tendsto (fun n : ℕ => |((a n))|) atTop (𝓝 0))))
  (h8 : (|(x)| = 1) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)))
  (h9 : (|(x)| > 1) → (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (((1 /. x) ^ n) /. (1 + ((1 /. x) ^ (2 * n))))))))
  : (|(x)| > 1) → (|((1 /. x))| < 1) := by
  sorry

theorem proof_gap_exercise_2726_9
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((x ^ n) /. (1 + (x ^ (2 * n))))))))
  (h3 : (|(x)| < 1) → (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (|((a n))| ≤ (|(x)| ^ n)))))
  (h4 : (|(x)| < 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (|(x)| ^ n) else 0)))
  (h5 : (|(x)| < 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0)))
  (h6 : (|(x)| = 1) → (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (|((a n))| = (1 /. 2)))))
  (h7 : (|(x)| = 1) → (Not (Tendsto (fun n : ℕ => |((a n))|) atTop (𝓝 0))))
  (h8 : (|(x)| = 1) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)))
  (h9 : (|(x)| > 1) → (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (((1 /. x) ^ n) /. (1 + ((1 /. x) ^ (2 * n))))))))
  (h10 : (|(x)| > 1) → (|((1 /. x))| < 1))
  : (|(x)| > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0)) := by
  sorry

theorem proof_gap_exercise_2726_10
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((x ^ n) /. (1 + (x ^ (2 * n))))))))
  (h3 : (|(x)| < 1) → (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (|((a n))| ≤ (|(x)| ^ n)))))
  (h4 : (|(x)| < 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (|(x)| ^ n) else 0)))
  (h5 : (|(x)| < 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0)))
  (h6 : (|(x)| = 1) → (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (|((a n))| = (1 /. 2)))))
  (h7 : (|(x)| = 1) → (Not (Tendsto (fun n : ℕ => |((a n))|) atTop (𝓝 0))))
  (h8 : (|(x)| = 1) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)))
  (h9 : (|(x)| > 1) → (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (((1 /. x) ^ n) /. (1 + ((1 /. x) ^ (2 * n))))))))
  (h10 : (|(x)| > 1) → (|((1 /. x))| < 1))
  (h11 : (|(x)| > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0)))
  : (x ∈ ({x_1 | (x_1 ∈ (Set.univ : Set ℝ)) ∧ (|(x_1)| ≠ 1)})) ↔ (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)) := by
  sorry

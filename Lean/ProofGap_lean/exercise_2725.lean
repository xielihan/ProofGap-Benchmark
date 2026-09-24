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

-- exercise: exercise_2725

theorem proof_gap_exercise_2725_1
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (((x * (x + n)) /. n) ^ n)))))
  : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((x ^ n) * ((1 + (x /. n)) ^ n))))) := by
  sorry

theorem proof_gap_exercise_2725_2
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (((x * (x + n)) /. n) ^ n)))))
  (h3 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((x ^ n) * ((1 + (x /. n)) ^ n))))))
  : (|(x)| > 1) → (Tendsto (fun n : ℕ => ((a n) : EReal)) atTop (𝓝 ⊤)) := by
  sorry

theorem proof_gap_exercise_2725_3
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (((x * (x + n)) /. n) ^ n)))))
  (h3 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((x ^ n) * ((1 + (x /. n)) ^ n))))))
  (h4 : (|(x)| > 1) → (Tendsto (fun n : ℕ => ((a n) : EReal)) atTop (𝓝 ⊤)))
  : (|(x)| > 1) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)) := by
  sorry

theorem proof_gap_exercise_2725_4
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (((x * (x + n)) /. n) ^ n)))))
  (h3 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((x ^ n) * ((1 + (x /. n)) ^ n))))))
  (h4 : (|(x)| > 1) → (Tendsto (fun n : ℕ => ((a n) : EReal)) atTop (𝓝 ⊤)))
  (h5 : (|(x)| > 1) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)))
  : (|(x)| = 1) → (Tendsto (fun n : ℕ => |((a n))|) atTop (𝓝 (Real.exp x))) := by
  sorry

theorem proof_gap_exercise_2725_5
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (((x * (x + n)) /. n) ^ n)))))
  (h3 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((x ^ n) * ((1 + (x /. n)) ^ n))))))
  (h4 : (|(x)| > 1) → (Tendsto (fun n : ℕ => ((a n) : EReal)) atTop (𝓝 ⊤)))
  (h5 : (|(x)| > 1) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)))
  (h6 : (|(x)| = 1) → (Tendsto (fun n : ℕ => |((a n))|) atTop (𝓝 (Real.exp x))))
  : (|(x)| = 1) → ((Real.exp x) ≠ 0) := by
  sorry

theorem proof_gap_exercise_2725_6
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (((x * (x + n)) /. n) ^ n)))))
  (h3 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((x ^ n) * ((1 + (x /. n)) ^ n))))))
  (h4 : (|(x)| > 1) → (Tendsto (fun n : ℕ => ((a n) : EReal)) atTop (𝓝 ⊤)))
  (h5 : (|(x)| > 1) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)))
  (h6 : (|(x)| = 1) → (Tendsto (fun n : ℕ => |((a n))|) atTop (𝓝 (Real.exp x))))
  (h7 : (|(x)| = 1) → ((Real.exp x) ≠ 0))
  : (|(x)| = 1) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)) := by
  sorry

theorem proof_gap_exercise_2725_7
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (((x * (x + n)) /. n) ^ n)))))
  (h3 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((x ^ n) * ((1 + (x /. n)) ^ n))))))
  (h4 : (|(x)| > 1) → (Tendsto (fun n : ℕ => ((a n) : EReal)) atTop (𝓝 ⊤)))
  (h5 : (|(x)| > 1) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)))
  (h6 : (|(x)| = 1) → (Tendsto (fun n : ℕ => |((a n))|) atTop (𝓝 (Real.exp x))))
  (h7 : (|(x)| = 1) → ((Real.exp x) ≠ 0))
  (h8 : (|(x)| = 1) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)))
  : (|(x)| < 1) → (∃ L : ℝ, Tendsto (fun n : ℕ => (|(x)| * |((1 + (x /. n)))|)) atTop (𝓝 L) ∧ (Tendsto (fun n : ℕ => (Real.rpow |((a n))| ((n)⁻¹))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (|(x)| * |((1 + (x /. n)))|)))))) := by
  sorry

theorem proof_gap_exercise_2725_8
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (((x * (x + n)) /. n) ^ n)))))
  (h3 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((x ^ n) * ((1 + (x /. n)) ^ n))))))
  (h4 : (|(x)| > 1) → (Tendsto (fun n : ℕ => ((a n) : EReal)) atTop (𝓝 ⊤)))
  (h5 : (|(x)| > 1) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)))
  (h6 : (|(x)| = 1) → (Tendsto (fun n : ℕ => |((a n))|) atTop (𝓝 (Real.exp x))))
  (h7 : (|(x)| = 1) → ((Real.exp x) ≠ 0))
  (h8 : (|(x)| = 1) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)))
  (h9 : (|(x)| < 1) → (Tendsto (fun n : ℕ => (Real.rpow |((a n))| ((n)⁻¹))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (|(x)| * |((1 + (x /. n)))|))))))
  (h10 : ∃ L : ℝ, Tendsto (fun n : ℕ => (|(x)| * |((1 + (x /. n)))|)) atTop (𝓝 L))
  : (|(x)| < 1) → (Tendsto (fun n : ℕ => (|(x)| * |((1 + (x /. n)))|)) atTop (𝓝 |(x)|)) := by
  sorry

theorem proof_gap_exercise_2725_9
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (((x * (x + n)) /. n) ^ n)))))
  (h3 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((x ^ n) * ((1 + (x /. n)) ^ n))))))
  (h4 : (|(x)| > 1) → (Tendsto (fun n : ℕ => ((a n) : EReal)) atTop (𝓝 ⊤)))
  (h5 : (|(x)| > 1) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)))
  (h6 : (|(x)| = 1) → (Tendsto (fun n : ℕ => |((a n))|) atTop (𝓝 (Real.exp x))))
  (h7 : (|(x)| = 1) → ((Real.exp x) ≠ 0))
  (h8 : (|(x)| = 1) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)))
  (h9 : (|(x)| < 1) → (Tendsto (fun n : ℕ => (Real.rpow |((a n))| ((n)⁻¹))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (|(x)| * |((1 + (x /. n)))|))))))
  (h10 : (|(x)| < 1) → (Tendsto (fun n : ℕ => (|(x)| * |((1 + (x /. n)))|)) atTop (𝓝 |(x)|)))
  (h11 : ∃ L : ℝ, Tendsto (fun n : ℕ => (|(x)| * |((1 + (x /. n)))|)) atTop (𝓝 L))
  : (|(x)| < 1) → (Tendsto (fun n : ℕ => (Real.rpow |((a n))| ((n)⁻¹))) atTop (𝓝 |(x)|)) := by
  sorry

theorem proof_gap_exercise_2725_10
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (((x * (x + n)) /. n) ^ n)))))
  (h3 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((x ^ n) * ((1 + (x /. n)) ^ n))))))
  (h4 : (|(x)| > 1) → (Tendsto (fun n : ℕ => ((a n) : EReal)) atTop (𝓝 ⊤)))
  (h5 : (|(x)| > 1) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)))
  (h6 : (|(x)| = 1) → (Tendsto (fun n : ℕ => |((a n))|) atTop (𝓝 (Real.exp x))))
  (h7 : (|(x)| = 1) → ((Real.exp x) ≠ 0))
  (h8 : (|(x)| = 1) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)))
  (h9 : (|(x)| < 1) → (Tendsto (fun n : ℕ => (Real.rpow |((a n))| ((n)⁻¹))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (|(x)| * |((1 + (x /. n)))|))))))
  (h10 : (|(x)| < 1) → (Tendsto (fun n : ℕ => (|(x)| * |((1 + (x /. n)))|)) atTop (𝓝 |(x)|)))
  (h11 : (|(x)| < 1) → (Tendsto (fun n : ℕ => (Real.rpow |((a n))| ((n)⁻¹))) atTop (𝓝 |(x)|)))
  (h12 : ∃ L : ℝ, Tendsto (fun n : ℕ => (|(x)| * |((1 + (x /. n)))|)) atTop (𝓝 L))
  : (|(x)| < 1) → (|(x)| < 1) := by
  sorry

theorem proof_gap_exercise_2725_11
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (((x * (x + n)) /. n) ^ n)))))
  (h3 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((x ^ n) * ((1 + (x /. n)) ^ n))))))
  (h4 : (|(x)| > 1) → (Tendsto (fun n : ℕ => ((a n) : EReal)) atTop (𝓝 ⊤)))
  (h5 : (|(x)| > 1) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)))
  (h6 : (|(x)| = 1) → (Tendsto (fun n : ℕ => |((a n))|) atTop (𝓝 (Real.exp x))))
  (h7 : (|(x)| = 1) → ((Real.exp x) ≠ 0))
  (h8 : (|(x)| = 1) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)))
  (h9 : (|(x)| < 1) → (Tendsto (fun n : ℕ => (Real.rpow |((a n))| ((n)⁻¹))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (|(x)| * |((1 + (x /. n)))|))))))
  (h10 : (|(x)| < 1) → (Tendsto (fun n : ℕ => (|(x)| * |((1 + (x /. n)))|)) atTop (𝓝 |(x)|)))
  (h11 : (|(x)| < 1) → (Tendsto (fun n : ℕ => (Real.rpow |((a n))| ((n)⁻¹))) atTop (𝓝 |(x)|)))
  (h12 : (|(x)| < 1) → (|(x)| < 1))
  (h13 : ∃ L : ℝ, Tendsto (fun n : ℕ => (|(x)| * |((1 + (x /. n)))|)) atTop (𝓝 L))
  : (|(x)| < 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0)) := by
  sorry

theorem proof_gap_exercise_2725_12
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (((x * (x + n)) /. n) ^ n)))))
  (h3 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((x ^ n) * ((1 + (x /. n)) ^ n))))))
  (h4 : (|(x)| > 1) → (Tendsto (fun n : ℕ => ((a n) : EReal)) atTop (𝓝 ⊤)))
  (h5 : (|(x)| > 1) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)))
  (h6 : (|(x)| = 1) → (Tendsto (fun n : ℕ => |((a n))|) atTop (𝓝 (Real.exp x))))
  (h7 : (|(x)| = 1) → ((Real.exp x) ≠ 0))
  (h8 : (|(x)| = 1) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)))
  (h9 : (|(x)| < 1) → (Tendsto (fun n : ℕ => (Real.rpow |((a n))| ((n)⁻¹))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (|(x)| * |((1 + (x /. n)))|))))))
  (h10 : (|(x)| < 1) → (Tendsto (fun n : ℕ => (|(x)| * |((1 + (x /. n)))|)) atTop (𝓝 |(x)|)))
  (h11 : (|(x)| < 1) → (Tendsto (fun n : ℕ => (Real.rpow |((a n))| ((n)⁻¹))) atTop (𝓝 |(x)|)))
  (h12 : (|(x)| < 1) → (|(x)| < 1))
  (h13 : (|(x)| < 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0)))
  (h14 : ∃ L : ℝ, Tendsto (fun n : ℕ => (|(x)| * |((1 + (x /. n)))|)) atTop (𝓝 L))
  : (x ∈ ({x_1 | (x_1 ∈ (Set.univ : Set ℝ)) ∧ (|(x_1)| < 1)})) ↔ (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)) := by
  sorry

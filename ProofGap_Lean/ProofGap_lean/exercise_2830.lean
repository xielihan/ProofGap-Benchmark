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

-- exercise: exercise_2830

theorem proof_gap_exercise_2830_1
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (1 /. ((2 : ℕ) ^ n))))))
  : Tendsto (fun n : ℕ => (Real.rpow (a n) ((n)⁻¹))) atTop (𝓝 (1 /. 2)) := by
  sorry

theorem proof_gap_exercise_2830_2
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (1 /. ((2 : ℕ) ^ n))))))
  (h3 : Tendsto (fun n : ℕ => (Real.rpow (a n) ((n)⁻¹))) atTop (𝓝 (1 /. 2)))
  : Tendsto (fun n : ℕ => (Real.rpow (1 /. 2) ((n)⁻¹))) atTop (𝓝 1) := by
  sorry

theorem proof_gap_exercise_2830_3
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (1 /. ((2 : ℕ) ^ n))))))
  (h3 : Tendsto (fun n : ℕ => (Real.rpow (a n) ((n)⁻¹))) atTop (𝓝 (1 /. 2)))
  (h4 : Tendsto (fun n : ℕ => (Real.rpow (1 /. 2) ((n)⁻¹))) atTop (𝓝 1))
  : (lpRadiusOfConvergence a) = 1 := by
  sorry

theorem proof_gap_exercise_2830_4
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (1 /. ((2 : ℕ) ^ n))))))
  (h3 : Tendsto (fun n : ℕ => (Real.rpow (a n) ((n)⁻¹))) atTop (𝓝 (1 /. 2)))
  (h4 : Tendsto (fun n : ℕ => (Real.rpow (1 /. 2) ((n)⁻¹))) atTop (𝓝 1))
  (h5 : (lpRadiusOfConvergence a) = 1)
  : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (|(x_1)| < 1)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((x_1 ^ (n ^ (2 : ℕ))) /. ((2 : ℕ) ^ n)) else 0)))) := by
  sorry

theorem proof_gap_exercise_2830_5
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (1 /. ((2 : ℕ) ^ n))))))
  (h3 : Tendsto (fun n : ℕ => (Real.rpow (a n) ((n)⁻¹))) atTop (𝓝 (1 /. 2)))
  (h4 : Tendsto (fun n : ℕ => (Real.rpow (1 /. 2) ((n)⁻¹))) atTop (𝓝 1))
  (h5 : (lpRadiusOfConvergence a) = 1)
  (h6 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (|(x_1)| < 1)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((x_1 ^ (n ^ (2 : ℕ))) /. ((2 : ℕ) ^ n)) else 0)))))
  : (|(x)| = 1) → ((∑' n, if (1 : ℕ) ≤ n then |(((x ^ (n ^ (2 : ℕ))) /. ((2 : ℕ) ^ n)))| else 0) = (∑' n, if (1 : ℕ) ≤ n then (1 /. ((2 : ℕ) ^ n)) else 0)) := by
  sorry

theorem proof_gap_exercise_2830_6
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (1 /. ((2 : ℕ) ^ n))))))
  (h3 : Tendsto (fun n : ℕ => (Real.rpow (a n) ((n)⁻¹))) atTop (𝓝 (1 /. 2)))
  (h4 : Tendsto (fun n : ℕ => (Real.rpow (1 /. 2) ((n)⁻¹))) atTop (𝓝 1))
  (h5 : (lpRadiusOfConvergence a) = 1)
  (h6 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (|(x_1)| < 1)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((x_1 ^ (n ^ (2 : ℕ))) /. ((2 : ℕ) ^ n)) else 0)))))
  (h7 : (|(x)| = 1) → ((∑' n, if (1 : ℕ) ≤ n then |(((x ^ (n ^ (2 : ℕ))) /. ((2 : ℕ) ^ n)))| else 0) = (∑' n, if (1 : ℕ) ≤ n then (1 /. ((2 : ℕ) ^ n)) else 0)))
  : (|(x)| = 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. ((2 : ℕ) ^ n)) else 0)) := by
  sorry

theorem proof_gap_exercise_2830_7
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (1 /. ((2 : ℕ) ^ n))))))
  (h3 : Tendsto (fun n : ℕ => (Real.rpow (a n) ((n)⁻¹))) atTop (𝓝 (1 /. 2)))
  (h4 : Tendsto (fun n : ℕ => (Real.rpow (1 /. 2) ((n)⁻¹))) atTop (𝓝 1))
  (h5 : (lpRadiusOfConvergence a) = 1)
  (h6 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (|(x_1)| < 1)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((x_1 ^ (n ^ (2 : ℕ))) /. ((2 : ℕ) ^ n)) else 0)))))
  (h7 : (|(x)| = 1) → ((∑' n, if (1 : ℕ) ≤ n then |(((x ^ (n ^ (2 : ℕ))) /. ((2 : ℕ) ^ n)))| else 0) = (∑' n, if (1 : ℕ) ≤ n then (1 /. ((2 : ℕ) ^ n)) else 0)))
  (h8 : (|(x)| = 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. ((2 : ℕ) ^ n)) else 0)))
  : (|(x)| = 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖(((x ^ (n ^ (2 : ℕ))) /. ((2 : ℕ) ^ n)))‖ else 0)) := by
  sorry

theorem proof_gap_exercise_2830_8
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (1 /. ((2 : ℕ) ^ n))))))
  (h3 : Tendsto (fun n : ℕ => (Real.rpow (a n) ((n)⁻¹))) atTop (𝓝 (1 /. 2)))
  (h4 : Tendsto (fun n : ℕ => (Real.rpow (1 /. 2) ((n)⁻¹))) atTop (𝓝 1))
  (h5 : (lpRadiusOfConvergence a) = 1)
  (h6 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (|(x_1)| < 1)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((x_1 ^ (n ^ (2 : ℕ))) /. ((2 : ℕ) ^ n)) else 0)))))
  (h7 : (|(x)| = 1) → ((∑' n, if (1 : ℕ) ≤ n then |(((x ^ (n ^ (2 : ℕ))) /. ((2 : ℕ) ^ n)))| else 0) = (∑' n, if (1 : ℕ) ≤ n then (1 /. ((2 : ℕ) ^ n)) else 0)))
  (h8 : (|(x)| = 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. ((2 : ℕ) ^ n)) else 0)))
  (h9 : (|(x)| = 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖(((x ^ (n ^ (2 : ℕ))) /. ((2 : ℕ) ^ n)))‖ else 0)))
  : (x ∈ (Set.Icc (-(1 : ℝ)) 1)) ↔ (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((a n) * (x ^ (n ^ (2 : ℕ)))) else 0)) := by
  sorry

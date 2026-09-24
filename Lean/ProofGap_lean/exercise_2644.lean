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

-- exercise: exercise_2644

theorem proof_gap_exercise_2644_1
  (u : (ℕ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : a > 0)
  (h4 : b > 0)
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((n ^ (2 * n)) /. ((Real.rpow (n + a) (n + b)) * (Real.rpow (n + b) (n + a))))))))
  : Tendsto (fun n : ℕ => ((u n) /. (1 /. (Real.rpow n (a + b))))) atTop (𝓝 (Real.exp (-(a + b)))) := by
  sorry

theorem proof_gap_exercise_2644_2
  (u : (ℕ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : a > 0)
  (h4 : b > 0)
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((n ^ (2 * n)) /. ((Real.rpow (n + a) (n + b)) * (Real.rpow (n + b) (n + a))))))))
  (h6 : Tendsto (fun n : ℕ => ((u n) /. (1 /. (Real.rpow n (a + b))))) atTop (𝓝 (Real.exp (-(a + b)))))
  : ((a + b) > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) (a + b))) else 0)) := by
  sorry

theorem proof_gap_exercise_2644_3
  (u : (ℕ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : a > 0)
  (h4 : b > 0)
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((n ^ (2 * n)) /. ((Real.rpow (n + a) (n + b)) * (Real.rpow (n + b) (n + a))))))))
  (h6 : Tendsto (fun n : ℕ => ((u n) /. (1 /. (Real.rpow n (a + b))))) atTop (𝓝 (Real.exp (-(a + b)))))
  (h7 : ((a + b) > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) (a + b))) else 0)))
  : ((a + b) > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (u n) else 0)) := by
  sorry

theorem proof_gap_exercise_2644_4
  (u : (ℕ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : a > 0)
  (h4 : b > 0)
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((n ^ (2 * n)) /. ((Real.rpow (n + a) (n + b)) * (Real.rpow (n + b) (n + a))))))))
  (h6 : Tendsto (fun n : ℕ => ((u n) /. (1 /. (Real.rpow n (a + b))))) atTop (𝓝 (Real.exp (-(a + b)))))
  (h7 : ((a + b) > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) (a + b))) else 0)))
  (h8 : ((a + b) > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (u n) else 0)))
  : ((a + b) ≤ 1) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) (a + b))) else 0)) := by
  sorry

theorem proof_gap_exercise_2644_5
  (u : (ℕ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : a > 0)
  (h4 : b > 0)
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((n ^ (2 * n)) /. ((Real.rpow (n + a) (n + b)) * (Real.rpow (n + b) (n + a))))))))
  (h6 : Tendsto (fun n : ℕ => ((u n) /. (1 /. (Real.rpow n (a + b))))) atTop (𝓝 (Real.exp (-(a + b)))))
  (h7 : ((a + b) > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) (a + b))) else 0)))
  (h8 : ((a + b) > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (u n) else 0)))
  (h9 : ((a + b) ≤ 1) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) (a + b))) else 0)))
  : ((a + b) ≤ 1) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (u n) else 0)) := by
  sorry

theorem proof_gap_exercise_2644_6
  (u : (ℕ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : a > 0)
  (h4 : b > 0)
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((n ^ (2 * n)) /. ((Real.rpow (n + a) (n + b)) * (Real.rpow (n + b) (n + a))))))))
  (h6 : Tendsto (fun n : ℕ => ((u n) /. (1 /. (Real.rpow n (a + b))))) atTop (𝓝 (Real.exp (-(a + b)))))
  (h7 : ((a + b) > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) (a + b))) else 0)))
  (h8 : ((a + b) > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (u n) else 0)))
  (h9 : ((a + b) ≤ 1) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) (a + b))) else 0)))
  (h10 : ((a + b) ≤ 1) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (u n) else 0)))
  : ((a, b) ∈ ({p : ℝ × ℝ | (((((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2 ∈ (Set.univ : Set ℝ))) ∧ (p.1 > 0)) ∧ (p.2 > 0)) ∧ ((p.1 + p.2) > 1))})) ↔ (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (u n) else 0)) := by
  sorry

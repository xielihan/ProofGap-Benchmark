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

-- exercise: exercise_2604

theorem proof_gap_exercise_2604_1
  (a : (ℕ -> ℝ))
  (p : ℝ)
  (q : ℝ)
  (k : ℕ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : q ∈ (Set.univ : Set ℝ))
  (h3 : k ∈ (Set.univ : Set ℕ))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((Real.rpow ((∏ k_1 ∈ Finset.Icc (1 : ℕ) n, ((2 * k_1) - 1)) /. (∏ k_1 ∈ Finset.Icc (1 : ℕ) n, (2 * k_1))) p) * (1 /. (Real.rpow (n : ℝ) q)))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((a n) /. (a (n + 1))) = ((Real.rpow (((2 * n) + 2) /. ((2 * n) + 1)) p) * (Real.rpow ((n + 1) /. n) q))))) := by
  sorry

theorem proof_gap_exercise_2604_2
  (a : (ℕ -> ℝ))
  (p : ℝ)
  (q : ℝ)
  (k : ℕ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : q ∈ (Set.univ : Set ℝ))
  (h3 : k ∈ (Set.univ : Set ℕ))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((Real.rpow ((∏ k_1 ∈ Finset.Icc (1 : ℕ) n, ((2 * k_1) - 1)) /. (∏ k_1 ∈ Finset.Icc (1 : ℕ) n, (2 * k_1))) p) * (1 /. (Real.rpow (n : ℝ) q)))))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((a n) /. (a (n + 1))) = ((Real.rpow (((2 * n) + 2) /. ((2 * n) + 1)) p) * (Real.rpow ((n + 1) /. n) q))))))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => ((((Real.rpow ((2 + (2 * x)) /. (2 + x)) p) * (Real.rpow (1 + x) q)) - 1) /. x)) (𝓝[≠] 0) (𝓝 L) ∧ (Tendsto (fun n : ℕ => (n * (((a n) /. (a (n + 1))) - 1))) atTop (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((Real.rpow ((2 + (2 * x)) /. (2 + x)) p) * (Real.rpow (1 + x) q)) - 1) /. x)))))) := by
  sorry

theorem proof_gap_exercise_2604_3
  (a : (ℕ -> ℝ))
  (p : ℝ)
  (q : ℝ)
  (k : ℕ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : q ∈ (Set.univ : Set ℝ))
  (h3 : k ∈ (Set.univ : Set ℕ))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((Real.rpow ((∏ k_1 ∈ Finset.Icc (1 : ℕ) n, ((2 * k_1) - 1)) /. (∏ k_1 ∈ Finset.Icc (1 : ℕ) n, (2 * k_1))) p) * (1 /. (Real.rpow (n : ℝ) q)))))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((a n) /. (a (n + 1))) = ((Real.rpow (((2 * n) + 2) /. ((2 * n) + 1)) p) * (Real.rpow ((n + 1) /. n) q))))))
  (h6 : Tendsto (fun n : ℕ => (n * (((a n) /. (a (n + 1))) - 1))) atTop (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((Real.rpow ((2 + (2 * x)) /. (2 + x)) p) * (Real.rpow (1 + x) q)) - 1) /. x)))))
  (h7 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((((Real.rpow ((2 + (2 * x)) /. (2 + x)) p) * (Real.rpow (1 + x) q)) - 1) /. x)) (𝓝[≠] 0) (𝓝 L))
  : Tendsto (fun x : ℝ => ((((Real.rpow ((2 + (2 * x)) /. (2 + x)) p) * (Real.rpow (1 + x) q)) - 1) /. x)) (𝓝[≠] 0) (𝓝 (q + (p /. 2))) := by
  sorry

theorem proof_gap_exercise_2604_4
  (a : (ℕ -> ℝ))
  (p : ℝ)
  (q : ℝ)
  (k : ℕ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : q ∈ (Set.univ : Set ℝ))
  (h3 : k ∈ (Set.univ : Set ℕ))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((Real.rpow ((∏ k_1 ∈ Finset.Icc (1 : ℕ) n, ((2 * k_1) - 1)) /. (∏ k_1 ∈ Finset.Icc (1 : ℕ) n, (2 * k_1))) p) * (1 /. (Real.rpow (n : ℝ) q)))))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((a n) /. (a (n + 1))) = ((Real.rpow (((2 * n) + 2) /. ((2 * n) + 1)) p) * (Real.rpow ((n + 1) /. n) q))))))
  (h6 : Tendsto (fun n : ℕ => (n * (((a n) /. (a (n + 1))) - 1))) atTop (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((Real.rpow ((2 + (2 * x)) /. (2 + x)) p) * (Real.rpow (1 + x) q)) - 1) /. x)))))
  (h7 : Tendsto (fun x : ℝ => ((((Real.rpow ((2 + (2 * x)) /. (2 + x)) p) * (Real.rpow (1 + x) q)) - 1) /. x)) (𝓝[≠] 0) (𝓝 (q + (p /. 2))))
  (h8 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((((Real.rpow ((2 + (2 * x)) /. (2 + x)) p) * (Real.rpow (1 + x) q)) - 1) /. x)) (𝓝[≠] 0) (𝓝 L))
  : Tendsto (fun n : ℕ => (n * (((a n) /. (a (n + 1))) - 1))) atTop (𝓝 (q + (p /. 2))) := by
  sorry

theorem proof_gap_exercise_2604_5
  (a : (ℕ -> ℝ))
  (p : ℝ)
  (q : ℝ)
  (k : ℕ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : q ∈ (Set.univ : Set ℝ))
  (h3 : k ∈ (Set.univ : Set ℕ))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((Real.rpow ((∏ k_1 ∈ Finset.Icc (1 : ℕ) n, ((2 * k_1) - 1)) /. (∏ k_1 ∈ Finset.Icc (1 : ℕ) n, (2 * k_1))) p) * (1 /. (Real.rpow (n : ℝ) q)))))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((a n) /. (a (n + 1))) = ((Real.rpow (((2 * n) + 2) /. ((2 * n) + 1)) p) * (Real.rpow ((n + 1) /. n) q))))))
  (h6 : Tendsto (fun n : ℕ => (n * (((a n) /. (a (n + 1))) - 1))) atTop (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((Real.rpow ((2 + (2 * x)) /. (2 + x)) p) * (Real.rpow (1 + x) q)) - 1) /. x)))))
  (h7 : Tendsto (fun x : ℝ => ((((Real.rpow ((2 + (2 * x)) /. (2 + x)) p) * (Real.rpow (1 + x) q)) - 1) /. x)) (𝓝[≠] 0) (𝓝 (q + (p /. 2))))
  (h8 : Tendsto (fun n : ℕ => (n * (((a n) /. (a (n + 1))) - 1))) atTop (𝓝 (q + (p /. 2))))
  (h9 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((((Real.rpow ((2 + (2 * x)) /. (2 + x)) p) * (Real.rpow (1 + x) q)) - 1) /. x)) (𝓝[≠] 0) (𝓝 L))
  : ((q + (p /. 2)) > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)) := by
  sorry

theorem proof_gap_exercise_2604_6
  (a : (ℕ -> ℝ))
  (p : ℝ)
  (q : ℝ)
  (k : ℕ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : q ∈ (Set.univ : Set ℝ))
  (h3 : k ∈ (Set.univ : Set ℕ))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((Real.rpow ((∏ k_1 ∈ Finset.Icc (1 : ℕ) n, ((2 * k_1) - 1)) /. (∏ k_1 ∈ Finset.Icc (1 : ℕ) n, (2 * k_1))) p) * (1 /. (Real.rpow (n : ℝ) q)))))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((a n) /. (a (n + 1))) = ((Real.rpow (((2 * n) + 2) /. ((2 * n) + 1)) p) * (Real.rpow ((n + 1) /. n) q))))))
  (h6 : Tendsto (fun n : ℕ => (n * (((a n) /. (a (n + 1))) - 1))) atTop (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((Real.rpow ((2 + (2 * x)) /. (2 + x)) p) * (Real.rpow (1 + x) q)) - 1) /. x)))))
  (h7 : Tendsto (fun x : ℝ => ((((Real.rpow ((2 + (2 * x)) /. (2 + x)) p) * (Real.rpow (1 + x) q)) - 1) /. x)) (𝓝[≠] 0) (𝓝 (q + (p /. 2))))
  (h8 : Tendsto (fun n : ℕ => (n * (((a n) /. (a (n + 1))) - 1))) atTop (𝓝 (q + (p /. 2))))
  (h9 : ((q + (p /. 2)) > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)))
  (h10 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((((Real.rpow ((2 + (2 * x)) /. (2 + x)) p) * (Real.rpow (1 + x) q)) - 1) /. x)) (𝓝[≠] 0) (𝓝 L))
  : ((p, q) ∈ ({p_1 : ℝ × ℝ | (p_1.1 ∈ (Set.univ : Set ℝ)) ∧ (p_1.2 ∈ (Set.univ : Set ℝ)) ∧ ((p_1.2 + (p_1.1 /. 2)) > 1)})) ↔ (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)) := by
  sorry

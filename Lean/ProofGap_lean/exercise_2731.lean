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

-- exercise: exercise_2731

theorem proof_gap_exercise_2731_1
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (((n + x) ^ n) /. (Real.rpow (n : ℝ) (n + x)))))))
  : (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > N)) → ((a n) > 0))))) := by
  sorry

theorem proof_gap_exercise_2731_2
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (((n + x) ^ n) /. (Real.rpow (n : ℝ) (n + x)))))))
  (h3 : (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > N)) → ((a n) > 0))))))
  : (∃ L : ℝ, Tendsto (fun n : ℕ => (Real.rpow (1 + (x /. n)) n)) atTop (𝓝 L) ∧ (Tendsto (fun n : ℕ => ((a n) /. (1 /. (Real.rpow n x)))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (Real.rpow (1 + (x /. n)) n)))))) := by
  sorry

theorem proof_gap_exercise_2731_3
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (((n + x) ^ n) /. (Real.rpow (n : ℝ) (n + x)))))))
  (h3 : (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > N)) → ((a n) > 0))))))
  (h4 : Tendsto (fun n : ℕ => ((a n) /. (1 /. (Real.rpow n x)))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (Real.rpow (1 + (x /. n)) n)))))
  (h5 : ∃ L : ℝ, Tendsto (fun n : ℕ => (Real.rpow (1 + (x /. n)) n)) atTop (𝓝 L))
  : Tendsto (fun n : ℕ => (Real.rpow (1 + (x /. n)) n)) atTop (𝓝 (Real.exp x)) := by
  sorry

theorem proof_gap_exercise_2731_4
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (((n + x) ^ n) /. (Real.rpow (n : ℝ) (n + x)))))))
  (h3 : (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > N)) → ((a n) > 0))))))
  (h4 : Tendsto (fun n : ℕ => ((a n) /. (1 /. (Real.rpow n x)))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (Real.rpow (1 + (x /. n)) n)))))
  (h5 : Tendsto (fun n : ℕ => (Real.rpow (1 + (x /. n)) n)) atTop (𝓝 (Real.exp x)))
  (h6 : ∃ L : ℝ, Tendsto (fun n : ℕ => (Real.rpow (1 + (x /. n)) n)) atTop (𝓝 L))
  : Tendsto (fun n : ℕ => ((a n) /. (1 /. (Real.rpow n x)))) atTop (𝓝 (Real.exp x)) := by
  sorry

theorem proof_gap_exercise_2731_5
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (((n + x) ^ n) /. (Real.rpow (n : ℝ) (n + x)))))))
  (h3 : (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > N)) → ((a n) > 0))))))
  (h4 : Tendsto (fun n : ℕ => ((a n) /. (1 /. (Real.rpow n x)))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (Real.rpow (1 + (x /. n)) n)))))
  (h5 : Tendsto (fun n : ℕ => (Real.rpow (1 + (x /. n)) n)) atTop (𝓝 (Real.exp x)))
  (h6 : Tendsto (fun n : ℕ => ((a n) /. (1 /. (Real.rpow n x)))) atTop (𝓝 (Real.exp x)))
  (h7 : ∃ L : ℝ, Tendsto (fun n : ℕ => (Real.rpow (1 + (x /. n)) n)) atTop (𝓝 L))
  : (x > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) x)) else 0)) := by
  sorry

theorem proof_gap_exercise_2731_6
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (((n + x) ^ n) /. (Real.rpow (n : ℝ) (n + x)))))))
  (h3 : (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > N)) → ((a n) > 0))))))
  (h4 : Tendsto (fun n : ℕ => ((a n) /. (1 /. (Real.rpow n x)))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (Real.rpow (1 + (x /. n)) n)))))
  (h5 : Tendsto (fun n : ℕ => (Real.rpow (1 + (x /. n)) n)) atTop (𝓝 (Real.exp x)))
  (h6 : Tendsto (fun n : ℕ => ((a n) /. (1 /. (Real.rpow n x)))) atTop (𝓝 (Real.exp x)))
  (h7 : (x > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) x)) else 0)))
  (h8 : ∃ L : ℝ, Tendsto (fun n : ℕ => (Real.rpow (1 + (x /. n)) n)) atTop (𝓝 L))
  : (x > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0)) := by
  sorry

theorem proof_gap_exercise_2731_7
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (((n + x) ^ n) /. (Real.rpow (n : ℝ) (n + x)))))))
  (h3 : (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > N)) → ((a n) > 0))))))
  (h4 : Tendsto (fun n : ℕ => ((a n) /. (1 /. (Real.rpow n x)))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (Real.rpow (1 + (x /. n)) n)))))
  (h5 : Tendsto (fun n : ℕ => (Real.rpow (1 + (x /. n)) n)) atTop (𝓝 (Real.exp x)))
  (h6 : Tendsto (fun n : ℕ => ((a n) /. (1 /. (Real.rpow n x)))) atTop (𝓝 (Real.exp x)))
  (h7 : (x > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) x)) else 0)))
  (h8 : (x > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0)))
  (h9 : ∃ L : ℝ, Tendsto (fun n : ℕ => (Real.rpow (1 + (x /. n)) n)) atTop (𝓝 L))
  : (x ≤ 1) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) x)) else 0)) := by
  sorry

theorem proof_gap_exercise_2731_8
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (((n + x) ^ n) /. (Real.rpow (n : ℝ) (n + x)))))))
  (h3 : (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > N)) → ((a n) > 0))))))
  (h4 : Tendsto (fun n : ℕ => ((a n) /. (1 /. (Real.rpow n x)))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (Real.rpow (1 + (x /. n)) n)))))
  (h5 : Tendsto (fun n : ℕ => (Real.rpow (1 + (x /. n)) n)) atTop (𝓝 (Real.exp x)))
  (h6 : Tendsto (fun n : ℕ => ((a n) /. (1 /. (Real.rpow n x)))) atTop (𝓝 (Real.exp x)))
  (h7 : (x > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) x)) else 0)))
  (h8 : (x > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0)))
  (h9 : (x ≤ 1) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) x)) else 0)))
  (h10 : ∃ L : ℝ, Tendsto (fun n : ℕ => (Real.rpow (1 + (x /. n)) n)) atTop (𝓝 L))
  : (x ≤ 1) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)) := by
  sorry

theorem proof_gap_exercise_2731_9
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (((n + x) ^ n) /. (Real.rpow (n : ℝ) (n + x)))))))
  (h3 : (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > N)) → ((a n) > 0))))))
  (h4 : Tendsto (fun n : ℕ => ((a n) /. (1 /. (Real.rpow n x)))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (Real.rpow (1 + (x /. n)) n)))))
  (h5 : Tendsto (fun n : ℕ => (Real.rpow (1 + (x /. n)) n)) atTop (𝓝 (Real.exp x)))
  (h6 : Tendsto (fun n : ℕ => ((a n) /. (1 /. (Real.rpow n x)))) atTop (𝓝 (Real.exp x)))
  (h7 : (x > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) x)) else 0)))
  (h8 : (x > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0)))
  (h9 : (x ≤ 1) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) x)) else 0)))
  (h10 : (x ≤ 1) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)))
  (h11 : ∃ L : ℝ, Tendsto (fun n : ℕ => (Real.rpow (1 + (x /. n)) n)) atTop (𝓝 L))
  : (x ∈ ({x_1 | (x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 1)})) ↔ (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)) := by
  sorry

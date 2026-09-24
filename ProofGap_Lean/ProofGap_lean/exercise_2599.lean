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

-- exercise: exercise_2599

theorem proof_gap_exercise_2599_1
  (u : (ℕ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (d : ℝ)
  (k : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : d ∈ (Set.univ : Set ℝ))
  (h4 : k ∈ (Set.univ : Set ℕ))
  (h5 : a > 0)
  (h6 : b > 0)
  (h7 : d > 0)
  (h8 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((∏ k_1 ∈ Finset.Icc (0 : ℕ) (n - 1), (a + (k_1 * d))) /. (∏ k_1 ∈ Finset.Icc (0 : ℕ) (n - 1), (b + (k_1 * d))))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((u n) /. (u (n + 1))) = ((b + (n * d)) /. (a + (n * d)))))) := by
  sorry

theorem proof_gap_exercise_2599_2
  (u : (ℕ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (d : ℝ)
  (k : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : d ∈ (Set.univ : Set ℝ))
  (h4 : k ∈ (Set.univ : Set ℕ))
  (h5 : a > 0)
  (h6 : b > 0)
  (h7 : d > 0)
  (h8 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((∏ k_1 ∈ Finset.Icc (0 : ℕ) (n - 1), (a + (k_1 * d))) /. (∏ k_1 ∈ Finset.Icc (0 : ℕ) (n - 1), (b + (k_1 * d))))))))
  (h9 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((u n) /. (u (n + 1))) = ((b + (n * d)) /. (a + (n * d)))))))
  : (∃ L : ℝ, Tendsto (fun n : ℕ => (n * (((b + (n * d)) /. (a + (n * d))) - 1))) atTop (𝓝 L) ∧ (Tendsto (fun n : ℕ => (n * (((u n) /. (u (n + 1))) - 1))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (n * (((b + (n * d)) /. (a + (n * d))) - 1))))))) := by
  sorry

theorem proof_gap_exercise_2599_3
  (u : (ℕ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (d : ℝ)
  (k : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : d ∈ (Set.univ : Set ℝ))
  (h4 : k ∈ (Set.univ : Set ℕ))
  (h5 : a > 0)
  (h6 : b > 0)
  (h7 : d > 0)
  (h8 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((∏ k_1 ∈ Finset.Icc (0 : ℕ) (n - 1), (a + (k_1 * d))) /. (∏ k_1 ∈ Finset.Icc (0 : ℕ) (n - 1), (b + (k_1 * d))))))))
  (h9 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((u n) /. (u (n + 1))) = ((b + (n * d)) /. (a + (n * d)))))))
  (h10 : Tendsto (fun n : ℕ => (n * (((u n) /. (u (n + 1))) - 1))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (n * (((b + (n * d)) /. (a + (n * d))) - 1))))))
  (h11 : ∃ L : ℝ, Tendsto (fun n : ℕ => (n * (((b + (n * d)) /. (a + (n * d))) - 1))) atTop (𝓝 L))
  : (∃ L : ℝ, Tendsto (fun n : ℕ => (((b - a) * n) /. (a + (n * d)))) atTop (𝓝 L) ∧ (Tendsto (fun n : ℕ => (n * (((b + (n * d)) /. (a + (n * d))) - 1))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (((b - a) * n) /. (a + (n * d)))))))) := by
  sorry

theorem proof_gap_exercise_2599_4
  (u : (ℕ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (d : ℝ)
  (k : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : d ∈ (Set.univ : Set ℝ))
  (h4 : k ∈ (Set.univ : Set ℕ))
  (h5 : a > 0)
  (h6 : b > 0)
  (h7 : d > 0)
  (h8 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((∏ k_1 ∈ Finset.Icc (0 : ℕ) (n - 1), (a + (k_1 * d))) /. (∏ k_1 ∈ Finset.Icc (0 : ℕ) (n - 1), (b + (k_1 * d))))))))
  (h9 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((u n) /. (u (n + 1))) = ((b + (n * d)) /. (a + (n * d)))))))
  (h10 : Tendsto (fun n : ℕ => (n * (((u n) /. (u (n + 1))) - 1))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (n * (((b + (n * d)) /. (a + (n * d))) - 1))))))
  (h11 : Tendsto (fun n : ℕ => (n * (((b + (n * d)) /. (a + (n * d))) - 1))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (((b - a) * n) /. (a + (n * d)))))))
  (h12 : ∃ L : ℝ, Tendsto (fun n : ℕ => (n * (((b + (n * d)) /. (a + (n * d))) - 1))) atTop (𝓝 L))
  (h13 : ∃ L : ℝ, Tendsto (fun n : ℕ => (((b - a) * n) /. (a + (n * d)))) atTop (𝓝 L))
  : Tendsto (fun n : ℕ => (((b - a) * n) /. (a + (n * d)))) atTop (𝓝 ((b - a) /. d)) := by
  sorry

theorem proof_gap_exercise_2599_5
  (u : (ℕ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (d : ℝ)
  (k : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : d ∈ (Set.univ : Set ℝ))
  (h4 : k ∈ (Set.univ : Set ℕ))
  (h5 : a > 0)
  (h6 : b > 0)
  (h7 : d > 0)
  (h8 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((∏ k_1 ∈ Finset.Icc (0 : ℕ) (n - 1), (a + (k_1 * d))) /. (∏ k_1 ∈ Finset.Icc (0 : ℕ) (n - 1), (b + (k_1 * d))))))))
  (h9 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((u n) /. (u (n + 1))) = ((b + (n * d)) /. (a + (n * d)))))))
  (h10 : Tendsto (fun n : ℕ => (n * (((u n) /. (u (n + 1))) - 1))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (n * (((b + (n * d)) /. (a + (n * d))) - 1))))))
  (h11 : Tendsto (fun n : ℕ => (n * (((b + (n * d)) /. (a + (n * d))) - 1))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (((b - a) * n) /. (a + (n * d)))))))
  (h12 : Tendsto (fun n : ℕ => (((b - a) * n) /. (a + (n * d)))) atTop (𝓝 ((b - a) /. d)))
  (h13 : ∃ L : ℝ, Tendsto (fun n : ℕ => (n * (((b + (n * d)) /. (a + (n * d))) - 1))) atTop (𝓝 L))
  (h14 : ∃ L : ℝ, Tendsto (fun n : ℕ => (((b - a) * n) /. (a + (n * d)))) atTop (𝓝 L))
  : Tendsto (fun n : ℕ => (n * (((u n) /. (u (n + 1))) - 1))) atTop (𝓝 ((b - a) /. d)) := by
  sorry

theorem proof_gap_exercise_2599_6
  (u : (ℕ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (d : ℝ)
  (k : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : d ∈ (Set.univ : Set ℝ))
  (h4 : k ∈ (Set.univ : Set ℕ))
  (h5 : a > 0)
  (h6 : b > 0)
  (h7 : d > 0)
  (h8 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((∏ k_1 ∈ Finset.Icc (0 : ℕ) (n - 1), (a + (k_1 * d))) /. (∏ k_1 ∈ Finset.Icc (0 : ℕ) (n - 1), (b + (k_1 * d))))))))
  (h9 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((u n) /. (u (n + 1))) = ((b + (n * d)) /. (a + (n * d)))))))
  (h10 : Tendsto (fun n : ℕ => (n * (((u n) /. (u (n + 1))) - 1))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (n * (((b + (n * d)) /. (a + (n * d))) - 1))))))
  (h11 : Tendsto (fun n : ℕ => (n * (((b + (n * d)) /. (a + (n * d))) - 1))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (((b - a) * n) /. (a + (n * d)))))))
  (h12 : Tendsto (fun n : ℕ => (((b - a) * n) /. (a + (n * d)))) atTop (𝓝 ((b - a) /. d)))
  (h13 : Tendsto (fun n : ℕ => (n * (((u n) /. (u (n + 1))) - 1))) atTop (𝓝 ((b - a) /. d)))
  (h14 : ∃ L : ℝ, Tendsto (fun n : ℕ => (n * (((b + (n * d)) /. (a + (n * d))) - 1))) atTop (𝓝 L))
  (h15 : ∃ L : ℝ, Tendsto (fun n : ℕ => (((b - a) * n) /. (a + (n * d)))) atTop (𝓝 L))
  : (((b - a) /. d) > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (u n) else 0)) := by
  sorry

theorem proof_gap_exercise_2599_7
  (u : (ℕ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (d : ℝ)
  (k : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : d ∈ (Set.univ : Set ℝ))
  (h4 : k ∈ (Set.univ : Set ℕ))
  (h5 : a > 0)
  (h6 : b > 0)
  (h7 : d > 0)
  (h8 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((∏ k_1 ∈ Finset.Icc (0 : ℕ) (n - 1), (a + (k_1 * d))) /. (∏ k_1 ∈ Finset.Icc (0 : ℕ) (n - 1), (b + (k_1 * d))))))))
  (h9 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((u n) /. (u (n + 1))) = ((b + (n * d)) /. (a + (n * d)))))))
  (h10 : Tendsto (fun n : ℕ => (n * (((u n) /. (u (n + 1))) - 1))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (n * (((b + (n * d)) /. (a + (n * d))) - 1))))))
  (h11 : Tendsto (fun n : ℕ => (n * (((b + (n * d)) /. (a + (n * d))) - 1))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (((b - a) * n) /. (a + (n * d)))))))
  (h12 : Tendsto (fun n : ℕ => (((b - a) * n) /. (a + (n * d)))) atTop (𝓝 ((b - a) /. d)))
  (h13 : Tendsto (fun n : ℕ => (n * (((u n) /. (u (n + 1))) - 1))) atTop (𝓝 ((b - a) /. d)))
  (h14 : (((b - a) /. d) > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (u n) else 0)))
  (h15 : ∃ L : ℝ, Tendsto (fun n : ℕ => (n * (((b + (n * d)) /. (a + (n * d))) - 1))) atTop (𝓝 L))
  (h16 : ∃ L : ℝ, Tendsto (fun n : ℕ => (((b - a) * n) /. (a + (n * d)))) atTop (𝓝 L))
  : (((b - a) /. d) > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (u n) else 0)) := by
  sorry

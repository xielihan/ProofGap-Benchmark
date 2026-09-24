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

-- exercise: exercise_2990

theorem proof_gap_exercise_2990_1
  (m : ℕ)
  (h1 : m ∈ (Set.univ : Set ℕ))
  (h2 : m ∈ ({n_1 : ℕ | 0 < n_1}))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 /. (n * (n + m))) = ((1 /. m) * ((1 /. n) - (1 /. (n + m))))))) := by
  sorry

theorem proof_gap_exercise_2990_2
  (m : ℕ)
  (h1 : m ∈ (Set.univ : Set ℕ))
  (h2 : m ∈ ({n_1 : ℕ | 0 < n_1}))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 /. (n * (n + m))) = ((1 /. m) * ((1 /. n) - (1 /. (n + m))))))))
  : Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc (1 : ℕ) N, (1 /. (n * (n + m))))) atTop (𝓝 (∑' n, if (1 : ℕ) ≤ n then (1 /. (n * (n + m))) else 0)) := by
  sorry

theorem proof_gap_exercise_2990_3
  (m : ℕ)
  (h1 : m ∈ (Set.univ : Set ℕ))
  (h2 : m ∈ ({n_1 : ℕ | 0 < n_1}))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 /. (n * (n + m))) = ((1 /. m) * ((1 /. n) - (1 /. (n + m))))))))
  (h4 : Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc (1 : ℕ) N, (1 /. (n * (n + m))))) atTop (𝓝 (∑' n, if (1 : ℕ) ≤ n then (1 /. (n * (n + m))) else 0)))
  : (∃ L : ℝ, Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc (1 : ℕ) N, ((1 /. n) - (1 /. (n + m))))) atTop (𝓝 L) ∧ (Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc (1 : ℕ) N, (1 /. (n * (n + m))))) atTop (𝓝 ((1 /. m) * atTop.limUnder (fun N : ℕ => (∑ n ∈ Finset.Icc (1 : ℕ) N, ((1 /. n) - (1 /. (n + m))))))))) := by
  sorry

theorem proof_gap_exercise_2990_4
  (m : ℕ)
  (h1 : m ∈ (Set.univ : Set ℕ))
  (h2 : m ∈ ({n_1 : ℕ | 0 < n_1}))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 /. (n * (n + m))) = ((1 /. m) * ((1 /. n) - (1 /. (n + m))))))))
  (h4 : Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc (1 : ℕ) N, (1 /. (n * (n + m))))) atTop (𝓝 (∑' n, if (1 : ℕ) ≤ n then (1 /. (n * (n + m))) else 0)))
  (h5 : Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc (1 : ℕ) N, (1 /. (n * (n + m))))) atTop (𝓝 ((1 /. m) * atTop.limUnder (fun N : ℕ => (∑ n ∈ Finset.Icc (1 : ℕ) N, ((1 /. n) - (1 /. (n + m))))))))
  (h6 : ∃ L : ℝ, Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc (1 : ℕ) N, ((1 /. n) - (1 /. (n + m))))) atTop (𝓝 L))
  : (∃ L : ℝ, Tendsto (fun N : ℕ => ((∑ k ∈ Finset.Icc (1 : ℕ) m, (1 /. k)) - (∑ k ∈ Finset.Icc (1 : ℕ) m, (1 /. (N + k))))) atTop (𝓝 L) ∧ (Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc (1 : ℕ) N, ((1 /. n) - (1 /. (n + m))))) atTop (𝓝 (atTop.limUnder (fun N : ℕ => ((∑ k ∈ Finset.Icc (1 : ℕ) m, (1 /. k)) - (∑ k ∈ Finset.Icc (1 : ℕ) m, (1 /. (N + k))))))))) := by
  sorry

theorem proof_gap_exercise_2990_5
  (m : ℕ)
  (h1 : m ∈ (Set.univ : Set ℕ))
  (h2 : m ∈ ({n_1 : ℕ | 0 < n_1}))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 /. (n * (n + m))) = ((1 /. m) * ((1 /. n) - (1 /. (n + m))))))))
  (h4 : Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc (1 : ℕ) N, (1 /. (n * (n + m))))) atTop (𝓝 (∑' n, if (1 : ℕ) ≤ n then (1 /. (n * (n + m))) else 0)))
  (h5 : Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc (1 : ℕ) N, (1 /. (n * (n + m))))) atTop (𝓝 ((1 /. m) * atTop.limUnder (fun N : ℕ => (∑ n ∈ Finset.Icc (1 : ℕ) N, ((1 /. n) - (1 /. (n + m))))))))
  (h6 : Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc (1 : ℕ) N, ((1 /. n) - (1 /. (n + m))))) atTop (𝓝 (atTop.limUnder (fun N : ℕ => ((∑ k ∈ Finset.Icc (1 : ℕ) m, (1 /. k)) - (∑ k ∈ Finset.Icc (1 : ℕ) m, (1 /. (N + k))))))))
  (h7 : ∃ L : ℝ, Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc (1 : ℕ) N, ((1 /. n) - (1 /. (n + m))))) atTop (𝓝 L))
  (h8 : ∃ L : ℝ, Tendsto (fun N : ℕ => ((∑ k ∈ Finset.Icc (1 : ℕ) m, (1 /. k)) - (∑ k ∈ Finset.Icc (1 : ℕ) m, (1 /. (N + k))))) atTop (𝓝 L))
  : Tendsto (fun N : ℕ => ((∑ k ∈ Finset.Icc (1 : ℕ) m, (1 /. k)) - (∑ k ∈ Finset.Icc (1 : ℕ) m, (1 /. (N + k))))) atTop (𝓝 (∑ k ∈ Finset.Icc (1 : ℕ) m, (1 /. k))) := by
  sorry

theorem proof_gap_exercise_2990_6
  (m : ℕ)
  (h1 : m ∈ (Set.univ : Set ℕ))
  (h2 : m ∈ ({n_1 : ℕ | 0 < n_1}))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 /. (n * (n + m))) = ((1 /. m) * ((1 /. n) - (1 /. (n + m))))))))
  (h4 : Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc (1 : ℕ) N, (1 /. (n * (n + m))))) atTop (𝓝 (∑' n, if (1 : ℕ) ≤ n then (1 /. (n * (n + m))) else 0)))
  (h5 : Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc (1 : ℕ) N, (1 /. (n * (n + m))))) atTop (𝓝 ((1 /. m) * atTop.limUnder (fun N : ℕ => (∑ n ∈ Finset.Icc (1 : ℕ) N, ((1 /. n) - (1 /. (n + m))))))))
  (h6 : Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc (1 : ℕ) N, ((1 /. n) - (1 /. (n + m))))) atTop (𝓝 (atTop.limUnder (fun N : ℕ => ((∑ k ∈ Finset.Icc (1 : ℕ) m, (1 /. k)) - (∑ k ∈ Finset.Icc (1 : ℕ) m, (1 /. (N + k))))))))
  (h7 : Tendsto (fun N : ℕ => ((∑ k ∈ Finset.Icc (1 : ℕ) m, (1 /. k)) - (∑ k ∈ Finset.Icc (1 : ℕ) m, (1 /. (N + k))))) atTop (𝓝 (∑ k ∈ Finset.Icc (1 : ℕ) m, (1 /. k))))
  (h8 : ∃ L : ℝ, Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc (1 : ℕ) N, ((1 /. n) - (1 /. (n + m))))) atTop (𝓝 L))
  (h9 : ∃ L : ℝ, Tendsto (fun N : ℕ => ((∑ k ∈ Finset.Icc (1 : ℕ) m, (1 /. k)) - (∑ k ∈ Finset.Icc (1 : ℕ) m, (1 /. (N + k))))) atTop (𝓝 L))
  : (∑' n, if (1 : ℕ) ≤ n then (1 /. (n * (n + m))) else 0) = ((1 /. m) * (∑ k ∈ Finset.Icc (1 : ℕ) m, (1 /. k))) := by
  sorry

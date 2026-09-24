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

-- exercise: exercise_1223

theorem proof_gap_exercise_1223_1
  (f : (ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (a : ℝ)
  (n : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℕ))
  (h3 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((x - a) ^ n) * (v_uCF_u86 x))))))
  (h5 : ContDiff ℝ ((n - 1) : ℕ∞) v_uCF_u86)
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv (n - 1) (fun t_1 => f t_1) x) = (∑ j ∈ Finset.Icc (0 : ℕ) (n - 1), (((Nat.choose (n - 1) j) * (iteratedDeriv j (fun t_1 => ((t_1 - a) ^ n)) x)) * (iteratedDeriv ((n - 1) - j) (fun t_1 => v_uCF_u86 t_1) x)))))) := by
  sorry

theorem proof_gap_exercise_1223_2
  (f : (ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (a : ℝ)
  (n : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℕ))
  (h3 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((x - a) ^ n) * (v_uCF_u86 x))))))
  (h5 : (exists (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (ContDiffOn ℝ ((n - 1) : ℕ∞) v_uCF_u86 (Set.Ioo (a - v_uCE_uB4) (a + v_uCE_uB4))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv (n - 1) (fun t_1 => f t_1) x) = (∑ j ∈ Finset.Icc (0 : ℕ) (n - 1), (((Nat.choose (n - 1) j) * (iteratedDeriv j (fun t_1 => ((t_1 - a) ^ n)) x)) * (iteratedDeriv ((n - 1) - j) (fun t_1 => v_uCF_u86 t_1) x)))))))
  : (iteratedDeriv (n - 1) (fun t_1 => f t_1) a) = 0 := by
  sorry

theorem proof_gap_exercise_1223_3
  (f : (ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (a : ℝ)
  (n : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℕ))
  (h3 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((x - a) ^ n) * (v_uCF_u86 x))))))
  (h5 : (exists (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (ContDiffOn ℝ ((n - 1) : ℕ∞) v_uCF_u86 (Set.Ioo (a - v_uCE_uB4) (a + v_uCE_uB4))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv (n - 1) (fun t_1 => f t_1) x) = (∑ j ∈ Finset.Icc (0 : ℕ) (n - 1), (((Nat.choose (n - 1) j) * (iteratedDeriv j (fun t_1 => ((t_1 - a) ^ n)) x)) * (iteratedDeriv ((n - 1) - j) (fun t_1 => v_uCF_u86 t_1) x)))))))
  (h7 : (iteratedDeriv (n - 1) (fun t_1 => f t_1) a) = 0)
  : Tendsto (fun x : ℝ => (((iteratedDeriv (n - 1) (fun t_1 => f t_1) x) - (iteratedDeriv (n - 1) (fun t_1 => f t_1) a)) /. (x - a))) (𝓝[≠] a) (𝓝 (iteratedDeriv n (fun t_1 => f t_1) a)) := by
  sorry

theorem proof_gap_exercise_1223_4
  (f : (ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (a : ℝ)
  (n : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℕ))
  (h3 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((x - a) ^ n) * (v_uCF_u86 x))))))
  (h5 : (exists (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (ContDiffOn ℝ ((n - 1) : ℕ∞) v_uCF_u86 (Set.Ioo (a - v_uCE_uB4) (a + v_uCE_uB4))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv (n - 1) (fun t_1 => f t_1) x) = (∑ j ∈ Finset.Icc (0 : ℕ) (n - 1), (((Nat.choose (n - 1) j) * (iteratedDeriv j (fun t_1 => ((t_1 - a) ^ n)) x)) * (iteratedDeriv ((n - 1) - j) (fun t_1 => v_uCF_u86 t_1) x)))))))
  (h7 : (iteratedDeriv (n - 1) (fun t_1 => f t_1) a) = 0)
  (h8 : Tendsto (fun x : ℝ => (((iteratedDeriv (n - 1) (fun t_1 => f t_1) x) - (iteratedDeriv (n - 1) (fun t_1 => f t_1) a)) /. (x - a))) (𝓝[≠] a) (𝓝 (iteratedDeriv n (fun t_1 => f t_1) a)))
  : Tendsto (fun x : ℝ => (∑ j ∈ Finset.Icc (0 : ℕ) (n - 1), ((Nat.choose (n - 1) j) * (((iteratedDeriv j (fun t_1 => ((t_1 - a) ^ n)) x) * (iteratedDeriv ((n - 1) - j) (fun t_1 => v_uCF_u86 t_1) x)) /. (x - a))))) (𝓝[≠] a) (𝓝 (iteratedDeriv n (fun t_1 => f t_1) a)) := by
  sorry

theorem proof_gap_exercise_1223_5
  (f : (ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (a : ℝ)
  (n : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℕ))
  (h3 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((x - a) ^ n) * (v_uCF_u86 x))))))
  (h5 : (exists (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (ContDiffOn ℝ ((n - 1) : ℕ∞) v_uCF_u86 (Set.Ioo (a - v_uCE_uB4) (a + v_uCE_uB4))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv (n - 1) (fun t_1 => f t_1) x) = (∑ j ∈ Finset.Icc (0 : ℕ) (n - 1), (((Nat.choose (n - 1) j) * (iteratedDeriv j (fun t_1 => ((t_1 - a) ^ n)) x)) * (iteratedDeriv ((n - 1) - j) (fun t_1 => v_uCF_u86 t_1) x)))))))
  (h7 : (iteratedDeriv (n - 1) (fun t_1 => f t_1) a) = 0)
  (h8 : Tendsto (fun x : ℝ => (((iteratedDeriv (n - 1) (fun t_1 => f t_1) x) - (iteratedDeriv (n - 1) (fun t_1 => f t_1) a)) /. (x - a))) (𝓝[≠] a) (𝓝 (iteratedDeriv n (fun t_1 => f t_1) a)))
  (h9 : Tendsto (fun x : ℝ => (∑ j ∈ Finset.Icc (0 : ℕ) (n - 1), ((Nat.choose (n - 1) j) * (((iteratedDeriv j (fun t_1 => ((t_1 - a) ^ n)) x) * (iteratedDeriv ((n - 1) - j) (fun t_1 => v_uCF_u86 t_1) x)) /. (x - a))))) (𝓝[≠] a) (𝓝 (iteratedDeriv n (fun t_1 => f t_1) a)))
  : Tendsto (fun x : ℝ => ((n)! * (v_uCF_u86 x))) (𝓝[≠] a) (𝓝 (iteratedDeriv n (fun t_1 => f t_1) a)) := by
  sorry

theorem proof_gap_exercise_1223_6
  (f : (ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (a : ℝ)
  (n : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℕ))
  (h3 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((x - a) ^ n) * (v_uCF_u86 x))))))
  (h5 : (exists (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (ContDiffOn ℝ ((n - 1) : ℕ∞) v_uCF_u86 (Set.Ioo (a - v_uCE_uB4) (a + v_uCE_uB4))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv (n - 1) (fun t_1 => f t_1) x) = (∑ j ∈ Finset.Icc (0 : ℕ) (n - 1), (((Nat.choose (n - 1) j) * (iteratedDeriv j (fun t_1 => ((t_1 - a) ^ n)) x)) * (iteratedDeriv ((n - 1) - j) (fun t_1 => v_uCF_u86 t_1) x)))))))
  (h7 : (iteratedDeriv (n - 1) (fun t_1 => f t_1) a) = 0)
  (h8 : Tendsto (fun x : ℝ => (((iteratedDeriv (n - 1) (fun t_1 => f t_1) x) - (iteratedDeriv (n - 1) (fun t_1 => f t_1) a)) /. (x - a))) (𝓝[≠] a) (𝓝 (iteratedDeriv n (fun t_1 => f t_1) a)))
  (h9 : Tendsto (fun x : ℝ => (∑ j ∈ Finset.Icc (0 : ℕ) (n - 1), ((Nat.choose (n - 1) j) * (((iteratedDeriv j (fun t_1 => ((t_1 - a) ^ n)) x) * (iteratedDeriv ((n - 1) - j) (fun t_1 => v_uCF_u86 t_1) x)) /. (x - a))))) (𝓝[≠] a) (𝓝 (iteratedDeriv n (fun t_1 => f t_1) a)))
  (h10 : Tendsto (fun x : ℝ => ((n)! * (v_uCF_u86 x))) (𝓝[≠] a) (𝓝 (iteratedDeriv n (fun t_1 => f t_1) a)))
  : (iteratedDeriv n (fun t_1 => f t_1) a) = ((n)! * (v_uCF_u86 a)) := by
  sorry

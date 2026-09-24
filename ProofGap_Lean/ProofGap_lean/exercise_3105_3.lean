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

-- exercise: exercise_3105_3

theorem proof_gap_exercise_3105_3_1
  (v_uCE_u93 : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (m : ℕ), ((m ∈ (Set.univ : Set ℕ)) → (x ≠ (-(m : ℝ))))))
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ≤ n)) → (Tendsto (fun n_1 : ℕ => (((n_1)! * (Real.rpow n_1 x)) /. (∏ k_1 ∈ Finset.Icc (0 : ℕ) n_1, (x + k_1)))) atTop (𝓝 (v_uCE_u93 x))))))))
  (h4 : (v_uCE_u93 x) ≠ 0)
  : (∃ L : ℝ, Tendsto (fun n : ℕ => (((n)! * (Real.rpow n (x + 1))) /. (∏ k ∈ Finset.Icc (1 : ℕ) (n + 1), (x + k)))) atTop (𝓝 L) ∧ ∃ L : ℝ, Tendsto (fun n : ℕ => (((n)! * (Real.rpow n x)) /. (∏ k ∈ Finset.Icc (0 : ℕ) n, (x + k)))) atTop (𝓝 L) ∧ (((v_uCE_u93 (x + 1)) /. (v_uCE_u93 x)) = (atTop.limUnder (fun n : ℕ => (((n)! * (Real.rpow n (x + 1))) /. (∏ k ∈ Finset.Icc (1 : ℕ) (n + 1), (x + k)))) /. atTop.limUnder (fun n : ℕ => (((n)! * (Real.rpow n x)) /. (∏ k ∈ Finset.Icc (0 : ℕ) n, (x + k))))))) := by
  sorry

theorem proof_gap_exercise_3105_3_2
  (v_uCE_u93 : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (m : ℕ), ((m ∈ (Set.univ : Set ℕ)) → (x ≠ (-(m : ℝ))))))
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ≤ n)) → (Tendsto (fun n_1 : ℕ => (((n_1)! * (Real.rpow n_1 x)) /. (∏ k_1 ∈ Finset.Icc (0 : ℕ) n_1, (x + k_1)))) atTop (𝓝 (v_uCE_u93 x))))))))
  (h4 : (v_uCE_u93 x) ≠ 0)
  (h5 : ((v_uCE_u93 (x + 1)) /. (v_uCE_u93 x)) = (atTop.limUnder (fun n : ℕ => (((n)! * (Real.rpow n (x + 1))) /. (∏ k ∈ Finset.Icc (1 : ℕ) (n + 1), (x + k)))) /. atTop.limUnder (fun n : ℕ => (((n)! * (Real.rpow n x)) /. (∏ k ∈ Finset.Icc (0 : ℕ) n, (x + k))))))
  (h6 : ∃ L : ℝ, Tendsto (fun n : ℕ => (((n)! * (Real.rpow n (x + 1))) /. (∏ k ∈ Finset.Icc (1 : ℕ) (n + 1), (x + k)))) atTop (𝓝 L))
  (h7 : ∃ L : ℝ, Tendsto (fun n : ℕ => (((n)! * (Real.rpow n x)) /. (∏ k ∈ Finset.Icc (0 : ℕ) n, (x + k)))) atTop (𝓝 L))
  : Tendsto (fun n : ℕ => ((((n)! * (Real.rpow n (x + 1))) /. (∏ k ∈ Finset.Icc (1 : ℕ) (n + 1), (x + k))) /. (((n)! * (Real.rpow n x)) /. (∏ k ∈ Finset.Icc (0 : ℕ) n, (x + k))))) atTop (𝓝 ((v_uCE_u93 (x + 1)) /. (v_uCE_u93 x))) := by
  sorry

theorem proof_gap_exercise_3105_3_3
  (v_uCE_u93 : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (m : ℕ), ((m ∈ (Set.univ : Set ℕ)) → (x ≠ (-(m : ℝ))))))
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ≤ n)) → (Tendsto (fun n_1 : ℕ => (((n_1)! * (Real.rpow n_1 x)) /. (∏ k_1 ∈ Finset.Icc (0 : ℕ) n_1, (x + k_1)))) atTop (𝓝 (v_uCE_u93 x))))))))
  (h4 : (v_uCE_u93 x) ≠ 0)
  (h5 : ((v_uCE_u93 (x + 1)) /. (v_uCE_u93 x)) = (atTop.limUnder (fun n : ℕ => (((n)! * (Real.rpow n (x + 1))) /. (∏ k ∈ Finset.Icc (1 : ℕ) (n + 1), (x + k)))) /. atTop.limUnder (fun n : ℕ => (((n)! * (Real.rpow n x)) /. (∏ k ∈ Finset.Icc (0 : ℕ) n, (x + k))))))
  (h6 : Tendsto (fun n : ℕ => ((((n)! * (Real.rpow n (x + 1))) /. (∏ k ∈ Finset.Icc (1 : ℕ) (n + 1), (x + k))) /. (((n)! * (Real.rpow n x)) /. (∏ k ∈ Finset.Icc (0 : ℕ) n, (x + k))))) atTop (𝓝 ((v_uCE_u93 (x + 1)) /. (v_uCE_u93 x))))
  (h7 : ∃ L : ℝ, Tendsto (fun n : ℕ => (((n)! * (Real.rpow n (x + 1))) /. (∏ k ∈ Finset.Icc (1 : ℕ) (n + 1), (x + k)))) atTop (𝓝 L))
  (h8 : ∃ L : ℝ, Tendsto (fun n : ℕ => (((n)! * (Real.rpow n x)) /. (∏ k ∈ Finset.Icc (0 : ℕ) n, (x + k)))) atTop (𝓝 L))
  : Tendsto (fun n : ℕ => ((n * x) /. ((x + n) + 1))) atTop (𝓝 ((v_uCE_u93 (x + 1)) /. (v_uCE_u93 x))) := by
  sorry

theorem proof_gap_exercise_3105_3_4
  (v_uCE_u93 : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (m : ℕ), ((m ∈ (Set.univ : Set ℕ)) → (x ≠ (-(m : ℝ))))))
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ≤ n)) → (Tendsto (fun n_1 : ℕ => (((n_1)! * (Real.rpow n_1 x)) /. (∏ k_1 ∈ Finset.Icc (0 : ℕ) n_1, (x + k_1)))) atTop (𝓝 (v_uCE_u93 x))))))))
  (h4 : (v_uCE_u93 x) ≠ 0)
  (h5 : ((v_uCE_u93 (x + 1)) /. (v_uCE_u93 x)) = (atTop.limUnder (fun n : ℕ => (((n)! * (Real.rpow n (x + 1))) /. (∏ k ∈ Finset.Icc (1 : ℕ) (n + 1), (x + k)))) /. atTop.limUnder (fun n : ℕ => (((n)! * (Real.rpow n x)) /. (∏ k ∈ Finset.Icc (0 : ℕ) n, (x + k))))))
  (h6 : Tendsto (fun n : ℕ => ((((n)! * (Real.rpow n (x + 1))) /. (∏ k ∈ Finset.Icc (1 : ℕ) (n + 1), (x + k))) /. (((n)! * (Real.rpow n x)) /. (∏ k ∈ Finset.Icc (0 : ℕ) n, (x + k))))) atTop (𝓝 ((v_uCE_u93 (x + 1)) /. (v_uCE_u93 x))))
  (h7 : Tendsto (fun n : ℕ => ((n * x) /. ((x + n) + 1))) atTop (𝓝 ((v_uCE_u93 (x + 1)) /. (v_uCE_u93 x))))
  (h8 : ∃ L : ℝ, Tendsto (fun n : ℕ => (((n)! * (Real.rpow n (x + 1))) /. (∏ k ∈ Finset.Icc (1 : ℕ) (n + 1), (x + k)))) atTop (𝓝 L))
  (h9 : ∃ L : ℝ, Tendsto (fun n : ℕ => (((n)! * (Real.rpow n x)) /. (∏ k ∈ Finset.Icc (0 : ℕ) n, (x + k)))) atTop (𝓝 L))
  : Tendsto (fun n : ℕ => ((n * x) /. ((x + n) + 1))) atTop (𝓝 x) := by
  sorry

theorem proof_gap_exercise_3105_3_5
  (v_uCE_u93 : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (m : ℕ), ((m ∈ (Set.univ : Set ℕ)) → (x ≠ (-(m : ℝ))))))
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ≤ n)) → (Tendsto (fun n_1 : ℕ => (((n_1)! * (Real.rpow n_1 x)) /. (∏ k_1 ∈ Finset.Icc (0 : ℕ) n_1, (x + k_1)))) atTop (𝓝 (v_uCE_u93 x))))))))
  (h4 : (v_uCE_u93 x) ≠ 0)
  (h5 : ((v_uCE_u93 (x + 1)) /. (v_uCE_u93 x)) = (atTop.limUnder (fun n : ℕ => (((n)! * (Real.rpow n (x + 1))) /. (∏ k ∈ Finset.Icc (1 : ℕ) (n + 1), (x + k)))) /. atTop.limUnder (fun n : ℕ => (((n)! * (Real.rpow n x)) /. (∏ k ∈ Finset.Icc (0 : ℕ) n, (x + k))))))
  (h6 : Tendsto (fun n : ℕ => ((((n)! * (Real.rpow n (x + 1))) /. (∏ k ∈ Finset.Icc (1 : ℕ) (n + 1), (x + k))) /. (((n)! * (Real.rpow n x)) /. (∏ k ∈ Finset.Icc (0 : ℕ) n, (x + k))))) atTop (𝓝 ((v_uCE_u93 (x + 1)) /. (v_uCE_u93 x))))
  (h7 : Tendsto (fun n : ℕ => ((n * x) /. ((x + n) + 1))) atTop (𝓝 ((v_uCE_u93 (x + 1)) /. (v_uCE_u93 x))))
  (h8 : Tendsto (fun n : ℕ => ((n * x) /. ((x + n) + 1))) atTop (𝓝 x))
  (h9 : ∃ L : ℝ, Tendsto (fun n : ℕ => (((n)! * (Real.rpow n (x + 1))) /. (∏ k ∈ Finset.Icc (1 : ℕ) (n + 1), (x + k)))) atTop (𝓝 L))
  (h10 : ∃ L : ℝ, Tendsto (fun n : ℕ => (((n)! * (Real.rpow n x)) /. (∏ k ∈ Finset.Icc (0 : ℕ) n, (x + k)))) atTop (𝓝 L))
  : ((v_uCE_u93 (x + 1)) /. (v_uCE_u93 x)) = x := by
  sorry

theorem proof_gap_exercise_3105_3_6
  (v_uCE_u93 : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (m : ℕ), ((m ∈ (Set.univ : Set ℕ)) → (x ≠ (-(m : ℝ))))))
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ≤ n)) → (Tendsto (fun n_1 : ℕ => (((n_1)! * (Real.rpow n_1 x)) /. (∏ k_1 ∈ Finset.Icc (0 : ℕ) n_1, (x + k_1)))) atTop (𝓝 (v_uCE_u93 x))))))))
  (h4 : (v_uCE_u93 x) ≠ 0)
  (h5 : ((v_uCE_u93 (x + 1)) /. (v_uCE_u93 x)) = (atTop.limUnder (fun n : ℕ => (((n)! * (Real.rpow n (x + 1))) /. (∏ k ∈ Finset.Icc (1 : ℕ) (n + 1), (x + k)))) /. atTop.limUnder (fun n : ℕ => (((n)! * (Real.rpow n x)) /. (∏ k ∈ Finset.Icc (0 : ℕ) n, (x + k))))))
  (h6 : Tendsto (fun n : ℕ => ((((n)! * (Real.rpow n (x + 1))) /. (∏ k ∈ Finset.Icc (1 : ℕ) (n + 1), (x + k))) /. (((n)! * (Real.rpow n x)) /. (∏ k ∈ Finset.Icc (0 : ℕ) n, (x + k))))) atTop (𝓝 ((v_uCE_u93 (x + 1)) /. (v_uCE_u93 x))))
  (h7 : Tendsto (fun n : ℕ => ((n * x) /. ((x + n) + 1))) atTop (𝓝 ((v_uCE_u93 (x + 1)) /. (v_uCE_u93 x))))
  (h8 : Tendsto (fun n : ℕ => ((n * x) /. ((x + n) + 1))) atTop (𝓝 x))
  (h9 : ((v_uCE_u93 (x + 1)) /. (v_uCE_u93 x)) = x)
  (h10 : ∃ L : ℝ, Tendsto (fun n : ℕ => (((n)! * (Real.rpow n (x + 1))) /. (∏ k ∈ Finset.Icc (1 : ℕ) (n + 1), (x + k)))) atTop (𝓝 L))
  (h11 : ∃ L : ℝ, Tendsto (fun n : ℕ => (((n)! * (Real.rpow n x)) /. (∏ k ∈ Finset.Icc (0 : ℕ) n, (x + k)))) atTop (𝓝 L))
  : (v_uCE_u93 (x + 1)) = (x * (v_uCE_u93 x)) := by
  sorry

theorem proof_gap_exercise_3105_3_7
  (v_uCE_u93 : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (m : ℕ), ((m ∈ (Set.univ : Set ℕ)) → (x ≠ (-(m : ℝ))))))
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ≤ n)) → (Tendsto (fun n_1 : ℕ => (((n_1)! * (Real.rpow n_1 x)) /. (∏ k_1 ∈ Finset.Icc (0 : ℕ) n_1, (x + k_1)))) atTop (𝓝 (v_uCE_u93 x))))))))
  (h4 : (v_uCE_u93 x) ≠ 0)
  (h5 : ((v_uCE_u93 (x + 1)) /. (v_uCE_u93 x)) = (atTop.limUnder (fun n : ℕ => (((n)! * (Real.rpow n (x + 1))) /. (∏ k ∈ Finset.Icc (1 : ℕ) (n + 1), (x + k)))) /. atTop.limUnder (fun n : ℕ => (((n)! * (Real.rpow n x)) /. (∏ k ∈ Finset.Icc (0 : ℕ) n, (x + k))))))
  (h6 : Tendsto (fun n : ℕ => ((((n)! * (Real.rpow n (x + 1))) /. (∏ k ∈ Finset.Icc (1 : ℕ) (n + 1), (x + k))) /. (((n)! * (Real.rpow n x)) /. (∏ k ∈ Finset.Icc (0 : ℕ) n, (x + k))))) atTop (𝓝 ((v_uCE_u93 (x + 1)) /. (v_uCE_u93 x))))
  (h7 : Tendsto (fun n : ℕ => ((n * x) /. ((x + n) + 1))) atTop (𝓝 ((v_uCE_u93 (x + 1)) /. (v_uCE_u93 x))))
  (h8 : Tendsto (fun n : ℕ => ((n * x) /. ((x + n) + 1))) atTop (𝓝 x))
  (h9 : ((v_uCE_u93 (x + 1)) /. (v_uCE_u93 x)) = x)
  (h10 : (v_uCE_u93 (x + 1)) = (x * (v_uCE_u93 x)))
  (h11 : ∃ L : ℝ, Tendsto (fun n : ℕ => (((n)! * (Real.rpow n (x + 1))) /. (∏ k ∈ Finset.Icc (1 : ℕ) (n + 1), (x + k)))) atTop (𝓝 L))
  (h12 : ∃ L : ℝ, Tendsto (fun n : ℕ => (((n)! * (Real.rpow n x)) /. (∏ k ∈ Finset.Icc (0 : ℕ) n, (x + k)))) atTop (𝓝 L))
  : (v_uCE_u93 (x + 1)) = (x * (v_uCE_u93 x)) := by
  sorry

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

-- exercise: exercise_3032

theorem proof_gap_exercise_3032_1
  (s : (ℕ -> ℝ))
  (R : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |(x)| ≠ 1)
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((s n) = ((x ^ ((2 : ℕ) ^ n)) /. (1 - (x ^ ((2 : ℕ) ^ (n + 1)))))))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((R n) = ((x ^ ((2 : ℕ) ^ (n + 1))) /. (1 - (x ^ ((2 : ℕ) ^ (n + 1)))))))))
  : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((x /. (1 - x)) = ((∑ k ∈ Finset.Icc (0 : ℕ) n, (s k)) + (R n))))) := by
  sorry

theorem proof_gap_exercise_3032_2
  (s : (ℕ -> ℝ))
  (R : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |(x)| ≠ 1)
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((s n) = ((x ^ ((2 : ℕ) ^ n)) /. (1 - (x ^ ((2 : ℕ) ^ (n + 1)))))))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((R n) = ((x ^ ((2 : ℕ) ^ (n + 1))) /. (1 - (x ^ ((2 : ℕ) ^ (n + 1)))))))))
  (h5 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((x /. (1 - x)) = ((∑ k ∈ Finset.Icc (0 : ℕ) n, (s k)) + (R n))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (|(x)| < 1)) → (Tendsto (fun n_1 : ℕ => (R n_1)) atTop (𝓝 0)))) := by
  sorry

theorem proof_gap_exercise_3032_3
  (s : (ℕ -> ℝ))
  (R : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |(x)| ≠ 1)
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((s n) = ((x ^ ((2 : ℕ) ^ n)) /. (1 - (x ^ ((2 : ℕ) ^ (n + 1)))))))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((R n) = ((x ^ ((2 : ℕ) ^ (n + 1))) /. (1 - (x ^ ((2 : ℕ) ^ (n + 1)))))))))
  (h5 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((x /. (1 - x)) = ((∑ k ∈ Finset.Icc (0 : ℕ) n, (s k)) + (R n))))))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (|(x)| < 1)) → (Tendsto (fun n_1 : ℕ => (R n_1)) atTop (𝓝 0)))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (|(x)| < 1)) → (HasSum (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then (s n_1) else 0) (x /. (1 - x))))) := by
  sorry

theorem proof_gap_exercise_3032_4
  (s : (ℕ -> ℝ))
  (R : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |(x)| ≠ 1)
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((s n) = ((x ^ ((2 : ℕ) ^ n)) /. (1 - (x ^ ((2 : ℕ) ^ (n + 1)))))))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((R n) = ((x ^ ((2 : ℕ) ^ (n + 1))) /. (1 - (x ^ ((2 : ℕ) ^ (n + 1)))))))))
  (h5 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((x /. (1 - x)) = ((∑ k ∈ Finset.Icc (0 : ℕ) n, (s k)) + (R n))))))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (|(x)| < 1)) → (Tendsto (fun n_1 : ℕ => (R n_1)) atTop (𝓝 0)))))
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (|(x)| < 1)) → (HasSum (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then (s n_1) else 0) (x /. (1 - x))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (|(x)| > 1)) → (Tendsto (fun n_1 : ℕ => (Real.rpow (1 /. |(x)|) (Real.rpow (2 : ℝ) (n_1 + 1)))) atTop (𝓝 0)))) := by
  sorry

theorem proof_gap_exercise_3032_5
  (s : (ℕ -> ℝ))
  (R : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |(x)| ≠ 1)
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((s n) = ((x ^ ((2 : ℕ) ^ n)) /. (1 - (x ^ ((2 : ℕ) ^ (n + 1)))))))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((R n) = ((x ^ ((2 : ℕ) ^ (n + 1))) /. (1 - (x ^ ((2 : ℕ) ^ (n + 1)))))))))
  (h5 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((x /. (1 - x)) = ((∑ k ∈ Finset.Icc (0 : ℕ) n, (s k)) + (R n))))))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (|(x)| < 1)) → (Tendsto (fun n_1 : ℕ => (R n_1)) atTop (𝓝 0)))))
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (|(x)| < 1)) → (HasSum (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then (s n_1) else 0) (x /. (1 - x))))))
  (h8 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (|(x)| > 1)) → (Tendsto (fun n_1 : ℕ => (Real.rpow (1 /. |(x)|) (Real.rpow (2 : ℝ) (n_1 + 1)))) atTop (𝓝 0)))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (|(x)| > 1)) → (Tendsto (fun n_1 : ℕ => (R n_1)) atTop (𝓝 (-(1 : ℝ)))))) := by
  sorry

theorem proof_gap_exercise_3032_6
  (s : (ℕ -> ℝ))
  (R : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |(x)| ≠ 1)
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((s n) = ((x ^ ((2 : ℕ) ^ n)) /. (1 - (x ^ ((2 : ℕ) ^ (n + 1)))))))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((R n) = ((x ^ ((2 : ℕ) ^ (n + 1))) /. (1 - (x ^ ((2 : ℕ) ^ (n + 1)))))))))
  (h5 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((x /. (1 - x)) = ((∑ k ∈ Finset.Icc (0 : ℕ) n, (s k)) + (R n))))))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (|(x)| < 1)) → (Tendsto (fun n_1 : ℕ => (R n_1)) atTop (𝓝 0)))))
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (|(x)| < 1)) → (HasSum (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then (s n_1) else 0) (x /. (1 - x))))))
  (h8 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (|(x)| > 1)) → (Tendsto (fun n_1 : ℕ => (Real.rpow (1 /. |(x)|) (Real.rpow (2 : ℝ) (n_1 + 1)))) atTop (𝓝 0)))))
  (h9 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (|(x)| > 1)) → (Tendsto (fun n_1 : ℕ => (R n_1)) atTop (𝓝 (-(1 : ℝ)))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (|(x)| > 1)) → (HasSum (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then (s n_1) else 0) (1 /. (1 - x))))) := by
  sorry

theorem proof_gap_exercise_3032_7
  (s : (ℕ -> ℝ))
  (R : (ℕ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |(x)| ≠ 1)
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((s n) = ((x ^ ((2 : ℕ) ^ n)) /. (1 - (x ^ ((2 : ℕ) ^ (n + 1)))))))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((R n) = ((x ^ ((2 : ℕ) ^ (n + 1))) /. (1 - (x ^ ((2 : ℕ) ^ (n + 1)))))))))
  (h5 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((x /. (1 - x)) = ((∑ k ∈ Finset.Icc (0 : ℕ) n, (s k)) + (R n))))))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (|(x)| < 1)) → (Tendsto (fun n_1 : ℕ => (R n_1)) atTop (𝓝 0)))))
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (|(x)| < 1)) → (HasSum (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then (s n_1) else 0) (x /. (1 - x))))))
  (h8 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (|(x)| > 1)) → (Tendsto (fun n_1 : ℕ => (Real.rpow (1 /. |(x)|) (Real.rpow (2 : ℝ) (n_1 + 1)))) atTop (𝓝 0)))))
  (h9 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (|(x)| > 1)) → (Tendsto (fun n_1 : ℕ => (R n_1)) atTop (𝓝 (-(1 : ℝ)))))))
  (h10 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (|(x)| > 1)) → (HasSum (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then (s n_1) else 0) (1 /. (1 - x))))))
  : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((∑' n_1, if (0 : ℕ) ≤ n_1 then (s n_1) else 0) = (if (|(x)| < 1) then (x /. (1 - x)) else (if (|(x)| > 1) then (1 /. (1 - x)) else (1 /. (1 - x))))))) := by
  sorry

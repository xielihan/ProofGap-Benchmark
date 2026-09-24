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

-- exercise: exercise_2574

theorem proof_gap_exercise_2574_1
  (S : (ℕ -> ℝ))
  (x : ℝ)
  (k : ℕ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : k ∈ (Set.univ : Set ℕ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((Real.sin (k_1 * x)) /. ((2 : ℕ) ^ k_1)))))))
  : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (p : ℕ), ((((p ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (p ∈ ({n_1 : ℕ | 0 < n_1}))) → (|(((S (n + p)) - (S n)))| = |((∑ k_1 ∈ Finset.Icc (n + 1) (n + p), ((Real.sin (k_1 * x)) /. ((2 : ℕ) ^ k_1))))|))))) := by
  sorry

theorem proof_gap_exercise_2574_2
  (S : (ℕ -> ℝ))
  (x : ℝ)
  (k : ℕ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : k ∈ (Set.univ : Set ℕ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((Real.sin (k_1 * x)) /. ((2 : ℕ) ^ k_1)))))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (p : ℕ), ((((p ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (p ∈ ({n_1 : ℕ | 0 < n_1}))) → (|(((S (n + p)) - (S n)))| = |((∑ k_1 ∈ Finset.Icc (n + 1) (n + p), ((Real.sin (k_1 * x)) /. ((2 : ℕ) ^ k_1))))|))))))
  : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (p : ℕ), ((((p ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (p ∈ ({n_1 : ℕ | 0 < n_1}))) → (|(((S (n + p)) - (S n)))| ≤ (∑ k_1 ∈ Finset.Icc (n + 1) (n + p), (1 /. ((2 : ℕ) ^ k_1)))))))) := by
  sorry

theorem proof_gap_exercise_2574_3
  (S : (ℕ -> ℝ))
  (x : ℝ)
  (k : ℕ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : k ∈ (Set.univ : Set ℕ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((Real.sin (k_1 * x)) /. ((2 : ℕ) ^ k_1)))))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (p : ℕ), ((((p ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (p ∈ ({n_1 : ℕ | 0 < n_1}))) → (|(((S (n + p)) - (S n)))| = |((∑ k_1 ∈ Finset.Icc (n + 1) (n + p), ((Real.sin (k_1 * x)) /. ((2 : ℕ) ^ k_1))))|))))))
  (h5 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (p : ℕ), ((((p ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (p ∈ ({n_1 : ℕ | 0 < n_1}))) → (|(((S (n + p)) - (S n)))| ≤ (∑ k_1 ∈ Finset.Icc (n + 1) (n + p), (1 /. ((2 : ℕ) ^ k_1)))))))))
  : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. ((2 : ℕ) ^ n)) else 0) := by
  sorry

theorem proof_gap_exercise_2574_4
  (S : (ℕ -> ℝ))
  (x : ℝ)
  (k : ℕ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : k ∈ (Set.univ : Set ℕ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((Real.sin (k_1 * x)) /. ((2 : ℕ) ^ k_1)))))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (p : ℕ), ((((p ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (p ∈ ({n_1 : ℕ | 0 < n_1}))) → (|(((S (n + p)) - (S n)))| = |((∑ k_1 ∈ Finset.Icc (n + 1) (n + p), ((Real.sin (k_1 * x)) /. ((2 : ℕ) ^ k_1))))|))))))
  (h5 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (p : ℕ), ((((p ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (p ∈ ({n_1 : ℕ | 0 < n_1}))) → (|(((S (n + p)) - (S n)))| ≤ (∑ k_1 ∈ Finset.Icc (n + 1) (n + p), (1 /. ((2 : ℕ) ^ k_1)))))))))
  (h6 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. ((2 : ℕ) ^ n)) else 0))
  : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ) (p : ℕ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (p ∈ (Set.univ : Set ℕ))) ∧ (n > N)) ∧ (p ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k_1 ∈ Finset.Icc (n + 1) (n + p), (1 /. ((2 : ℕ) ^ k_1))) < v_uCE_uB5))))))) := by
  sorry

theorem proof_gap_exercise_2574_5
  (S : (ℕ -> ℝ))
  (x : ℝ)
  (k : ℕ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : k ∈ (Set.univ : Set ℕ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((Real.sin (k_1 * x)) /. ((2 : ℕ) ^ k_1)))))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (p : ℕ), ((((p ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (p ∈ ({n_1 : ℕ | 0 < n_1}))) → (|(((S (n + p)) - (S n)))| = |((∑ k_1 ∈ Finset.Icc (n + 1) (n + p), ((Real.sin (k_1 * x)) /. ((2 : ℕ) ^ k_1))))|))))))
  (h5 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (p : ℕ), ((((p ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (p ∈ ({n_1 : ℕ | 0 < n_1}))) → (|(((S (n + p)) - (S n)))| ≤ (∑ k_1 ∈ Finset.Icc (n + 1) (n + p), (1 /. ((2 : ℕ) ^ k_1)))))))))
  (h6 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. ((2 : ℕ) ^ n)) else 0))
  (h7 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ) (p : ℕ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (p ∈ (Set.univ : Set ℕ))) ∧ (n > N)) ∧ (p ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k_1 ∈ Finset.Icc (n + 1) (n + p), (1 /. ((2 : ℕ) ^ k_1))) < v_uCE_uB5))))))))
  : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > N)) → (forall (p : ℕ), (((p ∈ (Set.univ : Set ℕ)) ∧ (p ∈ ({n_1 : ℕ | 0 < n_1}))) → (|(((S (n + p)) - (S n)))| < v_uCE_uB5))))))))) := by
  sorry

theorem proof_gap_exercise_2574_6
  (S : (ℕ -> ℝ))
  (x : ℝ)
  (k : ℕ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : k ∈ (Set.univ : Set ℕ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((Real.sin (k_1 * x)) /. ((2 : ℕ) ^ k_1)))))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (p : ℕ), ((((p ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (p ∈ ({n_1 : ℕ | 0 < n_1}))) → (|(((S (n + p)) - (S n)))| = |((∑ k_1 ∈ Finset.Icc (n + 1) (n + p), ((Real.sin (k_1 * x)) /. ((2 : ℕ) ^ k_1))))|))))))
  (h5 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (p : ℕ), ((((p ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (p ∈ ({n_1 : ℕ | 0 < n_1}))) → (|(((S (n + p)) - (S n)))| ≤ (∑ k_1 ∈ Finset.Icc (n + 1) (n + p), (1 /. ((2 : ℕ) ^ k_1)))))))))
  (h6 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. ((2 : ℕ) ^ n)) else 0))
  (h7 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ) (p : ℕ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (p ∈ (Set.univ : Set ℕ))) ∧ (n > N)) ∧ (p ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k_1 ∈ Finset.Icc (n + 1) (n + p), (1 /. ((2 : ℕ) ^ k_1))) < v_uCE_uB5))))))))
  (h8 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > N)) → (forall (p : ℕ), (((p ∈ (Set.univ : Set ℕ)) ∧ (p ∈ ({n_1 : ℕ | 0 < n_1}))) → (|(((S (n + p)) - (S n)))| < v_uCE_uB5))))))))))
  : CauchySeq S := by
  sorry

theorem proof_gap_exercise_2574_7
  (S : (ℕ -> ℝ))
  (x : ℝ)
  (k : ℕ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : k ∈ (Set.univ : Set ℕ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((Real.sin (k_1 * x)) /. ((2 : ℕ) ^ k_1)))))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (p : ℕ), ((((p ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (p ∈ ({n_1 : ℕ | 0 < n_1}))) → (|(((S (n + p)) - (S n)))| = |((∑ k_1 ∈ Finset.Icc (n + 1) (n + p), ((Real.sin (k_1 * x)) /. ((2 : ℕ) ^ k_1))))|))))))
  (h5 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (p : ℕ), ((((p ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (p ∈ ({n_1 : ℕ | 0 < n_1}))) → (|(((S (n + p)) - (S n)))| ≤ (∑ k_1 ∈ Finset.Icc (n + 1) (n + p), (1 /. ((2 : ℕ) ^ k_1)))))))))
  (h6 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. ((2 : ℕ) ^ n)) else 0))
  (h7 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ) (p : ℕ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (p ∈ (Set.univ : Set ℕ))) ∧ (n > N)) ∧ (p ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k_1 ∈ Finset.Icc (n + 1) (n + p), (1 /. ((2 : ℕ) ^ k_1))) < v_uCE_uB5))))))))
  (h8 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > N)) → (forall (p : ℕ), (((p ∈ (Set.univ : Set ℕ)) ∧ (p ∈ ({n_1 : ℕ | 0 < n_1}))) → (|(((S (n + p)) - (S n)))| < v_uCE_uB5))))))))))
  (h9 : CauchySeq S)
  : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((Real.sin (n * x)) /. ((2 : ℕ) ^ n)) else 0) := by
  sorry

theorem proof_gap_exercise_2574_8
  (S : (ℕ -> ℝ))
  (x : ℝ)
  (k : ℕ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : k ∈ (Set.univ : Set ℕ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((Real.sin (k_1 * x)) /. ((2 : ℕ) ^ k_1)))))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (p : ℕ), ((((p ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (p ∈ ({n_1 : ℕ | 0 < n_1}))) → (|(((S (n + p)) - (S n)))| = |((∑ k_1 ∈ Finset.Icc (n + 1) (n + p), ((Real.sin (k_1 * x)) /. ((2 : ℕ) ^ k_1))))|))))))
  (h5 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (p : ℕ), ((((p ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (p ∈ ({n_1 : ℕ | 0 < n_1}))) → (|(((S (n + p)) - (S n)))| ≤ (∑ k_1 ∈ Finset.Icc (n + 1) (n + p), (1 /. ((2 : ℕ) ^ k_1)))))))))
  (h6 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. ((2 : ℕ) ^ n)) else 0))
  (h7 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ) (p : ℕ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (p ∈ (Set.univ : Set ℕ))) ∧ (n > N)) ∧ (p ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k_1 ∈ Finset.Icc (n + 1) (n + p), (1 /. ((2 : ℕ) ^ k_1))) < v_uCE_uB5))))))))
  (h8 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > N)) → (forall (p : ℕ), (((p ∈ (Set.univ : Set ℕ)) ∧ (p ∈ ({n_1 : ℕ | 0 < n_1}))) → (|(((S (n + p)) - (S n)))| < v_uCE_uB5))))))))))
  (h9 : CauchySeq S)
  (h10 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((Real.sin (n * x)) /. ((2 : ℕ) ^ n)) else 0))
  : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((Real.sin (n * x)) /. ((2 : ℕ) ^ n)) else 0) := by
  sorry

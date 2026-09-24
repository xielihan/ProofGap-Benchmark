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

-- exercise: exercise_2706_2

theorem proof_gap_exercise_2706_2_1
  (h1 : a = (fun (n : ℕ) => ((-(1 : ℤ)) ^ n)))
  (h2 : b = (fun (n : ℕ) => ((-(1 : ℤ)) ^ (n + 1))))
  (h3 : c = (fun (n : ℕ) => ((a n) + (b n))))
  : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0) := by
  sorry

theorem proof_gap_exercise_2706_2_2
  (h1 : a = (fun (n : ℕ) => ((-(1 : ℤ)) ^ n)))
  (h2 : b = (fun (n : ℕ) => ((-(1 : ℤ)) ^ (n + 1))))
  (h3 : c = (fun (n : ℕ) => ((a n) + (b n))))
  (h4 : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0))
  : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (b n) else 0) := by
  sorry

theorem proof_gap_exercise_2706_2_3
  (h1 : a = (fun (n : ℕ) => ((-(1 : ℤ)) ^ n)))
  (h2 : b = (fun (n : ℕ) => ((-(1 : ℤ)) ^ (n + 1))))
  (h3 : c = (fun (n : ℕ) => ((a n) + (b n))))
  (h4 : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0))
  (h5 : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (b n) else 0))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((c n) = 0))) := by
  sorry

theorem proof_gap_exercise_2706_2_4
  (h1 : a = (fun (n : ℕ) => ((-(1 : ℤ)) ^ n)))
  (h2 : b = (fun (n : ℕ) => ((-(1 : ℤ)) ^ (n + 1))))
  (h3 : c = (fun (n : ℕ) => ((a n) + (b n))))
  (h4 : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0))
  (h5 : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (b n) else 0))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((c n) = 0))))
  : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (c n) else 0) := by
  sorry

theorem proof_gap_exercise_2706_2_5
  (h1 : a = (fun (n : ℕ) => ((-(1 : ℤ)) ^ n)))
  (h2 : b = (fun (n : ℕ) => ((-(1 : ℤ)) ^ (n + 1))))
  (h3 : c = (fun (n : ℕ) => ((a n) + (b n))))
  (h4 : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0))
  (h5 : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (b n) else 0))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((c n) = 0))))
  (h7 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (c n) else 0))
  (h8 : A = (fun (n : ℕ) => (1 /. n)))
  (h9 : B = (fun (n : ℕ) => (1 /. n)))
  (h10 : C = (fun (n : ℕ) => ((A n) + (B n))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((C n) = (2 /. n)))) := by
  sorry

theorem proof_gap_exercise_2706_2_6
  (h1 : a = (fun (n : ℕ) => ((-(1 : ℤ)) ^ n)))
  (h2 : b = (fun (n : ℕ) => ((-(1 : ℤ)) ^ (n + 1))))
  (h3 : c = (fun (n : ℕ) => ((a n) + (b n))))
  (h4 : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0))
  (h5 : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (b n) else 0))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((c n) = 0))))
  (h7 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (c n) else 0))
  (h8 : A = (fun (n : ℕ) => (1 /. n)))
  (h9 : B = (fun (n : ℕ) => (1 /. n)))
  (h10 : C = (fun (n : ℕ) => ((A n) + (B n))))
  (h11 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((C n) = (2 /. n)))))
  : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (A n) else 0) := by
  sorry

theorem proof_gap_exercise_2706_2_7
  (h1 : a = (fun (n : ℕ) => ((-(1 : ℤ)) ^ n)))
  (h2 : b = (fun (n : ℕ) => ((-(1 : ℤ)) ^ (n + 1))))
  (h3 : c = (fun (n : ℕ) => ((a n) + (b n))))
  (h4 : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0))
  (h5 : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (b n) else 0))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((c n) = 0))))
  (h7 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (c n) else 0))
  (h8 : A = (fun (n : ℕ) => (1 /. n)))
  (h9 : B = (fun (n : ℕ) => (1 /. n)))
  (h10 : C = (fun (n : ℕ) => ((A n) + (B n))))
  (h11 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((C n) = (2 /. n)))))
  (h12 : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (A n) else 0))
  : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (B n) else 0) := by
  sorry

theorem proof_gap_exercise_2706_2_8
  (h1 : a = (fun (n : ℕ) => ((-(1 : ℤ)) ^ n)))
  (h2 : b = (fun (n : ℕ) => ((-(1 : ℤ)) ^ (n + 1))))
  (h3 : c = (fun (n : ℕ) => ((a n) + (b n))))
  (h4 : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0))
  (h5 : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (b n) else 0))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((c n) = 0))))
  (h7 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (c n) else 0))
  (h8 : A = (fun (n : ℕ) => (1 /. n)))
  (h9 : B = (fun (n : ℕ) => (1 /. n)))
  (h10 : C = (fun (n : ℕ) => ((A n) + (B n))))
  (h11 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((C n) = (2 /. n)))))
  (h12 : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (A n) else 0))
  (h13 : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (B n) else 0))
  : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (C n) else 0) := by
  sorry

theorem proof_gap_exercise_2706_2_9
  (h1 : a = (fun (n : ℕ) => ((-(1 : ℤ)) ^ n)))
  (h2 : b = (fun (n : ℕ) => ((-(1 : ℤ)) ^ (n + 1))))
  (h3 : c = (fun (n : ℕ) => ((a n) + (b n))))
  (h4 : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0))
  (h5 : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (b n) else 0))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((c n) = 0))))
  (h7 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (c n) else 0))
  (h8 : A = (fun (n : ℕ) => (1 /. n)))
  (h9 : B = (fun (n : ℕ) => (1 /. n)))
  (h10 : C = (fun (n : ℕ) => ((A n) + (B n))))
  (h11 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((C n) = (2 /. n)))))
  (h12 : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (A n) else 0))
  (h13 : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (B n) else 0))
  (h14 : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (C n) else 0))
  : (exists (a : (ℕ -> ℝ)) (b : (ℕ -> ℝ)) (c : (ℕ -> ℝ)), (((True ∧ (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0))) ∧ (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (b n) else 0))) ∧ (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (c n) else 0)))) := by
  sorry

theorem proof_gap_exercise_2706_2_10
  (h1 : a = (fun (n : ℕ) => ((-(1 : ℤ)) ^ n)))
  (h2 : b = (fun (n : ℕ) => ((-(1 : ℤ)) ^ (n + 1))))
  (h3 : c = (fun (n : ℕ) => ((a n) + (b n))))
  (h4 : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0))
  (h5 : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (b n) else 0))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((c n) = 0))))
  (h7 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (c n) else 0))
  (h8 : A = (fun (n : ℕ) => (1 /. n)))
  (h9 : B = (fun (n : ℕ) => (1 /. n)))
  (h10 : C = (fun (n : ℕ) => ((A n) + (B n))))
  (h11 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((C n) = (2 /. n)))))
  (h12 : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (A n) else 0))
  (h13 : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (B n) else 0))
  (h14 : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (C n) else 0))
  (h15 : (exists (a : (ℕ -> ℝ)) (b : (ℕ -> ℝ)) (c : (ℕ -> ℝ)), (((True ∧ (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0))) ∧ (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (b n) else 0))) ∧ (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (c n) else 0)))))
  : (exists (A : (ℕ -> ℝ)) (B : (ℕ -> ℝ)) (C : (ℕ -> ℝ)), (((True ∧ (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (A n) else 0))) ∧ (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (B n) else 0))) ∧ (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (C n) else 0)))) := by
  sorry

theorem proof_gap_exercise_2706_2_11
  (h1 : a = (fun (n : ℕ) => ((-(1 : ℤ)) ^ n)))
  (h2 : b = (fun (n : ℕ) => ((-(1 : ℤ)) ^ (n + 1))))
  (h3 : c = (fun (n : ℕ) => ((a n) + (b n))))
  (h4 : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0))
  (h5 : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (b n) else 0))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((c n) = 0))))
  (h7 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (c n) else 0))
  (h8 : A = (fun (n : ℕ) => (1 /. n)))
  (h9 : B = (fun (n : ℕ) => (1 /. n)))
  (h10 : C = (fun (n : ℕ) => ((A n) + (B n))))
  (h11 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((C n) = (2 /. n)))))
  (h12 : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (A n) else 0))
  (h13 : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (B n) else 0))
  (h14 : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (C n) else 0))
  (h15 : (exists (a : (ℕ -> ℝ)) (b : (ℕ -> ℝ)) (c : (ℕ -> ℝ)), (((True ∧ (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0))) ∧ (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (b n) else 0))) ∧ (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (c n) else 0)))))
  (h16 : (exists (A : (ℕ -> ℝ)) (B : (ℕ -> ℝ)) (C : (ℕ -> ℝ)), (((True ∧ (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (A n) else 0))) ∧ (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (B n) else 0))) ∧ (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (C n) else 0)))))
  : (forall (a : (ℕ -> ℝ)) (b : (ℕ -> ℝ)) (c : (ℕ -> ℝ)), ((((True ∧ (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((c n) = ((a n) + (b n)))))) ∧ (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0))) ∧ (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (b n) else 0))) → ((Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (c n) else 0)) ∨ (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (c n) else 0))))) := by
  sorry

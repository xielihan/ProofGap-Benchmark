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

-- exercise: exercise_3088

theorem proof_gap_exercise_3088_1
  (p : (ℕ -> ℝ))
  (v_uCE_uB1 : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((v_uCE_uB1 n) = (((-(1 : ℤ)) ^ (n + 1)) /. n)))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) = (1 + (v_uCE_uB1 n))))))
  : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (v_uCE_uB1 n) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((v_uCE_uB1 n))‖ else 0) := by
  sorry

theorem proof_gap_exercise_3088_2
  (p : (ℕ -> ℝ))
  (v_uCE_uB1 : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((v_uCE_uB1 n) = (((-(1 : ℤ)) ^ (n + 1)) /. n)))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) = (1 + (v_uCE_uB1 n))))))
  (h3 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (v_uCE_uB1 n) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((v_uCE_uB1 n))‖ else 0))
  : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((v_uCE_uB1 n) ^ (2 : ℕ)) else 0) := by
  sorry

theorem proof_gap_exercise_3088_3
  (p : (ℕ -> ℝ))
  (v_uCE_uB1 : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((v_uCE_uB1 n) = (((-(1 : ℤ)) ^ (n + 1)) /. n)))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) = (1 + (v_uCE_uB1 n))))))
  (h3 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (v_uCE_uB1 n) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((v_uCE_uB1 n))‖ else 0))
  (h4 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((v_uCE_uB1 n) ^ (2 : ℕ)) else 0))
  : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (Real.log (p n)) else 0) := by
  sorry

theorem proof_gap_exercise_3088_4
  (p : (ℕ -> ℝ))
  (v_uCE_uB1 : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((v_uCE_uB1 n) = (((-(1 : ℤ)) ^ (n + 1)) /. n)))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) = (1 + (v_uCE_uB1 n))))))
  (h3 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (v_uCE_uB1 n) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((v_uCE_uB1 n))‖ else 0))
  (h4 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((v_uCE_uB1 n) ^ (2 : ℕ)) else 0))
  (h5 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (Real.log (p n)) else 0))
  : Not (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((Real.log (p n)))‖ else 0)) := by
  sorry

theorem proof_gap_exercise_3088_5
  (p : (ℕ -> ℝ))
  (v_uCE_uB1 : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((v_uCE_uB1 n) = (((-(1 : ℤ)) ^ (n + 1)) /. n)))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) = (1 + (v_uCE_uB1 n))))))
  (h3 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (v_uCE_uB1 n) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((v_uCE_uB1 n))‖ else 0))
  (h4 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((v_uCE_uB1 n) ^ (2 : ℕ)) else 0))
  (h5 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (Real.log (p n)) else 0))
  (h6 : Not (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((Real.log (p n)))‖ else 0)))
  : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (Real.log (p n)) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((Real.log (p n)))‖ else 0) := by
  sorry

theorem proof_gap_exercise_3088_6
  (p : (ℕ -> ℝ))
  (v_uCE_uB1 : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((v_uCE_uB1 n) = (((-(1 : ℤ)) ^ (n + 1)) /. n)))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) = (1 + (v_uCE_uB1 n))))))
  (h3 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (v_uCE_uB1 n) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((v_uCE_uB1 n))‖ else 0))
  (h4 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((v_uCE_uB1 n) ^ (2 : ℕ)) else 0))
  (h5 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (Real.log (p n)) else 0))
  (h6 : Not (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((Real.log (p n)))‖ else 0)))
  (h7 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (Real.log (p n)) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((Real.log (p n)))‖ else 0))
  : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (Real.log (p n)) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((Real.log (p n)))‖ else 0) := by
  sorry

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

-- exercise: exercise_1394_1

theorem proof_gap_exercise_1394_1_1
  (R_Plus_n_1 : (ℝ -> ℝ))
  (x : ℝ)
  (n : ℕ)
  (v_uCE_uB8 : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℕ))
  (h3 : v_uCE_uB8 ∈ (Set.univ : Set ℝ))
  (h4 : 0 ≤ x)
  (h5 : x ≤ 1)
  (h6 : f = (fun (t : ℝ) => (Real.exp t)))
  : (Real.exp x) = ((∑ k ∈ Finset.Icc (0 : ℕ) n, ((x ^ k) /. (k)!)) + (R_Plus_n_1 x)) := by
  sorry

theorem proof_gap_exercise_1394_1_2
  (R_Plus_n_1 : (ℝ -> ℝ))
  (x : ℝ)
  (n : ℕ)
  (v_uCE_uB8 : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℕ))
  (h3 : v_uCE_uB8 ∈ (Set.univ : Set ℝ))
  (h4 : 0 ≤ x)
  (h5 : x ≤ 1)
  (h6 : f = (fun (t : ℝ) => (Real.exp t)))
  (h7 : (Real.exp x) = ((∑ k ∈ Finset.Icc (0 : ℕ) n, ((x ^ k) /. (k)!)) + (R_Plus_n_1 x)))
  : (R_Plus_n_1 x) = (((iteratedDeriv (n + 1) (fun t_1 => f t_1) (v_uCE_uB8 * x)) /. ((n + 1))!) * (x ^ (n + 1))) := by
  sorry

theorem proof_gap_exercise_1394_1_3
  (R_Plus_n_1 : (ℝ -> ℝ))
  (x : ℝ)
  (n : ℕ)
  (v_uCE_uB8 : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℕ))
  (h3 : v_uCE_uB8 ∈ (Set.univ : Set ℝ))
  (h4 : 0 ≤ x)
  (h5 : x ≤ 1)
  (h6 : f = (fun (t : ℝ) => (Real.exp t)))
  (h7 : (Real.exp x) = ((∑ k ∈ Finset.Icc (0 : ℕ) n, ((x ^ k) /. (k)!)) + (R_Plus_n_1 x)))
  (h8 : (R_Plus_n_1 x) = (((iteratedDeriv (n + 1) (fun t_1 => f t_1) (v_uCE_uB8 * x)) /. ((n + 1))!) * (x ^ (n + 1))))
  : 0 < v_uCE_uB8 := by
  sorry

theorem proof_gap_exercise_1394_1_4
  (R_Plus_n_1 : (ℝ -> ℝ))
  (x : ℝ)
  (n : ℕ)
  (v_uCE_uB8 : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℕ))
  (h3 : v_uCE_uB8 ∈ (Set.univ : Set ℝ))
  (h4 : 0 ≤ x)
  (h5 : x ≤ 1)
  (h6 : f = (fun (t : ℝ) => (Real.exp t)))
  (h7 : (Real.exp x) = ((∑ k ∈ Finset.Icc (0 : ℕ) n, ((x ^ k) /. (k)!)) + (R_Plus_n_1 x)))
  (h8 : (R_Plus_n_1 x) = (((iteratedDeriv (n + 1) (fun t_1 => f t_1) (v_uCE_uB8 * x)) /. ((n + 1))!) * (x ^ (n + 1))))
  (h9 : 0 < v_uCE_uB8)
  : v_uCE_uB8 < 1 := by
  sorry

theorem proof_gap_exercise_1394_1_5
  (R_Plus_n_1 : (ℝ -> ℝ))
  (x : ℝ)
  (n : ℕ)
  (v_uCE_uB8 : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℕ))
  (h3 : v_uCE_uB8 ∈ (Set.univ : Set ℝ))
  (h4 : 0 ≤ x)
  (h5 : x ≤ 1)
  (h6 : f = (fun (t : ℝ) => (Real.exp t)))
  (h7 : (Real.exp x) = ((∑ k ∈ Finset.Icc (0 : ℕ) n, ((x ^ k) /. (k)!)) + (R_Plus_n_1 x)))
  (h8 : (R_Plus_n_1 x) = (((iteratedDeriv (n + 1) (fun t_1 => f t_1) (v_uCE_uB8 * x)) /. ((n + 1))!) * (x ^ (n + 1))))
  (h9 : 0 < v_uCE_uB8)
  (h10 : v_uCE_uB8 < 1)
  : (iteratedDeriv (n + 1) (fun t_1 => f t_1) (v_uCE_uB8 * x)) = (Real.exp (v_uCE_uB8 * x)) := by
  sorry

theorem proof_gap_exercise_1394_1_6
  (R_Plus_n_1 : (ℝ -> ℝ))
  (x : ℝ)
  (n : ℕ)
  (v_uCE_uB8 : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℕ))
  (h3 : v_uCE_uB8 ∈ (Set.univ : Set ℝ))
  (h4 : 0 ≤ x)
  (h5 : x ≤ 1)
  (h6 : f = (fun (t : ℝ) => (Real.exp t)))
  (h7 : (Real.exp x) = ((∑ k ∈ Finset.Icc (0 : ℕ) n, ((x ^ k) /. (k)!)) + (R_Plus_n_1 x)))
  (h8 : (R_Plus_n_1 x) = (((iteratedDeriv (n + 1) (fun t_1 => f t_1) (v_uCE_uB8 * x)) /. ((n + 1))!) * (x ^ (n + 1))))
  (h9 : 0 < v_uCE_uB8)
  (h10 : v_uCE_uB8 < 1)
  (h11 : (iteratedDeriv (n + 1) (fun t_1 => f t_1) (v_uCE_uB8 * x)) = (Real.exp (v_uCE_uB8 * x)))
  : (Real.exp (v_uCE_uB8 * x)) < (Real.exp 1) := by
  sorry

theorem proof_gap_exercise_1394_1_7
  (R_Plus_n_1 : (ℝ -> ℝ))
  (x : ℝ)
  (n : ℕ)
  (v_uCE_uB8 : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℕ))
  (h3 : v_uCE_uB8 ∈ (Set.univ : Set ℝ))
  (h4 : 0 ≤ x)
  (h5 : x ≤ 1)
  (h6 : f = (fun (t : ℝ) => (Real.exp t)))
  (h7 : (Real.exp x) = ((∑ k ∈ Finset.Icc (0 : ℕ) n, ((x ^ k) /. (k)!)) + (R_Plus_n_1 x)))
  (h8 : (R_Plus_n_1 x) = (((iteratedDeriv (n + 1) (fun t_1 => f t_1) (v_uCE_uB8 * x)) /. ((n + 1))!) * (x ^ (n + 1))))
  (h9 : 0 < v_uCE_uB8)
  (h10 : v_uCE_uB8 < 1)
  (h11 : (iteratedDeriv (n + 1) (fun t_1 => f t_1) (v_uCE_uB8 * x)) = (Real.exp (v_uCE_uB8 * x)))
  (h12 : (Real.exp (v_uCE_uB8 * x)) < (Real.exp 1))
  : (iteratedDeriv (n + 1) (fun t_1 => f t_1) (v_uCE_uB8 * x)) < (Real.exp 1) := by
  sorry

theorem proof_gap_exercise_1394_1_8
  (R_Plus_n_1 : (ℝ -> ℝ))
  (x : ℝ)
  (n : ℕ)
  (v_uCE_uB8 : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℕ))
  (h3 : v_uCE_uB8 ∈ (Set.univ : Set ℝ))
  (h4 : 0 ≤ x)
  (h5 : x ≤ 1)
  (h6 : f = (fun (t : ℝ) => (Real.exp t)))
  (h7 : (Real.exp x) = ((∑ k ∈ Finset.Icc (0 : ℕ) n, ((x ^ k) /. (k)!)) + (R_Plus_n_1 x)))
  (h8 : (R_Plus_n_1 x) = (((iteratedDeriv (n + 1) (fun t_1 => f t_1) (v_uCE_uB8 * x)) /. ((n + 1))!) * (x ^ (n + 1))))
  (h9 : 0 < v_uCE_uB8)
  (h10 : v_uCE_uB8 < 1)
  (h11 : (iteratedDeriv (n + 1) (fun t_1 => f t_1) (v_uCE_uB8 * x)) = (Real.exp (v_uCE_uB8 * x)))
  (h12 : (Real.exp (v_uCE_uB8 * x)) < (Real.exp 1))
  (h13 : (iteratedDeriv (n + 1) (fun t_1 => f t_1) (v_uCE_uB8 * x)) < (Real.exp 1))
  : |((R_Plus_n_1 x))| < (((Real.exp 1) /. ((n + 1))!) * (|(x)| ^ (n + 1))) := by
  sorry

theorem proof_gap_exercise_1394_1_9
  (R_Plus_n_1 : (ℝ -> ℝ))
  (x : ℝ)
  (n : ℕ)
  (v_uCE_uB8 : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℕ))
  (h3 : v_uCE_uB8 ∈ (Set.univ : Set ℝ))
  (h4 : 0 ≤ x)
  (h5 : x ≤ 1)
  (h6 : f = (fun (t : ℝ) => (Real.exp t)))
  (h7 : (Real.exp x) = ((∑ k ∈ Finset.Icc (0 : ℕ) n, ((x ^ k) /. (k)!)) + (R_Plus_n_1 x)))
  (h8 : (R_Plus_n_1 x) = (((iteratedDeriv (n + 1) (fun t_1 => f t_1) (v_uCE_uB8 * x)) /. ((n + 1))!) * (x ^ (n + 1))))
  (h9 : 0 < v_uCE_uB8)
  (h10 : v_uCE_uB8 < 1)
  (h11 : (iteratedDeriv (n + 1) (fun t_1 => f t_1) (v_uCE_uB8 * x)) = (Real.exp (v_uCE_uB8 * x)))
  (h12 : (Real.exp (v_uCE_uB8 * x)) < (Real.exp 1))
  (h13 : (iteratedDeriv (n + 1) (fun t_1 => f t_1) (v_uCE_uB8 * x)) < (Real.exp 1))
  (h14 : |((R_Plus_n_1 x))| < (((Real.exp 1) /. ((n + 1))!) * (|(x)| ^ (n + 1))))
  : (((Real.exp 1) /. ((n + 1))!) * (|(x)| ^ (n + 1))) ≤ ((Real.exp 1) /. ((n + 1))!) := by
  sorry

theorem proof_gap_exercise_1394_1_10
  (R_Plus_n_1 : (ℝ -> ℝ))
  (x : ℝ)
  (n : ℕ)
  (v_uCE_uB8 : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℕ))
  (h3 : v_uCE_uB8 ∈ (Set.univ : Set ℝ))
  (h4 : 0 ≤ x)
  (h5 : x ≤ 1)
  (h6 : f = (fun (t : ℝ) => (Real.exp t)))
  (h7 : (Real.exp x) = ((∑ k ∈ Finset.Icc (0 : ℕ) n, ((x ^ k) /. (k)!)) + (R_Plus_n_1 x)))
  (h8 : (R_Plus_n_1 x) = (((iteratedDeriv (n + 1) (fun t_1 => f t_1) (v_uCE_uB8 * x)) /. ((n + 1))!) * (x ^ (n + 1))))
  (h9 : 0 < v_uCE_uB8)
  (h10 : v_uCE_uB8 < 1)
  (h11 : (iteratedDeriv (n + 1) (fun t_1 => f t_1) (v_uCE_uB8 * x)) = (Real.exp (v_uCE_uB8 * x)))
  (h12 : (Real.exp (v_uCE_uB8 * x)) < (Real.exp 1))
  (h13 : (iteratedDeriv (n + 1) (fun t_1 => f t_1) (v_uCE_uB8 * x)) < (Real.exp 1))
  (h14 : |((R_Plus_n_1 x))| < (((Real.exp 1) /. ((n + 1))!) * (|(x)| ^ (n + 1))))
  (h15 : (((Real.exp 1) /. ((n + 1))!) * (|(x)| ^ (n + 1))) ≤ ((Real.exp 1) /. ((n + 1))!))
  : ((Real.exp 1) /. ((n + 1))!) < (3 /. ((n + 1))!) := by
  sorry

theorem proof_gap_exercise_1394_1_11
  (R_Plus_n_1 : (ℝ -> ℝ))
  (x : ℝ)
  (n : ℕ)
  (v_uCE_uB8 : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℕ))
  (h3 : v_uCE_uB8 ∈ (Set.univ : Set ℝ))
  (h4 : 0 ≤ x)
  (h5 : x ≤ 1)
  (h6 : f = (fun (t : ℝ) => (Real.exp t)))
  (h7 : (Real.exp x) = ((∑ k ∈ Finset.Icc (0 : ℕ) n, ((x ^ k) /. (k)!)) + (R_Plus_n_1 x)))
  (h8 : (R_Plus_n_1 x) = (((iteratedDeriv (n + 1) (fun t_1 => f t_1) (v_uCE_uB8 * x)) /. ((n + 1))!) * (x ^ (n + 1))))
  (h9 : 0 < v_uCE_uB8)
  (h10 : v_uCE_uB8 < 1)
  (h11 : (iteratedDeriv (n + 1) (fun t_1 => f t_1) (v_uCE_uB8 * x)) = (Real.exp (v_uCE_uB8 * x)))
  (h12 : (Real.exp (v_uCE_uB8 * x)) < (Real.exp 1))
  (h13 : (iteratedDeriv (n + 1) (fun t_1 => f t_1) (v_uCE_uB8 * x)) < (Real.exp 1))
  (h14 : |((R_Plus_n_1 x))| < (((Real.exp 1) /. ((n + 1))!) * (|(x)| ^ (n + 1))))
  (h15 : (((Real.exp 1) /. ((n + 1))!) * (|(x)| ^ (n + 1))) ≤ ((Real.exp 1) /. ((n + 1))!))
  (h16 : ((Real.exp 1) /. ((n + 1))!) < (3 /. ((n + 1))!))
  : |((R_Plus_n_1 x))| < (3 /. ((n + 1))!) := by
  sorry

theorem proof_gap_exercise_1394_1_12
  (R_Plus_n_1 : (ℝ -> ℝ))
  (x : ℝ)
  (n : ℕ)
  (v_uCE_uB8 : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℕ))
  (h3 : v_uCE_uB8 ∈ (Set.univ : Set ℝ))
  (h4 : 0 ≤ x)
  (h5 : x ≤ 1)
  (h6 : f = (fun (t : ℝ) => (Real.exp t)))
  (h7 : (Real.exp x) = ((∑ k ∈ Finset.Icc (0 : ℕ) n, ((x ^ k) /. (k)!)) + (R_Plus_n_1 x)))
  (h8 : (R_Plus_n_1 x) = (((iteratedDeriv (n + 1) (fun t_1 => f t_1) (v_uCE_uB8 * x)) /. ((n + 1))!) * (x ^ (n + 1))))
  (h9 : 0 < v_uCE_uB8)
  (h10 : v_uCE_uB8 < 1)
  (h11 : (iteratedDeriv (n + 1) (fun t_1 => f t_1) (v_uCE_uB8 * x)) = (Real.exp (v_uCE_uB8 * x)))
  (h12 : (Real.exp (v_uCE_uB8 * x)) < (Real.exp 1))
  (h13 : (iteratedDeriv (n + 1) (fun t_1 => f t_1) (v_uCE_uB8 * x)) < (Real.exp 1))
  (h14 : |((R_Plus_n_1 x))| < (((Real.exp 1) /. ((n + 1))!) * (|(x)| ^ (n + 1))))
  (h15 : (((Real.exp 1) /. ((n + 1))!) * (|(x)| ^ (n + 1))) ≤ ((Real.exp 1) /. ((n + 1))!))
  (h16 : ((Real.exp 1) /. ((n + 1))!) < (3 /. ((n + 1))!))
  (h17 : |((R_Plus_n_1 x))| < (3 /. ((n + 1))!))
  : |((R_Plus_n_1 x))| < (3 /. ((n + 1))!) := by
  sorry

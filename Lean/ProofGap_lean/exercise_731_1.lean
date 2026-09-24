import Mathlib

attribute [local instance] Classical.propDecidable

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

-- exercise: exercise_731_1

theorem proof_gap_exercise_731_1_1
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 2))) → ((f x) = (if ((0 ≤ x) ∧ (x ≤ 1)) then (x ^ (2 : ℕ)) else (if ((1 < x) ∧ (x ≤ 2)) then (2 - x) else (2 - x)))))))
  : (let _ : ((Set.Icc 0 1)) ⊆ ({ x_1 : ℝ | (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x_1)) ∧ (x_1 ≤ 1)) }) := (by intro x hx; simpa only [Set.mem_ofPred_eq, Set.mem_univ, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Ioi, Set.mem_Iic, Set.mem_Iio, Set.mem_prod, true_and, and_true, and_assoc, and_left_comm, and_comm] using hx); (ContinuousOn (fun (x : ℝ) => (x ^ (2 : ℕ))) (Set.Icc 0 1))) := by
  sorry

theorem proof_gap_exercise_731_1_2
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 2))) → ((f x) = (if ((0 ≤ x) ∧ (x ≤ 1)) then (x ^ (2 : ℕ)) else (if ((1 < x) ∧ (x ≤ 2)) then (2 - x) else (2 - x)))))))
  (h2 : (let _ : ((Set.Icc 0 1)) ⊆ ({ x_1 : ℝ | (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x_1)) ∧ (x_1 ≤ 1)) }) := (by intro x hx; simpa only [Set.mem_ofPred_eq, Set.mem_univ, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Ioi, Set.mem_Iic, Set.mem_Iio, Set.mem_prod, true_and, and_true, and_assoc, and_left_comm, and_comm] using hx); (ContinuousOn (fun (x : ℝ) => (x ^ (2 : ℕ))) (Set.Icc 0 1))))
  : (let _ : ((Set.Ioc 1 2)) ⊆ ({ x_1 : ℝ | (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (1 < x_1)) ∧ (x_1 ≤ 2)) }) := (by intro x hx; simpa only [Set.mem_ofPred_eq, Set.mem_univ, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Ioi, Set.mem_Iic, Set.mem_Iio, Set.mem_prod, true_and, and_true, and_assoc, and_left_comm, and_comm] using hx); (ContinuousOn (fun (x : ℝ) => (2 - x)) (Set.Ioc 1 2))) := by
  sorry

theorem proof_gap_exercise_731_1_3
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 2))) → ((f x) = (if ((0 ≤ x) ∧ (x ≤ 1)) then (x ^ (2 : ℕ)) else (if ((1 < x) ∧ (x ≤ 2)) then (2 - x) else (2 - x)))))))
  (h2 : (let _ : ((Set.Icc 0 1)) ⊆ ({ x_1 : ℝ | (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x_1)) ∧ (x_1 ≤ 1)) }) := (by intro x hx; simpa only [Set.mem_ofPred_eq, Set.mem_univ, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Ioi, Set.mem_Iic, Set.mem_Iio, Set.mem_prod, true_and, and_true, and_assoc, and_left_comm, and_comm] using hx); (ContinuousOn (fun (x : ℝ) => (x ^ (2 : ℕ))) (Set.Icc 0 1))))
  (h3 : (let _ : ((Set.Ioc 1 2)) ⊆ ({ x_1 : ℝ | (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (1 < x_1)) ∧ (x_1 ≤ 2)) }) := (by intro x hx; simpa only [Set.mem_ofPred_eq, Set.mem_univ, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Ioi, Set.mem_Iic, Set.mem_Iio, Set.mem_prod, true_and, and_true, and_assoc, and_left_comm, and_comm] using hx); (ContinuousOn (fun (x : ℝ) => (2 - x)) (Set.Ioc 1 2))))
  : (f (1 : ℝ)) = 1 := by
  sorry

theorem proof_gap_exercise_731_1_4
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 2))) → ((f x) = (if ((0 ≤ x) ∧ (x ≤ 1)) then (x ^ (2 : ℕ)) else (if ((1 < x) ∧ (x ≤ 2)) then (2 - x) else (2 - x)))))))
  (h2 : (let _ : ((Set.Icc 0 1)) ⊆ ({ x_1 : ℝ | (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x_1)) ∧ (x_1 ≤ 1)) }) := (by intro x hx; simpa only [Set.mem_ofPred_eq, Set.mem_univ, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Ioi, Set.mem_Iic, Set.mem_Iio, Set.mem_prod, true_and, and_true, and_assoc, and_left_comm, and_comm] using hx); (ContinuousOn (fun (x : ℝ) => (x ^ (2 : ℕ))) (Set.Icc 0 1))))
  (h3 : (let _ : ((Set.Ioc 1 2)) ⊆ ({ x_1 : ℝ | (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (1 < x_1)) ∧ (x_1 ≤ 2)) }) := (by intro x hx; simpa only [Set.mem_ofPred_eq, Set.mem_univ, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Ioi, Set.mem_Iic, Set.mem_Iio, Set.mem_prod, true_and, and_true, and_assoc, and_left_comm, and_comm] using hx); (ContinuousOn (fun (x : ℝ) => (2 - x)) (Set.Ioc 1 2))))
  (h4 : (f (1 : ℝ)) = 1)
  : Tendsto (fun x : ℝ => (f x)) (𝓝[<] 1) (𝓝 1) := by
  sorry

theorem proof_gap_exercise_731_1_5
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 2))) → ((f x) = (if ((0 ≤ x) ∧ (x ≤ 1)) then (x ^ (2 : ℕ)) else (if ((1 < x) ∧ (x ≤ 2)) then (2 - x) else (2 - x)))))))
  (h2 : (let _ : ((Set.Icc 0 1)) ⊆ ({ x_1 : ℝ | (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x_1)) ∧ (x_1 ≤ 1)) }) := (by intro x hx; simpa only [Set.mem_ofPred_eq, Set.mem_univ, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Ioi, Set.mem_Iic, Set.mem_Iio, Set.mem_prod, true_and, and_true, and_assoc, and_left_comm, and_comm] using hx); (ContinuousOn (fun (x : ℝ) => (x ^ (2 : ℕ))) (Set.Icc 0 1))))
  (h3 : (let _ : ((Set.Ioc 1 2)) ⊆ ({ x_1 : ℝ | (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (1 < x_1)) ∧ (x_1 ≤ 2)) }) := (by intro x hx; simpa only [Set.mem_ofPred_eq, Set.mem_univ, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Ioi, Set.mem_Iic, Set.mem_Iio, Set.mem_prod, true_and, and_true, and_assoc, and_left_comm, and_comm] using hx); (ContinuousOn (fun (x : ℝ) => (2 - x)) (Set.Ioc 1 2))))
  (h4 : (f (1 : ℝ)) = 1)
  (h5 : Tendsto (fun x : ℝ => (f x)) (𝓝[<] 1) (𝓝 1))
  : Tendsto (fun x : ℝ => (f x)) (𝓝[>] 1) (𝓝 1) := by
  sorry

theorem proof_gap_exercise_731_1_6
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 2))) → ((f x) = (if ((0 ≤ x) ∧ (x ≤ 1)) then (x ^ (2 : ℕ)) else (if ((1 < x) ∧ (x ≤ 2)) then (2 - x) else (2 - x)))))))
  (h2 : (let _ : ((Set.Icc 0 1)) ⊆ ({ x_1 : ℝ | (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x_1)) ∧ (x_1 ≤ 1)) }) := (by intro x hx; simpa only [Set.mem_ofPred_eq, Set.mem_univ, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Ioi, Set.mem_Iic, Set.mem_Iio, Set.mem_prod, true_and, and_true, and_assoc, and_left_comm, and_comm] using hx); (ContinuousOn (fun (x : ℝ) => (x ^ (2 : ℕ))) (Set.Icc 0 1))))
  (h3 : (let _ : ((Set.Ioc 1 2)) ⊆ ({ x_1 : ℝ | (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (1 < x_1)) ∧ (x_1 ≤ 2)) }) := (by intro x hx; simpa only [Set.mem_ofPred_eq, Set.mem_univ, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Ioi, Set.mem_Iic, Set.mem_Iio, Set.mem_prod, true_and, and_true, and_assoc, and_left_comm, and_comm] using hx); (ContinuousOn (fun (x : ℝ) => (2 - x)) (Set.Ioc 1 2))))
  (h4 : (f (1 : ℝ)) = 1)
  (h5 : Tendsto (fun x : ℝ => (f x)) (𝓝[<] 1) (𝓝 1))
  (h6 : Tendsto (fun x : ℝ => (f x)) (𝓝[>] 1) (𝓝 1))
  : ContinuousAt f 1 := by
  sorry

theorem proof_gap_exercise_731_1_7
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 2))) → ((f x) = (if ((0 ≤ x) ∧ (x ≤ 1)) then (x ^ (2 : ℕ)) else (if ((1 < x) ∧ (x ≤ 2)) then (2 - x) else (2 - x)))))))
  (h2 : (let _ : ((Set.Icc 0 1)) ⊆ ({ x_1 : ℝ | (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x_1)) ∧ (x_1 ≤ 1)) }) := (by intro x hx; simpa only [Set.mem_ofPred_eq, Set.mem_univ, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Ioi, Set.mem_Iic, Set.mem_Iio, Set.mem_prod, true_and, and_true, and_assoc, and_left_comm, and_comm] using hx); (ContinuousOn (fun (x : ℝ) => (x ^ (2 : ℕ))) (Set.Icc 0 1))))
  (h3 : (let _ : ((Set.Ioc 1 2)) ⊆ ({ x_1 : ℝ | (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (1 < x_1)) ∧ (x_1 ≤ 2)) }) := (by intro x hx; simpa only [Set.mem_ofPred_eq, Set.mem_univ, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Ioi, Set.mem_Iic, Set.mem_Iio, Set.mem_prod, true_and, and_true, and_assoc, and_left_comm, and_comm] using hx); (ContinuousOn (fun (x : ℝ) => (2 - x)) (Set.Ioc 1 2))))
  (h4 : (f (1 : ℝ)) = 1)
  (h5 : Tendsto (fun x : ℝ => (f x)) (𝓝[<] 1) (𝓝 1))
  (h6 : Tendsto (fun x : ℝ => (f x)) (𝓝[>] 1) (𝓝 1))
  (h7 : ContinuousAt f 1)
  : ContinuousOn f (Set.Icc 0 2) := by
  sorry

theorem proof_gap_exercise_731_1_8
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 2))) → ((f x) = (if ((0 ≤ x) ∧ (x ≤ 1)) then (x ^ (2 : ℕ)) else (if ((1 < x) ∧ (x ≤ 2)) then (2 - x) else (2 - x)))))))
  (h2 : (let _ : ((Set.Icc 0 1)) ⊆ ({ x_1 : ℝ | (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x_1)) ∧ (x_1 ≤ 1)) }) := (by intro x hx; simpa only [Set.mem_ofPred_eq, Set.mem_univ, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Ioi, Set.mem_Iic, Set.mem_Iio, Set.mem_prod, true_and, and_true, and_assoc, and_left_comm, and_comm] using hx); (ContinuousOn (fun (x : ℝ) => (x ^ (2 : ℕ))) (Set.Icc 0 1))))
  (h3 : (let _ : ((Set.Ioc 1 2)) ⊆ ({ x_1 : ℝ | (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (1 < x_1)) ∧ (x_1 ≤ 2)) }) := (by intro x hx; simpa only [Set.mem_ofPred_eq, Set.mem_univ, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Ioi, Set.mem_Iic, Set.mem_Iio, Set.mem_prod, true_and, and_true, and_assoc, and_left_comm, and_comm] using hx); (ContinuousOn (fun (x : ℝ) => (2 - x)) (Set.Ioc 1 2))))
  (h4 : (f (1 : ℝ)) = 1)
  (h5 : Tendsto (fun x : ℝ => (f x)) (𝓝[<] 1) (𝓝 1))
  (h6 : Tendsto (fun x : ℝ => (f x)) (𝓝[>] 1) (𝓝 1))
  (h7 : ContinuousAt f 1)
  (h8 : ContinuousOn f (Set.Icc 0 2))
  : ContinuousOn f (Set.Icc 0 2) := by
  sorry

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

-- exercise: exercise_3058

theorem proof_gap_exercise_3058_1
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |(x)| < 1)
  (h3 : P = (fun (n : ℕ) => (∏ k ∈ Finset.Icc (0 : ℕ) n, (1 + (x ^ ((2 : ℕ) ^ k))))))
  : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((((1 - x) * (P n)) = ((1 - x) * (∏ k ∈ Finset.Icc (0 : ℕ) n, (1 + (x ^ ((2 : ℕ) ^ k)))))) ∧ (((1 - x) * (∏ k ∈ Finset.Icc (0 : ℕ) n, (1 + (x ^ ((2 : ℕ) ^ k))))) = (1 - (x ^ ((2 : ℕ) ^ (n + 1)))))))) := by
  sorry

theorem proof_gap_exercise_3058_2
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |(x)| < 1)
  (h3 : P = (fun (n : ℕ) => (∏ k ∈ Finset.Icc (0 : ℕ) n, (1 + (x ^ ((2 : ℕ) ^ k))))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((((1 - x) * (P n)) = ((1 - x) * (∏ k ∈ Finset.Icc (0 : ℕ) n, (1 + (x ^ ((2 : ℕ) ^ k)))))) ∧ (((1 - x) * (∏ k ∈ Finset.Icc (0 : ℕ) n, (1 + (x ^ ((2 : ℕ) ^ k))))) = (1 - (x ^ ((2 : ℕ) ^ (n + 1)))))))))
  : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((P n) = ((1 - (x ^ ((2 : ℕ) ^ (n + 1)))) /. (1 - x))))) := by
  sorry

theorem proof_gap_exercise_3058_3
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |(x)| < 1)
  (h3 : P = (fun (n : ℕ) => (∏ k ∈ Finset.Icc (0 : ℕ) n, (1 + (x ^ ((2 : ℕ) ^ k))))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((((1 - x) * (P n)) = ((1 - x) * (∏ k ∈ Finset.Icc (0 : ℕ) n, (1 + (x ^ ((2 : ℕ) ^ k)))))) ∧ (((1 - x) * (∏ k ∈ Finset.Icc (0 : ℕ) n, (1 + (x ^ ((2 : ℕ) ^ k))))) = (1 - (x ^ ((2 : ℕ) ^ (n + 1)))))))))
  (h5 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((P n) = ((1 - (x ^ ((2 : ℕ) ^ (n + 1)))) /. (1 - x))))))
  : Tendsto (fun n : ℕ => (Real.rpow x (Real.rpow (2 : ℝ) (n + 1)))) atTop (𝓝 0) := by
  sorry

theorem proof_gap_exercise_3058_4
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |(x)| < 1)
  (h3 : P = (fun (n : ℕ) => (∏ k ∈ Finset.Icc (0 : ℕ) n, (1 + (x ^ ((2 : ℕ) ^ k))))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((((1 - x) * (P n)) = ((1 - x) * (∏ k ∈ Finset.Icc (0 : ℕ) n, (1 + (x ^ ((2 : ℕ) ^ k)))))) ∧ (((1 - x) * (∏ k ∈ Finset.Icc (0 : ℕ) n, (1 + (x ^ ((2 : ℕ) ^ k))))) = (1 - (x ^ ((2 : ℕ) ^ (n + 1)))))))))
  (h5 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((P n) = ((1 - (x ^ ((2 : ℕ) ^ (n + 1)))) /. (1 - x))))))
  (h6 : Tendsto (fun n : ℕ => (Real.rpow x (Real.rpow (2 : ℝ) (n + 1)))) atTop (𝓝 0))
  : Tendsto (fun n : ℕ => (P n)) atTop (𝓝 (1 /. (1 - x))) := by
  sorry

theorem proof_gap_exercise_3058_5
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |(x)| < 1)
  (h3 : P = (fun (n : ℕ) => (∏ k ∈ Finset.Icc (0 : ℕ) n, (1 + (x ^ ((2 : ℕ) ^ k))))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((((1 - x) * (P n)) = ((1 - x) * (∏ k ∈ Finset.Icc (0 : ℕ) n, (1 + (x ^ ((2 : ℕ) ^ k)))))) ∧ (((1 - x) * (∏ k ∈ Finset.Icc (0 : ℕ) n, (1 + (x ^ ((2 : ℕ) ^ k))))) = (1 - (x ^ ((2 : ℕ) ^ (n + 1)))))))))
  (h5 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((P n) = ((1 - (x ^ ((2 : ℕ) ^ (n + 1)))) /. (1 - x))))))
  (h6 : Tendsto (fun n : ℕ => (Real.rpow x (Real.rpow (2 : ℝ) (n + 1)))) atTop (𝓝 0))
  (h7 : Tendsto (fun n : ℕ => (P n)) atTop (𝓝 (1 /. (1 - x))))
  : (∏' n, if (0 : ℕ) ≤ n then (1 + (x ^ ((2 : ℕ) ^ n))) else 1) = (1 /. (1 - x)) := by
  sorry

theorem proof_gap_exercise_3058_6
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |(x)| < 1)
  (h3 : P = (fun (n : ℕ) => (∏ k ∈ Finset.Icc (0 : ℕ) n, (1 + (x ^ ((2 : ℕ) ^ k))))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((((1 - x) * (P n)) = ((1 - x) * (∏ k ∈ Finset.Icc (0 : ℕ) n, (1 + (x ^ ((2 : ℕ) ^ k)))))) ∧ (((1 - x) * (∏ k ∈ Finset.Icc (0 : ℕ) n, (1 + (x ^ ((2 : ℕ) ^ k))))) = (1 - (x ^ ((2 : ℕ) ^ (n + 1)))))))))
  (h5 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((P n) = ((1 - (x ^ ((2 : ℕ) ^ (n + 1)))) /. (1 - x))))))
  (h6 : Tendsto (fun n : ℕ => (Real.rpow x (Real.rpow (2 : ℝ) (n + 1)))) atTop (𝓝 0))
  (h7 : Tendsto (fun n : ℕ => (P n)) atTop (𝓝 (1 /. (1 - x))))
  (h8 : (∏' n, if (0 : ℕ) ≤ n then (1 + (x ^ ((2 : ℕ) ^ n))) else 1) = (1 /. (1 - x)))
  : (∏' n, if (0 : ℕ) ≤ n then (1 + ((1 /. 2) ^ ((2 : ℕ) ^ n))) else 1) = (1 /. (1 - (1 /. 2))) := by
  sorry

theorem proof_gap_exercise_3058_7
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |(x)| < 1)
  (h3 : P = (fun (n : ℕ) => (∏ k ∈ Finset.Icc (0 : ℕ) n, (1 + (x ^ ((2 : ℕ) ^ k))))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((((1 - x) * (P n)) = ((1 - x) * (∏ k ∈ Finset.Icc (0 : ℕ) n, (1 + (x ^ ((2 : ℕ) ^ k)))))) ∧ (((1 - x) * (∏ k ∈ Finset.Icc (0 : ℕ) n, (1 + (x ^ ((2 : ℕ) ^ k))))) = (1 - (x ^ ((2 : ℕ) ^ (n + 1)))))))))
  (h5 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((P n) = ((1 - (x ^ ((2 : ℕ) ^ (n + 1)))) /. (1 - x))))))
  (h6 : Tendsto (fun n : ℕ => (Real.rpow x (Real.rpow (2 : ℝ) (n + 1)))) atTop (𝓝 0))
  (h7 : Tendsto (fun n : ℕ => (P n)) atTop (𝓝 (1 /. (1 - x))))
  (h8 : (∏' n, if (0 : ℕ) ≤ n then (1 + (x ^ ((2 : ℕ) ^ n))) else 1) = (1 /. (1 - x)))
  (h9 : (∏' n, if (0 : ℕ) ≤ n then (1 + ((1 /. 2) ^ ((2 : ℕ) ^ n))) else 1) = (1 /. (1 - (1 /. 2))))
  : (1 /. (1 - (1 /. 2))) = 2 := by
  sorry

theorem proof_gap_exercise_3058_8
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |(x)| < 1)
  (h3 : P = (fun (n : ℕ) => (∏ k ∈ Finset.Icc (0 : ℕ) n, (1 + (x ^ ((2 : ℕ) ^ k))))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((((1 - x) * (P n)) = ((1 - x) * (∏ k ∈ Finset.Icc (0 : ℕ) n, (1 + (x ^ ((2 : ℕ) ^ k)))))) ∧ (((1 - x) * (∏ k ∈ Finset.Icc (0 : ℕ) n, (1 + (x ^ ((2 : ℕ) ^ k))))) = (1 - (x ^ ((2 : ℕ) ^ (n + 1)))))))))
  (h5 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((P n) = ((1 - (x ^ ((2 : ℕ) ^ (n + 1)))) /. (1 - x))))))
  (h6 : Tendsto (fun n : ℕ => (Real.rpow x (Real.rpow (2 : ℝ) (n + 1)))) atTop (𝓝 0))
  (h7 : Tendsto (fun n : ℕ => (P n)) atTop (𝓝 (1 /. (1 - x))))
  (h8 : (∏' n, if (0 : ℕ) ≤ n then (1 + (x ^ ((2 : ℕ) ^ n))) else 1) = (1 /. (1 - x)))
  (h9 : (∏' n, if (0 : ℕ) ≤ n then (1 + ((1 /. 2) ^ ((2 : ℕ) ^ n))) else 1) = (1 /. (1 - (1 /. 2))))
  (h10 : (1 /. (1 - (1 /. 2))) = 2)
  : (∏' n, if (0 : ℕ) ≤ n then (1 + ((1 /. 2) ^ ((2 : ℕ) ^ n))) else 1) = 2 := by
  sorry

theorem proof_gap_exercise_3058_9
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |(x)| < 1)
  (h3 : P = (fun (n : ℕ) => (∏ k ∈ Finset.Icc (0 : ℕ) n, (1 + (x ^ ((2 : ℕ) ^ k))))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((((1 - x) * (P n)) = ((1 - x) * (∏ k ∈ Finset.Icc (0 : ℕ) n, (1 + (x ^ ((2 : ℕ) ^ k)))))) ∧ (((1 - x) * (∏ k ∈ Finset.Icc (0 : ℕ) n, (1 + (x ^ ((2 : ℕ) ^ k))))) = (1 - (x ^ ((2 : ℕ) ^ (n + 1)))))))))
  (h5 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((P n) = ((1 - (x ^ ((2 : ℕ) ^ (n + 1)))) /. (1 - x))))))
  (h6 : Tendsto (fun n : ℕ => (Real.rpow x (Real.rpow (2 : ℝ) (n + 1)))) atTop (𝓝 0))
  (h7 : Tendsto (fun n : ℕ => (P n)) atTop (𝓝 (1 /. (1 - x))))
  (h8 : (∏' n, if (0 : ℕ) ≤ n then (1 + (x ^ ((2 : ℕ) ^ n))) else 1) = (1 /. (1 - x)))
  (h9 : (∏' n, if (0 : ℕ) ≤ n then (1 + ((1 /. 2) ^ ((2 : ℕ) ^ n))) else 1) = (1 /. (1 - (1 /. 2))))
  (h10 : (1 /. (1 - (1 /. 2))) = 2)
  (h11 : (∏' n, if (0 : ℕ) ≤ n then (1 + ((1 /. 2) ^ ((2 : ℕ) ^ n))) else 1) = 2)
  : (∏' n, if (0 : ℕ) ≤ n then (1 + (x ^ ((2 : ℕ) ^ n))) else 1) = (1 /. (1 - x)) := by
  sorry

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

-- exercise: exercise_2734

theorem proof_gap_exercise_2734_1
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (y : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : y ∈ (Set.univ : Set ℝ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (Real.rpow ((|(x)| ^ (n ^ (2 : ℕ))) + (|(y)| ^ (n ^ (2 : ℕ)))) (((n : ℝ))⁻¹))))))
  : ((max |(x)| |(y)|) > 0) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((Real.rpow (((|(x)| /. (max |(x)| |(y)|)) ^ (n ^ (2 : ℕ))) + ((|(y)| /. (max |(x)| |(y)|)) ^ (n ^ (2 : ℕ)))) (((n : ℝ))⁻¹)) * ((max |(x)| |(y)|) ^ n))))) := by
  sorry

theorem proof_gap_exercise_2734_2
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (y : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : y ∈ (Set.univ : Set ℝ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (Real.rpow ((|(x)| ^ (n ^ (2 : ℕ))) + (|(y)| ^ (n ^ (2 : ℕ)))) (((n : ℝ))⁻¹))))))
  (h4 : ((max |(x)| |(y)|) > 0) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((Real.rpow (((|(x)| /. (max |(x)| |(y)|)) ^ (n ^ (2 : ℕ))) + ((|(y)| /. (max |(x)| |(y)|)) ^ (n ^ (2 : ℕ)))) (((n : ℝ))⁻¹)) * ((max |(x)| |(y)|) ^ n))))))
  : ((max |(x)| |(y)|) > 0) → (Tendsto (fun n : ℕ => (Real.rpow (a n) ((n)⁻¹))) atTop (𝓝 (max |(x)| |(y)|))) := by
  sorry

theorem proof_gap_exercise_2734_3
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (y : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : y ∈ (Set.univ : Set ℝ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (Real.rpow ((|(x)| ^ (n ^ (2 : ℕ))) + (|(y)| ^ (n ^ (2 : ℕ)))) (((n : ℝ))⁻¹))))))
  (h4 : ((max |(x)| |(y)|) > 0) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((Real.rpow (((|(x)| /. (max |(x)| |(y)|)) ^ (n ^ (2 : ℕ))) + ((|(y)| /. (max |(x)| |(y)|)) ^ (n ^ (2 : ℕ)))) (((n : ℝ))⁻¹)) * ((max |(x)| |(y)|) ^ n))))))
  (h5 : ((max |(x)| |(y)|) > 0) → (Tendsto (fun n : ℕ => (Real.rpow (a n) ((n)⁻¹))) atTop (𝓝 (max |(x)| |(y)|))))
  : ((max |(x)| |(y)|) < 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0)) := by
  sorry

theorem proof_gap_exercise_2734_4
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (y : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : y ∈ (Set.univ : Set ℝ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (Real.rpow ((|(x)| ^ (n ^ (2 : ℕ))) + (|(y)| ^ (n ^ (2 : ℕ)))) (((n : ℝ))⁻¹))))))
  (h4 : ((max |(x)| |(y)|) > 0) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((Real.rpow (((|(x)| /. (max |(x)| |(y)|)) ^ (n ^ (2 : ℕ))) + ((|(y)| /. (max |(x)| |(y)|)) ^ (n ^ (2 : ℕ)))) (((n : ℝ))⁻¹)) * ((max |(x)| |(y)|) ^ n))))))
  (h5 : ((max |(x)| |(y)|) > 0) → (Tendsto (fun n : ℕ => (Real.rpow (a n) ((n)⁻¹))) atTop (𝓝 (max |(x)| |(y)|))))
  (h6 : ((max |(x)| |(y)|) < 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0)))
  : ((max |(x)| |(y)|) > 1) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)) := by
  sorry

theorem proof_gap_exercise_2734_5
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (y : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : y ∈ (Set.univ : Set ℝ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (Real.rpow ((|(x)| ^ (n ^ (2 : ℕ))) + (|(y)| ^ (n ^ (2 : ℕ)))) (((n : ℝ))⁻¹))))))
  (h4 : ((max |(x)| |(y)|) > 0) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((Real.rpow (((|(x)| /. (max |(x)| |(y)|)) ^ (n ^ (2 : ℕ))) + ((|(y)| /. (max |(x)| |(y)|)) ^ (n ^ (2 : ℕ)))) (((n : ℝ))⁻¹)) * ((max |(x)| |(y)|) ^ n))))))
  (h5 : ((max |(x)| |(y)|) > 0) → (Tendsto (fun n : ℕ => (Real.rpow (a n) ((n)⁻¹))) atTop (𝓝 (max |(x)| |(y)|))))
  (h6 : ((max |(x)| |(y)|) < 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0)))
  (h7 : ((max |(x)| |(y)|) > 1) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)))
  : ((max |(x)| |(y)|) = 1) → (Tendsto (fun n : ℕ => (a n)) atTop (𝓝 1)) := by
  sorry

theorem proof_gap_exercise_2734_6
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (y : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : y ∈ (Set.univ : Set ℝ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (Real.rpow ((|(x)| ^ (n ^ (2 : ℕ))) + (|(y)| ^ (n ^ (2 : ℕ)))) (((n : ℝ))⁻¹))))))
  (h4 : ((max |(x)| |(y)|) > 0) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((Real.rpow (((|(x)| /. (max |(x)| |(y)|)) ^ (n ^ (2 : ℕ))) + ((|(y)| /. (max |(x)| |(y)|)) ^ (n ^ (2 : ℕ)))) (((n : ℝ))⁻¹)) * ((max |(x)| |(y)|) ^ n))))))
  (h5 : ((max |(x)| |(y)|) > 0) → (Tendsto (fun n : ℕ => (Real.rpow (a n) ((n)⁻¹))) atTop (𝓝 (max |(x)| |(y)|))))
  (h6 : ((max |(x)| |(y)|) < 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0)))
  (h7 : ((max |(x)| |(y)|) > 1) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)))
  (h8 : ((max |(x)| |(y)|) = 1) → (Tendsto (fun n : ℕ => (a n)) atTop (𝓝 1)))
  : ((max |(x)| |(y)|) = 1) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)) := by
  sorry

theorem proof_gap_exercise_2734_7
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (y : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : y ∈ (Set.univ : Set ℝ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (Real.rpow ((|(x)| ^ (n ^ (2 : ℕ))) + (|(y)| ^ (n ^ (2 : ℕ)))) (((n : ℝ))⁻¹))))))
  (h4 : ((max |(x)| |(y)|) > 0) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((Real.rpow (((|(x)| /. (max |(x)| |(y)|)) ^ (n ^ (2 : ℕ))) + ((|(y)| /. (max |(x)| |(y)|)) ^ (n ^ (2 : ℕ)))) (((n : ℝ))⁻¹)) * ((max |(x)| |(y)|) ^ n))))))
  (h5 : ((max |(x)| |(y)|) > 0) → (Tendsto (fun n : ℕ => (Real.rpow (a n) ((n)⁻¹))) atTop (𝓝 (max |(x)| |(y)|))))
  (h6 : ((max |(x)| |(y)|) < 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0)))
  (h7 : ((max |(x)| |(y)|) > 1) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)))
  (h8 : ((max |(x)| |(y)|) = 1) → (Tendsto (fun n : ℕ => (a n)) atTop (𝓝 1)))
  (h9 : ((max |(x)| |(y)|) = 1) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)))
  : ((x, y) ∈ ({p | p = (x, y) ∧ ((((max |(x)| |(y)|) < 1) ∧ (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0))) ∨ (((max |(x)| |(y)|) ≥ 1) ∧ (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0))))})) ↔ ((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) := by
  sorry

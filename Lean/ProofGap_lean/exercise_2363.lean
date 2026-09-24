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

-- exercise: exercise_2363

theorem proof_gap_exercise_2363_1
  (m : ℝ)
  (n : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : n > 0)
  (h4 : (m > (-(1 : ℝ))) ∧ ((n - m) > 1))
  : (∫ x in Set.Ioi (0 : ℝ), (((Real.rpow x m) /. ((1 : ℝ) + (Real.rpow x n))) * (1 : ℝ))) = ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.rpow x m) /. ((1 : ℝ) + (Real.rpow x n))) * (1 : ℝ))) + (∫ x in Set.Ioi (1 : ℝ), (((Real.rpow x m) /. ((1 : ℝ) + (Real.rpow x n))) * (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_2363_2
  (m : ℝ)
  (n : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : n > 0)
  (h4 : (∫ x in Set.Ioi (0 : ℝ), (((Real.rpow x m) /. ((1 : ℝ) + (Real.rpow x n))) * (1 : ℝ))) = ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.rpow x m) /. ((1 : ℝ) + (Real.rpow x n))) * (1 : ℝ))) + (∫ x in Set.Ioi (1 : ℝ), (((Real.rpow x m) /. ((1 : ℝ) + (Real.rpow x n))) * (1 : ℝ)))))
  : Tendsto (fun x : ℝ => ((Real.rpow x (-m)) * ((Real.rpow x m) /. (1 + (Real.rpow x n))))) (𝓝[>] 0) (𝓝 1) := by
  sorry

theorem proof_gap_exercise_2363_3
  (m : ℝ)
  (n : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : n > 0)
  (h4 : (∫ x in Set.Ioi (0 : ℝ), (((Real.rpow x m) /. ((1 : ℝ) + (Real.rpow x n))) * (1 : ℝ))) = ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.rpow x m) /. ((1 : ℝ) + (Real.rpow x n))) * (1 : ℝ))) + (∫ x in Set.Ioi (1 : ℝ), (((Real.rpow x m) /. ((1 : ℝ) + (Real.rpow x n))) * (1 : ℝ)))))
  (h5 : Tendsto (fun x : ℝ => ((Real.rpow x (-m)) * ((Real.rpow x m) /. (1 + (Real.rpow x n))))) (𝓝[>] 0) (𝓝 1))
  : ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.rpow x m) /. ((1 : ℝ) + (Real.rpow x n))) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)) ↔ ((-m) < 1) := by
  sorry

theorem proof_gap_exercise_2363_4
  (m : ℝ)
  (n : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : n > 0)
  (h4 : (∫ x in Set.Ioi (0 : ℝ), (((Real.rpow x m) /. ((1 : ℝ) + (Real.rpow x n))) * (1 : ℝ))) = ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.rpow x m) /. ((1 : ℝ) + (Real.rpow x n))) * (1 : ℝ))) + (∫ x in Set.Ioi (1 : ℝ), (((Real.rpow x m) /. ((1 : ℝ) + (Real.rpow x n))) * (1 : ℝ)))))
  (h5 : Tendsto (fun x : ℝ => ((Real.rpow x (-m)) * ((Real.rpow x m) /. (1 + (Real.rpow x n))))) (𝓝[>] 0) (𝓝 1))
  (h6 : ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.rpow x m) /. ((1 : ℝ) + (Real.rpow x n))) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)) ↔ ((-m) < 1))
  : ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.rpow x m) /. ((1 : ℝ) + (Real.rpow x n))) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)) ↔ (m > (-(1 : ℝ))) := by
  sorry

theorem proof_gap_exercise_2363_5
  (m : ℝ)
  (n : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : n > 0)
  (h4 : (∫ x in Set.Ioi (0 : ℝ), (((Real.rpow x m) /. ((1 : ℝ) + (Real.rpow x n))) * (1 : ℝ))) = ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.rpow x m) /. ((1 : ℝ) + (Real.rpow x n))) * (1 : ℝ))) + (∫ x in Set.Ioi (1 : ℝ), (((Real.rpow x m) /. ((1 : ℝ) + (Real.rpow x n))) * (1 : ℝ)))))
  (h5 : Tendsto (fun x : ℝ => ((Real.rpow x (-m)) * ((Real.rpow x m) /. (1 + (Real.rpow x n))))) (𝓝[>] 0) (𝓝 1))
  (h6 : ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.rpow x m) /. ((1 : ℝ) + (Real.rpow x n))) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)) ↔ ((-m) < 1))
  (h7 : ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.rpow x m) /. ((1 : ℝ) + (Real.rpow x n))) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)) ↔ (m > (-(1 : ℝ))))
  : Tendsto (fun x : ℝ => ((Real.rpow x (n - m)) * ((Real.rpow x m) /. (1 + (Real.rpow x n))))) atTop (𝓝 1) := by
  sorry

theorem proof_gap_exercise_2363_6
  (m : ℝ)
  (n : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : n > 0)
  (h4 : (∫ x in Set.Ioi (0 : ℝ), (((Real.rpow x m) /. ((1 : ℝ) + (Real.rpow x n))) * (1 : ℝ))) = ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.rpow x m) /. ((1 : ℝ) + (Real.rpow x n))) * (1 : ℝ))) + (∫ x in Set.Ioi (1 : ℝ), (((Real.rpow x m) /. ((1 : ℝ) + (Real.rpow x n))) * (1 : ℝ)))))
  (h5 : Tendsto (fun x : ℝ => ((Real.rpow x (-m)) * ((Real.rpow x m) /. (1 + (Real.rpow x n))))) (𝓝[>] 0) (𝓝 1))
  (h6 : ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.rpow x m) /. ((1 : ℝ) + (Real.rpow x n))) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)) ↔ ((-m) < 1))
  (h7 : ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.rpow x m) /. ((1 : ℝ) + (Real.rpow x n))) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)) ↔ (m > (-(1 : ℝ))))
  (h8 : Tendsto (fun x : ℝ => ((Real.rpow x (n - m)) * ((Real.rpow x m) /. (1 + (Real.rpow x n))))) atTop (𝓝 1))
  : ((∫ x in Set.Ioi (1 : ℝ), (((Real.rpow x m) /. ((1 : ℝ) + (Real.rpow x n))) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)) ↔ ((n - m) > 1) := by
  sorry

theorem proof_gap_exercise_2363_7
  (m : ℝ)
  (n : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : n > 0)
  (h4 : (∫ x in Set.Ioi (0 : ℝ), (((Real.rpow x m) /. ((1 : ℝ) + (Real.rpow x n))) * (1 : ℝ))) = ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.rpow x m) /. ((1 : ℝ) + (Real.rpow x n))) * (1 : ℝ))) + (∫ x in Set.Ioi (1 : ℝ), (((Real.rpow x m) /. ((1 : ℝ) + (Real.rpow x n))) * (1 : ℝ)))))
  (h5 : Tendsto (fun x : ℝ => ((Real.rpow x (-m)) * ((Real.rpow x m) /. (1 + (Real.rpow x n))))) (𝓝[>] 0) (𝓝 1))
  (h6 : ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.rpow x m) /. ((1 : ℝ) + (Real.rpow x n))) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)) ↔ ((-m) < 1))
  (h7 : ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.rpow x m) /. ((1 : ℝ) + (Real.rpow x n))) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)) ↔ (m > (-(1 : ℝ))))
  (h8 : Tendsto (fun x : ℝ => ((Real.rpow x (n - m)) * ((Real.rpow x m) /. (1 + (Real.rpow x n))))) atTop (𝓝 1))
  (h9 : ((∫ x in Set.Ioi (1 : ℝ), (((Real.rpow x m) /. ((1 : ℝ) + (Real.rpow x n))) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)) ↔ ((n - m) > 1))
  : ((m, n) ∈ ({p : ℝ × ℝ | (((((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2 ∈ (Set.univ : Set ℝ))) ∧ (p.2 > 0)) ∧ (p.1 > (-(1 : ℝ)))) ∧ ((p.2 - p.1) > 1))})) ↔ ((∫ x in Set.Ioi (0 : ℝ), (((Real.rpow x m) /. ((1 : ℝ) + (Real.rpow x n))) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)) := by
  sorry

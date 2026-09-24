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

-- exercise: exercise_2364

theorem proof_gap_exercise_2364_1
  (a : ℝ)
  (n : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : a ≠ 0)
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((Real.arctan (a * x)) = (-(Real.arctan ((-a) * x)))))) := by
  sorry

theorem proof_gap_exercise_2364_2
  (a : ℝ)
  (n : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : a ≠ 0)
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((Real.arctan (a * x)) = (-(Real.arctan ((-a) * x)))))))
  (h5 : (1 < n) ∧ (n < 2))
  : (a > 0) → ((∫ x in Set.Ioi (0 : ℝ), (((Real.arctan (a * x)) /. (Real.rpow x n)) * (1 : ℝ))) = ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.arctan (a * x)) /. (Real.rpow x n)) * (1 : ℝ))) + (∫ x in Set.Ioi (1 : ℝ), (((Real.arctan (a * x)) /. (Real.rpow x n)) * (1 : ℝ))))) := by
  sorry

theorem proof_gap_exercise_2364_3
  (a : ℝ)
  (n : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : a ≠ 0)
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((Real.arctan (a * x)) = (-(Real.arctan ((-a) * x)))))))
  (h5 : (a > 0) → ((∫ x in Set.Ioi (0 : ℝ), (((Real.arctan (a * x)) /. (Real.rpow x n)) * (1 : ℝ))) = ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.arctan (a * x)) /. (Real.rpow x n)) * (1 : ℝ))) + (∫ x in Set.Ioi (1 : ℝ), (((Real.arctan (a * x)) /. (Real.rpow x n)) * (1 : ℝ))))))
  (h6 : (1 < n) ∧ (n < 2))
  : (a > 0) → (Tendsto (fun x : ℝ => ((Real.rpow x (n - 1)) * ((Real.arctan (a * x)) /. (Real.rpow x n)))) (𝓝[>] 0) (𝓝 a)) := by
  sorry

theorem proof_gap_exercise_2364_4
  (a : ℝ)
  (n : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : a ≠ 0)
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((Real.arctan (a * x)) = (-(Real.arctan ((-a) * x)))))))
  (h5 : (a > 0) → ((∫ x in Set.Ioi (0 : ℝ), (((Real.arctan (a * x)) /. (Real.rpow x n)) * (1 : ℝ))) = ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.arctan (a * x)) /. (Real.rpow x n)) * (1 : ℝ))) + (∫ x in Set.Ioi (1 : ℝ), (((Real.arctan (a * x)) /. (Real.rpow x n)) * (1 : ℝ))))))
  (h6 : (a > 0) → (Tendsto (fun x : ℝ => ((Real.rpow x (n - 1)) * ((Real.arctan (a * x)) /. (Real.rpow x n)))) (𝓝[>] 0) (𝓝 a)))
  : (a > 0) → (((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.arctan (a * x)) /. (Real.rpow x n)) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)) ↔ ((n - 1) < 1)) := by
  sorry

theorem proof_gap_exercise_2364_5
  (a : ℝ)
  (n : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : a ≠ 0)
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((Real.arctan (a * x)) = (-(Real.arctan ((-a) * x)))))))
  (h5 : (a > 0) → ((∫ x in Set.Ioi (0 : ℝ), (((Real.arctan (a * x)) /. (Real.rpow x n)) * (1 : ℝ))) = ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.arctan (a * x)) /. (Real.rpow x n)) * (1 : ℝ))) + (∫ x in Set.Ioi (1 : ℝ), (((Real.arctan (a * x)) /. (Real.rpow x n)) * (1 : ℝ))))))
  (h6 : (a > 0) → (Tendsto (fun x : ℝ => ((Real.rpow x (n - 1)) * ((Real.arctan (a * x)) /. (Real.rpow x n)))) (𝓝[>] 0) (𝓝 a)))
  (h7 : (a > 0) → (((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.arctan (a * x)) /. (Real.rpow x n)) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)) ↔ ((n - 1) < 1)))
  : (a > 0) → (((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.arctan (a * x)) /. (Real.rpow x n)) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)) ↔ (n < 2)) := by
  sorry

theorem proof_gap_exercise_2364_6
  (a : ℝ)
  (n : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : a ≠ 0)
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((Real.arctan (a * x)) = (-(Real.arctan ((-a) * x)))))))
  (h5 : (a > 0) → ((∫ x in Set.Ioi (0 : ℝ), (((Real.arctan (a * x)) /. (Real.rpow x n)) * (1 : ℝ))) = ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.arctan (a * x)) /. (Real.rpow x n)) * (1 : ℝ))) + (∫ x in Set.Ioi (1 : ℝ), (((Real.arctan (a * x)) /. (Real.rpow x n)) * (1 : ℝ))))))
  (h6 : (a > 0) → (Tendsto (fun x : ℝ => ((Real.rpow x (n - 1)) * ((Real.arctan (a * x)) /. (Real.rpow x n)))) (𝓝[>] 0) (𝓝 a)))
  (h7 : (a > 0) → (((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.arctan (a * x)) /. (Real.rpow x n)) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)) ↔ ((n - 1) < 1)))
  (h8 : (a > 0) → (((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.arctan (a * x)) /. (Real.rpow x n)) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)) ↔ (n < 2)))
  : (a > 0) → (Tendsto (fun x : ℝ => ((Real.rpow x n) * ((Real.arctan (a * x)) /. (Real.rpow x n)))) atTop (𝓝 (Real.pi /. 2))) := by
  sorry

theorem proof_gap_exercise_2364_7
  (a : ℝ)
  (n : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : a ≠ 0)
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((Real.arctan (a * x)) = (-(Real.arctan ((-a) * x)))))))
  (h5 : (a > 0) → ((∫ x in Set.Ioi (0 : ℝ), (((Real.arctan (a * x)) /. (Real.rpow x n)) * (1 : ℝ))) = ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.arctan (a * x)) /. (Real.rpow x n)) * (1 : ℝ))) + (∫ x in Set.Ioi (1 : ℝ), (((Real.arctan (a * x)) /. (Real.rpow x n)) * (1 : ℝ))))))
  (h6 : (a > 0) → (Tendsto (fun x : ℝ => ((Real.rpow x (n - 1)) * ((Real.arctan (a * x)) /. (Real.rpow x n)))) (𝓝[>] 0) (𝓝 a)))
  (h7 : (a > 0) → (((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.arctan (a * x)) /. (Real.rpow x n)) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)) ↔ ((n - 1) < 1)))
  (h8 : (a > 0) → (((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.arctan (a * x)) /. (Real.rpow x n)) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)) ↔ (n < 2)))
  (h9 : (a > 0) → (Tendsto (fun x : ℝ => ((Real.rpow x n) * ((Real.arctan (a * x)) /. (Real.rpow x n)))) atTop (𝓝 (Real.pi /. 2))))
  : (a > 0) → (((∫ x in Set.Ioi (1 : ℝ), (((Real.arctan (a * x)) /. (Real.rpow x n)) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)) ↔ (n > 1)) := by
  sorry

theorem proof_gap_exercise_2364_8
  (a : ℝ)
  (n : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : a ≠ 0)
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((Real.arctan (a * x)) = (-(Real.arctan ((-a) * x)))))))
  (h5 : (a > 0) → ((∫ x in Set.Ioi (0 : ℝ), (((Real.arctan (a * x)) /. (Real.rpow x n)) * (1 : ℝ))) = ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.arctan (a * x)) /. (Real.rpow x n)) * (1 : ℝ))) + (∫ x in Set.Ioi (1 : ℝ), (((Real.arctan (a * x)) /. (Real.rpow x n)) * (1 : ℝ))))))
  (h6 : (a > 0) → (Tendsto (fun x : ℝ => ((Real.rpow x (n - 1)) * ((Real.arctan (a * x)) /. (Real.rpow x n)))) (𝓝[>] 0) (𝓝 a)))
  (h7 : (a > 0) → (((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.arctan (a * x)) /. (Real.rpow x n)) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)) ↔ ((n - 1) < 1)))
  (h8 : (a > 0) → (((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.arctan (a * x)) /. (Real.rpow x n)) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)) ↔ (n < 2)))
  (h9 : (a > 0) → (Tendsto (fun x : ℝ => ((Real.rpow x n) * ((Real.arctan (a * x)) /. (Real.rpow x n)))) atTop (𝓝 (Real.pi /. 2))))
  (h10 : (a > 0) → (((∫ x in Set.Ioi (1 : ℝ), (((Real.arctan (a * x)) /. (Real.rpow x n)) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)) ↔ (n > 1)))
  : ((a, n) ∈ ({p | p = (a, n) ∧ (a ≠ 0) ∧ (1 < n) ∧ (n < 2)})) ↔ ((∫ x in Set.Ioi (0 : ℝ), (((Real.arctan (a * x)) /. (Real.rpow x n)) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)) := by
  sorry

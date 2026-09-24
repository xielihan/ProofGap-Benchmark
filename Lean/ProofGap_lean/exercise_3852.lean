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

-- exercise: exercise_3852

theorem proof_gap_exercise_3852_1
  (B : (ℝ × ℝ -> ℝ))
  (m : ℝ)
  (n : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : t = (x /. (1 + x)))
  : 0 < t := by
  sorry

theorem proof_gap_exercise_3852_2
  (B : (ℝ × ℝ -> ℝ))
  (m : ℝ)
  (n : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : t = (x /. (1 + x)))
  (h4 : 0 < t)
  : t < 1 := by
  sorry

theorem proof_gap_exercise_3852_3
  (B : (ℝ × ℝ -> ℝ))
  (m : ℝ)
  (n : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : t = (x /. (1 + x)))
  (h4 : 0 < t)
  (h5 : t < 1)
  : (∫ x in Set.Ioi (0 : ℝ), (((Real.rpow x (m - 1)) /. (Real.rpow (1 + x) n)) * (1 : ℝ))) = (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t (m - 1)) * (Real.rpow (1 - t) ((n - m) - 1))) * (1 : ℝ))) := by
  sorry

theorem proof_gap_exercise_3852_4
  (B : (ℝ × ℝ -> ℝ))
  (m : ℝ)
  (n : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : t = (x /. (1 + x)))
  (h4 : 0 < t)
  (h5 : t < 1)
  (h6 : (∫ x in Set.Ioi (0 : ℝ), (((Real.rpow x (m - 1)) /. (Real.rpow (1 + x) n)) * (1 : ℝ))) = (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t (m - 1)) * (Real.rpow (1 - t) ((n - m) - 1))) * (1 : ℝ))))
  : (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t (m - 1)) * (Real.rpow (1 - t) ((n - m) - 1))) * (1 : ℝ))) = (B (m, (n - m))) := by
  sorry

theorem proof_gap_exercise_3852_5
  (B : (ℝ × ℝ -> ℝ))
  (m : ℝ)
  (n : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : t = (x /. (1 + x)))
  (h4 : 0 < t)
  (h5 : t < 1)
  (h6 : (∫ x in Set.Ioi (0 : ℝ), (((Real.rpow x (m - 1)) /. (Real.rpow (1 + x) n)) * (1 : ℝ))) = (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t (m - 1)) * (Real.rpow (1 - t) ((n - m) - 1))) * (1 : ℝ))))
  (h7 : (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t (m - 1)) * (Real.rpow (1 - t) ((n - m) - 1))) * (1 : ℝ))) = (B (m, (n - m))))
  : m > 0 := by
  sorry

theorem proof_gap_exercise_3852_6
  (B : (ℝ × ℝ -> ℝ))
  (m : ℝ)
  (n : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : t = (x /. (1 + x)))
  (h4 : 0 < t)
  (h5 : t < 1)
  (h6 : (∫ x in Set.Ioi (0 : ℝ), (((Real.rpow x (m - 1)) /. (Real.rpow (1 + x) n)) * (1 : ℝ))) = (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t (m - 1)) * (Real.rpow (1 - t) ((n - m) - 1))) * (1 : ℝ))))
  (h7 : (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t (m - 1)) * (Real.rpow (1 - t) ((n - m) - 1))) * (1 : ℝ))) = (B (m, (n - m))))
  (h8 : m > 0)
  : (n - m) > 0 := by
  sorry

theorem proof_gap_exercise_3852_7
  (B : (ℝ × ℝ -> ℝ))
  (m : ℝ)
  (n : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : t = (x /. (1 + x)))
  (h4 : 0 < t)
  (h5 : t < 1)
  (h6 : (∫ x in Set.Ioi (0 : ℝ), (((Real.rpow x (m - 1)) /. (Real.rpow (1 + x) n)) * (1 : ℝ))) = (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t (m - 1)) * (Real.rpow (1 - t) ((n - m) - 1))) * (1 : ℝ))))
  (h7 : (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t (m - 1)) * (Real.rpow (1 - t) ((n - m) - 1))) * (1 : ℝ))) = (B (m, (n - m))))
  (h8 : m > 0)
  (h9 : (n - m) > 0)
  : 0 < m := by
  sorry

theorem proof_gap_exercise_3852_8
  (B : (ℝ × ℝ -> ℝ))
  (m : ℝ)
  (n : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : t = (x /. (1 + x)))
  (h4 : 0 < t)
  (h5 : t < 1)
  (h6 : (∫ x in Set.Ioi (0 : ℝ), (((Real.rpow x (m - 1)) /. (Real.rpow (1 + x) n)) * (1 : ℝ))) = (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t (m - 1)) * (Real.rpow (1 - t) ((n - m) - 1))) * (1 : ℝ))))
  (h7 : (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t (m - 1)) * (Real.rpow (1 - t) ((n - m) - 1))) * (1 : ℝ))) = (B (m, (n - m))))
  (h8 : m > 0)
  (h9 : (n - m) > 0)
  (h10 : 0 < m)
  : m < n := by
  sorry

theorem proof_gap_exercise_3852_9
  (B : (ℝ × ℝ -> ℝ))
  (m : ℝ)
  (n : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : t = (x /. (1 + x)))
  (h4 : 0 < t)
  (h5 : t < 1)
  (h6 : (∫ x in Set.Ioi (0 : ℝ), (((Real.rpow x (m - 1)) /. (Real.rpow (1 + x) n)) * (1 : ℝ))) = (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t (m - 1)) * (Real.rpow (1 - t) ((n - m) - 1))) * (1 : ℝ))))
  (h7 : (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t (m - 1)) * (Real.rpow (1 - t) ((n - m) - 1))) * (1 : ℝ))) = (B (m, (n - m))))
  (h8 : m > 0)
  (h9 : (n - m) > 0)
  (h10 : 0 < m)
  (h11 : m < n)
  : (∫ x in Set.Ioi (0 : ℝ), (((Real.rpow x (m - 1)) /. (Real.rpow (1 + x) n)) * (1 : ℝ))) = (B (m, (n - m))) := by
  sorry

import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat

open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

open scoped RealInnerProductSpace

noncomputable def lpFunDeri (_f : ℝ × (ℝ × ℝ) -> ℝ) (_g : ℝ) : ℝ × (ℝ × ℝ) -> ℝ :=
  fun _ => 0

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

-- exercise: exercise_3509

theorem proof_gap_exercise_3509_1
  (z : (ℝ × (ℝ × ℝ) -> ℝ))
  (x_1 : ℝ)
  (x_2 : ℝ)
  (x_3 : ℝ)
  (y_1 : ℝ)
  (y_2 : ℝ)
  (y_3 : ℝ)
  (h1 : x_1 ∈ (Set.univ : Set ℝ))
  (h2 : x_2 ∈ (Set.univ : Set ℝ))
  (h3 : x_3 ∈ (Set.univ : Set ℝ))
  (h4 : y_1 ∈ (Set.univ : Set ℝ))
  (h5 : y_2 ∈ (Set.univ : Set ℝ))
  (h6 : y_3 ∈ (Set.univ : Set ℝ))
  (h7 : ContDiff ℝ (2 : ℕ∞) z)
  (h8 : y_1 = ((x_2 + x_3) - x_1))
  (h9 : y_2 = ((x_1 + x_3) - x_2))
  (h10 : y_3 = ((x_1 + x_2) - x_3))
  (h11 : (((((((lpFunDeri (lpFunDeri z x_1) x_1) (x_1, (x_2, x_3))) + ((lpFunDeri (lpFunDeri z x_2) x_2) (x_1, (x_2, x_3)))) + ((lpFunDeri (lpFunDeri z x_3) x_3) (x_1, (x_2, x_3)))) + ((lpFunDeri (lpFunDeri z x_1) x_2) (x_1, (x_2, x_3)))) + ((lpFunDeri (lpFunDeri z x_1) x_3) (x_1, (x_2, x_3)))) + ((lpFunDeri (lpFunDeri z x_2) x_3) (x_1, (x_2, x_3)))) = 0)
  : ((lpFunDeri z x_1) (x_1, (x_2, x_3))) = (((-((lpFunDeri z y_1) (y_1, (y_2, y_3)))) + ((lpFunDeri z y_2) (y_1, (y_2, y_3)))) + ((lpFunDeri z y_3) (y_1, (y_2, y_3)))) := by
  sorry

theorem proof_gap_exercise_3509_2
  (z : (ℝ × (ℝ × ℝ) -> ℝ))
  (x_1 : ℝ)
  (x_2 : ℝ)
  (x_3 : ℝ)
  (y_1 : ℝ)
  (y_2 : ℝ)
  (y_3 : ℝ)
  (h1 : x_1 ∈ (Set.univ : Set ℝ))
  (h2 : x_2 ∈ (Set.univ : Set ℝ))
  (h3 : x_3 ∈ (Set.univ : Set ℝ))
  (h4 : y_1 ∈ (Set.univ : Set ℝ))
  (h5 : y_2 ∈ (Set.univ : Set ℝ))
  (h6 : y_3 ∈ (Set.univ : Set ℝ))
  (h7 : ContDiff ℝ (2 : ℕ∞) z)
  (h8 : y_1 = ((x_2 + x_3) - x_1))
  (h9 : y_2 = ((x_1 + x_3) - x_2))
  (h10 : y_3 = ((x_1 + x_2) - x_3))
  (h11 : (((((((lpFunDeri (lpFunDeri z x_1) x_1) (x_1, (x_2, x_3))) + ((lpFunDeri (lpFunDeri z x_2) x_2) (x_1, (x_2, x_3)))) + ((lpFunDeri (lpFunDeri z x_3) x_3) (x_1, (x_2, x_3)))) + ((lpFunDeri (lpFunDeri z x_1) x_2) (x_1, (x_2, x_3)))) + ((lpFunDeri (lpFunDeri z x_1) x_3) (x_1, (x_2, x_3)))) + ((lpFunDeri (lpFunDeri z x_2) x_3) (x_1, (x_2, x_3)))) = 0)
  (h12 : ((lpFunDeri z x_1) (x_1, (x_2, x_3))) = (((-((lpFunDeri z y_1) (y_1, (y_2, y_3)))) + ((lpFunDeri z y_2) (y_1, (y_2, y_3)))) + ((lpFunDeri z y_3) (y_1, (y_2, y_3)))))
  : ((lpFunDeri z x_2) (x_1, (x_2, x_3))) = ((((lpFunDeri z y_1) (y_1, (y_2, y_3))) - ((lpFunDeri z y_2) (y_1, (y_2, y_3)))) + ((lpFunDeri z y_3) (y_1, (y_2, y_3)))) := by
  sorry

theorem proof_gap_exercise_3509_3
  (z : (ℝ × (ℝ × ℝ) -> ℝ))
  (x_1 : ℝ)
  (x_2 : ℝ)
  (x_3 : ℝ)
  (y_1 : ℝ)
  (y_2 : ℝ)
  (y_3 : ℝ)
  (h1 : x_1 ∈ (Set.univ : Set ℝ))
  (h2 : x_2 ∈ (Set.univ : Set ℝ))
  (h3 : x_3 ∈ (Set.univ : Set ℝ))
  (h4 : y_1 ∈ (Set.univ : Set ℝ))
  (h5 : y_2 ∈ (Set.univ : Set ℝ))
  (h6 : y_3 ∈ (Set.univ : Set ℝ))
  (h7 : ContDiff ℝ (2 : ℕ∞) z)
  (h8 : y_1 = ((x_2 + x_3) - x_1))
  (h9 : y_2 = ((x_1 + x_3) - x_2))
  (h10 : y_3 = ((x_1 + x_2) - x_3))
  (h11 : (((((((lpFunDeri (lpFunDeri z x_1) x_1) (x_1, (x_2, x_3))) + ((lpFunDeri (lpFunDeri z x_2) x_2) (x_1, (x_2, x_3)))) + ((lpFunDeri (lpFunDeri z x_3) x_3) (x_1, (x_2, x_3)))) + ((lpFunDeri (lpFunDeri z x_1) x_2) (x_1, (x_2, x_3)))) + ((lpFunDeri (lpFunDeri z x_1) x_3) (x_1, (x_2, x_3)))) + ((lpFunDeri (lpFunDeri z x_2) x_3) (x_1, (x_2, x_3)))) = 0)
  (h12 : ((lpFunDeri z x_1) (x_1, (x_2, x_3))) = (((-((lpFunDeri z y_1) (y_1, (y_2, y_3)))) + ((lpFunDeri z y_2) (y_1, (y_2, y_3)))) + ((lpFunDeri z y_3) (y_1, (y_2, y_3)))))
  (h13 : ((lpFunDeri z x_2) (x_1, (x_2, x_3))) = ((((lpFunDeri z y_1) (y_1, (y_2, y_3))) - ((lpFunDeri z y_2) (y_1, (y_2, y_3)))) + ((lpFunDeri z y_3) (y_1, (y_2, y_3)))))
  : ((lpFunDeri z x_3) (x_1, (x_2, x_3))) = ((((lpFunDeri z y_1) (y_1, (y_2, y_3))) + ((lpFunDeri z y_2) (y_1, (y_2, y_3)))) - ((lpFunDeri z y_3) (y_1, (y_2, y_3)))) := by
  sorry

theorem proof_gap_exercise_3509_4
  (z : (ℝ × (ℝ × ℝ) -> ℝ))
  (x_1 : ℝ)
  (x_2 : ℝ)
  (x_3 : ℝ)
  (y_1 : ℝ)
  (y_2 : ℝ)
  (y_3 : ℝ)
  (h1 : x_1 ∈ (Set.univ : Set ℝ))
  (h2 : x_2 ∈ (Set.univ : Set ℝ))
  (h3 : x_3 ∈ (Set.univ : Set ℝ))
  (h4 : y_1 ∈ (Set.univ : Set ℝ))
  (h5 : y_2 ∈ (Set.univ : Set ℝ))
  (h6 : y_3 ∈ (Set.univ : Set ℝ))
  (h7 : ContDiff ℝ (2 : ℕ∞) z)
  (h8 : y_1 = ((x_2 + x_3) - x_1))
  (h9 : y_2 = ((x_1 + x_3) - x_2))
  (h10 : y_3 = ((x_1 + x_2) - x_3))
  (h11 : (((((((lpFunDeri (lpFunDeri z x_1) x_1) (x_1, (x_2, x_3))) + ((lpFunDeri (lpFunDeri z x_2) x_2) (x_1, (x_2, x_3)))) + ((lpFunDeri (lpFunDeri z x_3) x_3) (x_1, (x_2, x_3)))) + ((lpFunDeri (lpFunDeri z x_1) x_2) (x_1, (x_2, x_3)))) + ((lpFunDeri (lpFunDeri z x_1) x_3) (x_1, (x_2, x_3)))) + ((lpFunDeri (lpFunDeri z x_2) x_3) (x_1, (x_2, x_3)))) = 0)
  (h12 : ((lpFunDeri z x_1) (x_1, (x_2, x_3))) = (((-((lpFunDeri z y_1) (y_1, (y_2, y_3)))) + ((lpFunDeri z y_2) (y_1, (y_2, y_3)))) + ((lpFunDeri z y_3) (y_1, (y_2, y_3)))))
  (h13 : ((lpFunDeri z x_2) (x_1, (x_2, x_3))) = ((((lpFunDeri z y_1) (y_1, (y_2, y_3))) - ((lpFunDeri z y_2) (y_1, (y_2, y_3)))) + ((lpFunDeri z y_3) (y_1, (y_2, y_3)))))
  (h14 : ((lpFunDeri z x_3) (x_1, (x_2, x_3))) = ((((lpFunDeri z y_1) (y_1, (y_2, y_3))) + ((lpFunDeri z y_2) (y_1, (y_2, y_3)))) - ((lpFunDeri z y_3) (y_1, (y_2, y_3)))))
  : (((((((lpFunDeri (lpFunDeri z x_1) x_1) (x_1, (x_2, x_3))) + ((lpFunDeri (lpFunDeri z x_2) x_2) (x_1, (x_2, x_3)))) + ((lpFunDeri (lpFunDeri z x_3) x_3) (x_1, (x_2, x_3)))) + ((lpFunDeri (lpFunDeri z x_1) x_2) (x_1, (x_2, x_3)))) + ((lpFunDeri (lpFunDeri z x_1) x_3) (x_1, (x_2, x_3)))) + ((lpFunDeri (lpFunDeri z x_2) x_3) (x_1, (x_2, x_3)))) = (2 * ((((lpFunDeri (lpFunDeri z y_1) y_1) (y_1, (y_2, y_3))) + ((lpFunDeri (lpFunDeri z y_2) y_2) (y_1, (y_2, y_3)))) + ((lpFunDeri (lpFunDeri z y_3) y_3) (y_1, (y_2, y_3))))) := by
  sorry

theorem proof_gap_exercise_3509_5
  (z : (ℝ × (ℝ × ℝ) -> ℝ))
  (x_1 : ℝ)
  (x_2 : ℝ)
  (x_3 : ℝ)
  (y_1 : ℝ)
  (y_2 : ℝ)
  (y_3 : ℝ)
  (h1 : x_1 ∈ (Set.univ : Set ℝ))
  (h2 : x_2 ∈ (Set.univ : Set ℝ))
  (h3 : x_3 ∈ (Set.univ : Set ℝ))
  (h4 : y_1 ∈ (Set.univ : Set ℝ))
  (h5 : y_2 ∈ (Set.univ : Set ℝ))
  (h6 : y_3 ∈ (Set.univ : Set ℝ))
  (h7 : ContDiff ℝ (2 : ℕ∞) z)
  (h8 : y_1 = ((x_2 + x_3) - x_1))
  (h9 : y_2 = ((x_1 + x_3) - x_2))
  (h10 : y_3 = ((x_1 + x_2) - x_3))
  (h11 : (((((((lpFunDeri (lpFunDeri z x_1) x_1) (x_1, (x_2, x_3))) + ((lpFunDeri (lpFunDeri z x_2) x_2) (x_1, (x_2, x_3)))) + ((lpFunDeri (lpFunDeri z x_3) x_3) (x_1, (x_2, x_3)))) + ((lpFunDeri (lpFunDeri z x_1) x_2) (x_1, (x_2, x_3)))) + ((lpFunDeri (lpFunDeri z x_1) x_3) (x_1, (x_2, x_3)))) + ((lpFunDeri (lpFunDeri z x_2) x_3) (x_1, (x_2, x_3)))) = 0)
  (h12 : ((lpFunDeri z x_1) (x_1, (x_2, x_3))) = (((-((lpFunDeri z y_1) (y_1, (y_2, y_3)))) + ((lpFunDeri z y_2) (y_1, (y_2, y_3)))) + ((lpFunDeri z y_3) (y_1, (y_2, y_3)))))
  (h13 : ((lpFunDeri z x_2) (x_1, (x_2, x_3))) = ((((lpFunDeri z y_1) (y_1, (y_2, y_3))) - ((lpFunDeri z y_2) (y_1, (y_2, y_3)))) + ((lpFunDeri z y_3) (y_1, (y_2, y_3)))))
  (h14 : ((lpFunDeri z x_3) (x_1, (x_2, x_3))) = ((((lpFunDeri z y_1) (y_1, (y_2, y_3))) + ((lpFunDeri z y_2) (y_1, (y_2, y_3)))) - ((lpFunDeri z y_3) (y_1, (y_2, y_3)))))
  (h15 : (((((((lpFunDeri (lpFunDeri z x_1) x_1) (x_1, (x_2, x_3))) + ((lpFunDeri (lpFunDeri z x_2) x_2) (x_1, (x_2, x_3)))) + ((lpFunDeri (lpFunDeri z x_3) x_3) (x_1, (x_2, x_3)))) + ((lpFunDeri (lpFunDeri z x_1) x_2) (x_1, (x_2, x_3)))) + ((lpFunDeri (lpFunDeri z x_1) x_3) (x_1, (x_2, x_3)))) + ((lpFunDeri (lpFunDeri z x_2) x_3) (x_1, (x_2, x_3)))) = (2 * ((((lpFunDeri (lpFunDeri z y_1) y_1) (y_1, (y_2, y_3))) + ((lpFunDeri (lpFunDeri z y_2) y_2) (y_1, (y_2, y_3)))) + ((lpFunDeri (lpFunDeri z y_3) y_3) (y_1, (y_2, y_3))))))
  : ((((lpFunDeri (lpFunDeri z y_1) y_1) (y_1, (y_2, y_3))) + ((lpFunDeri (lpFunDeri z y_2) y_2) (y_1, (y_2, y_3)))) + ((lpFunDeri (lpFunDeri z y_3) y_3) (y_1, (y_2, y_3)))) = 0 := by
  sorry

theorem proof_gap_exercise_3509_6
  (z : (ℝ × (ℝ × ℝ) -> ℝ))
  (x_1 : ℝ)
  (x_2 : ℝ)
  (x_3 : ℝ)
  (y_1 : ℝ)
  (y_2 : ℝ)
  (y_3 : ℝ)
  (h1 : x_1 ∈ (Set.univ : Set ℝ))
  (h2 : x_2 ∈ (Set.univ : Set ℝ))
  (h3 : x_3 ∈ (Set.univ : Set ℝ))
  (h4 : y_1 ∈ (Set.univ : Set ℝ))
  (h5 : y_2 ∈ (Set.univ : Set ℝ))
  (h6 : y_3 ∈ (Set.univ : Set ℝ))
  (h7 : ContDiff ℝ (2 : ℕ∞) z)
  (h8 : y_1 = ((x_2 + x_3) - x_1))
  (h9 : y_2 = ((x_1 + x_3) - x_2))
  (h10 : y_3 = ((x_1 + x_2) - x_3))
  (h11 : (((((((lpFunDeri (lpFunDeri z x_1) x_1) (x_1, (x_2, x_3))) + ((lpFunDeri (lpFunDeri z x_2) x_2) (x_1, (x_2, x_3)))) + ((lpFunDeri (lpFunDeri z x_3) x_3) (x_1, (x_2, x_3)))) + ((lpFunDeri (lpFunDeri z x_1) x_2) (x_1, (x_2, x_3)))) + ((lpFunDeri (lpFunDeri z x_1) x_3) (x_1, (x_2, x_3)))) + ((lpFunDeri (lpFunDeri z x_2) x_3) (x_1, (x_2, x_3)))) = 0)
  (h12 : ((lpFunDeri z x_1) (x_1, (x_2, x_3))) = (((-((lpFunDeri z y_1) (y_1, (y_2, y_3)))) + ((lpFunDeri z y_2) (y_1, (y_2, y_3)))) + ((lpFunDeri z y_3) (y_1, (y_2, y_3)))))
  (h13 : ((lpFunDeri z x_2) (x_1, (x_2, x_3))) = ((((lpFunDeri z y_1) (y_1, (y_2, y_3))) - ((lpFunDeri z y_2) (y_1, (y_2, y_3)))) + ((lpFunDeri z y_3) (y_1, (y_2, y_3)))))
  (h14 : ((lpFunDeri z x_3) (x_1, (x_2, x_3))) = ((((lpFunDeri z y_1) (y_1, (y_2, y_3))) + ((lpFunDeri z y_2) (y_1, (y_2, y_3)))) - ((lpFunDeri z y_3) (y_1, (y_2, y_3)))))
  (h15 : (((((((lpFunDeri (lpFunDeri z x_1) x_1) (x_1, (x_2, x_3))) + ((lpFunDeri (lpFunDeri z x_2) x_2) (x_1, (x_2, x_3)))) + ((lpFunDeri (lpFunDeri z x_3) x_3) (x_1, (x_2, x_3)))) + ((lpFunDeri (lpFunDeri z x_1) x_2) (x_1, (x_2, x_3)))) + ((lpFunDeri (lpFunDeri z x_1) x_3) (x_1, (x_2, x_3)))) + ((lpFunDeri (lpFunDeri z x_2) x_3) (x_1, (x_2, x_3)))) = (2 * ((((lpFunDeri (lpFunDeri z y_1) y_1) (y_1, (y_2, y_3))) + ((lpFunDeri (lpFunDeri z y_2) y_2) (y_1, (y_2, y_3)))) + ((lpFunDeri (lpFunDeri z y_3) y_3) (y_1, (y_2, y_3))))))
  (h16 : ((((lpFunDeri (lpFunDeri z y_1) y_1) (y_1, (y_2, y_3))) + ((lpFunDeri (lpFunDeri z y_2) y_2) (y_1, (y_2, y_3)))) + ((lpFunDeri (lpFunDeri z y_3) y_3) (y_1, (y_2, y_3)))) = 0)
  : ((((lpFunDeri (lpFunDeri z y_1) y_1) (y_1, (y_2, y_3))) + ((lpFunDeri (lpFunDeri z y_2) y_2) (y_1, (y_2, y_3)))) + ((lpFunDeri (lpFunDeri z y_3) y_3) (y_1, (y_2, y_3)))) = 0 := by
  sorry

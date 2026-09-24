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

-- exercise: exercise_1105_1

theorem proof_gap_exercise_1105_1_1
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (n : ℕ)
  (x : ℝ)
  (v_uCE_uB5 : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h3 : (x ∈ (Set.univ : Set ℝ)) ∧ (((a ^ n) + x) > 0))
  (h4 : (v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0))
  (h5 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h6 : |(|(x)| - 0)| ≤ v_uCE_uB5)
  (h7 : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (y > 0))) → (((f : ℝ → _) y) = (Real.rpow y (((n : ℝ))⁻¹)))))
  (h8 : y_0 = (a ^ n))
  (h9 : v_uCE_u94_y = x)
  : DifferentiableOn ℝ f (Set.Ioi 0) := by
  sorry

theorem proof_gap_exercise_1105_1_2
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (n : ℕ)
  (x : ℝ)
  (v_uCE_uB5 : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h3 : (x ∈ (Set.univ : Set ℝ)) ∧ (((a ^ n) + x) > 0))
  (h4 : (v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0))
  (h5 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h6 : |(|(x)| - 0)| ≤ v_uCE_uB5)
  (h7 : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (y > 0))) → (((f : ℝ → _) y) = (Real.rpow y (((n : ℝ))⁻¹)))))
  (h8 : y_0 = (a ^ n))
  (h9 : v_uCE_u94_y = x)
  (h10 : DifferentiableOn ℝ f (Set.Ioi 0))
  : |((f (y_0 + v_uCE_u94_y)) - ((f y_0) + ((iteratedDeriv 1 (fun t => f t) y_0) * v_uCE_u94_y)))| ≤ v_uCE_uB5 := by
  sorry

theorem proof_gap_exercise_1105_1_3
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (n : ℕ)
  (x : ℝ)
  (v_uCE_uB5 : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h3 : (x ∈ (Set.univ : Set ℝ)) ∧ (((a ^ n) + x) > 0))
  (h4 : (v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0))
  (h5 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h6 : |(|(x)| - 0)| ≤ v_uCE_uB5)
  (h7 : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (y > 0))) → (((f : ℝ → _) y) = (Real.rpow y (((n : ℝ))⁻¹)))))
  (h8 : y_0 = (a ^ n))
  (h9 : v_uCE_u94_y = x)
  (h10 : DifferentiableOn ℝ f (Set.Ioi 0))
  (h11 : |((f (y_0 + v_uCE_u94_y)) - ((f y_0) + ((iteratedDeriv 1 (fun t => f t) y_0) * v_uCE_u94_y)))| ≤ v_uCE_uB5)
  : |((Real.rpow ((a ^ n) + x) (((n : ℝ))⁻¹)) - ((Real.rpow (a ^ n) (((n : ℝ))⁻¹)) + (x /. (n * (Real.rpow ((a ^ n) ^ (n - 1)) (((n : ℝ))⁻¹))))))| ≤ v_uCE_uB5 := by
  sorry

theorem proof_gap_exercise_1105_1_4
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (n : ℕ)
  (x : ℝ)
  (v_uCE_uB5 : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h3 : (x ∈ (Set.univ : Set ℝ)) ∧ (((a ^ n) + x) > 0))
  (h4 : (v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0))
  (h5 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h6 : |(|(x)| - 0)| ≤ v_uCE_uB5)
  (h7 : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (y > 0))) → (((f : ℝ → _) y) = (Real.rpow y (((n : ℝ))⁻¹)))))
  (h8 : y_0 = (a ^ n))
  (h9 : v_uCE_u94_y = x)
  (h10 : DifferentiableOn ℝ f (Set.Ioi 0))
  (h11 : |((f (y_0 + v_uCE_u94_y)) - ((f y_0) + ((iteratedDeriv 1 (fun t => f t) y_0) * v_uCE_u94_y)))| ≤ v_uCE_uB5)
  (h12 : |((Real.rpow ((a ^ n) + x) (((n : ℝ))⁻¹)) - ((Real.rpow (a ^ n) (((n : ℝ))⁻¹)) + (x /. (n * (Real.rpow ((a ^ n) ^ (n - 1)) (((n : ℝ))⁻¹))))))| ≤ v_uCE_uB5)
  : |((Real.rpow ((a ^ n) + x) (((n : ℝ))⁻¹)) - (a + (x /. (n * (a ^ (n - 1))))))| ≤ v_uCE_uB5 := by
  sorry

theorem proof_gap_exercise_1105_1_5
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (n : ℕ)
  (x : ℝ)
  (v_uCE_uB5 : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h3 : (x ∈ (Set.univ : Set ℝ)) ∧ (((a ^ n) + x) > 0))
  (h4 : (v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0))
  (h5 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h6 : |(|(x)| - 0)| ≤ v_uCE_uB5)
  (h7 : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (y > 0))) → (((f : ℝ → _) y) = (Real.rpow y (((n : ℝ))⁻¹)))))
  (h8 : y_0 = (a ^ n))
  (h9 : v_uCE_u94_y = x)
  (h10 : DifferentiableOn ℝ f (Set.Ioi 0))
  (h11 : |((f (y_0 + v_uCE_u94_y)) - ((f y_0) + ((iteratedDeriv 1 (fun t => f t) y_0) * v_uCE_u94_y)))| ≤ v_uCE_uB5)
  (h12 : |((Real.rpow ((a ^ n) + x) (((n : ℝ))⁻¹)) - ((Real.rpow (a ^ n) (((n : ℝ))⁻¹)) + (x /. (n * (Real.rpow ((a ^ n) ^ (n - 1)) (((n : ℝ))⁻¹))))))| ≤ v_uCE_uB5)
  (h13 : |((Real.rpow ((a ^ n) + x) (((n : ℝ))⁻¹)) - (a + (x /. (n * (a ^ (n - 1))))))| ≤ v_uCE_uB5)
  : (Real.rpow (9 : ℝ) (((3 : ℝ))⁻¹)) = (Real.rpow (((2 : ℕ) ^ (3 : ℕ)) + 1) (((3 : ℝ))⁻¹)) := by
  sorry

theorem proof_gap_exercise_1105_1_6
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (n : ℕ)
  (x : ℝ)
  (v_uCE_uB5 : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h3 : (x ∈ (Set.univ : Set ℝ)) ∧ (((a ^ n) + x) > 0))
  (h4 : (v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0))
  (h5 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h6 : |(|(x)| - 0)| ≤ v_uCE_uB5)
  (h7 : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (y > 0))) → (((f : ℝ → _) y) = (Real.rpow y (((n : ℝ))⁻¹)))))
  (h8 : y_0 = (a ^ n))
  (h9 : v_uCE_u94_y = x)
  (h10 : DifferentiableOn ℝ f (Set.Ioi 0))
  (h11 : |((f (y_0 + v_uCE_u94_y)) - ((f y_0) + ((iteratedDeriv 1 (fun t => f t) y_0) * v_uCE_u94_y)))| ≤ v_uCE_uB5)
  (h12 : |((Real.rpow ((a ^ n) + x) (((n : ℝ))⁻¹)) - ((Real.rpow (a ^ n) (((n : ℝ))⁻¹)) + (x /. (n * (Real.rpow ((a ^ n) ^ (n - 1)) (((n : ℝ))⁻¹))))))| ≤ v_uCE_uB5)
  (h13 : |((Real.rpow ((a ^ n) + x) (((n : ℝ))⁻¹)) - (a + (x /. (n * (a ^ (n - 1))))))| ≤ v_uCE_uB5)
  (h14 : (Real.rpow (9 : ℝ) (((3 : ℝ))⁻¹)) = (Real.rpow (((2 : ℕ) ^ (3 : ℕ)) + 1) (((3 : ℝ))⁻¹)))
  : |((Real.rpow (((2 : ℕ) ^ (3 : ℕ)) + 1) (((3 : ℝ))⁻¹)) - (2 + (1 /. (3 * ((2 : ℕ) ^ (2 : ℕ))))))| ≤ v_uCE_uB5 := by
  sorry

theorem proof_gap_exercise_1105_1_7
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (n : ℕ)
  (x : ℝ)
  (v_uCE_uB5 : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h3 : (x ∈ (Set.univ : Set ℝ)) ∧ (((a ^ n) + x) > 0))
  (h4 : (v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0))
  (h5 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h6 : |(|(x)| - 0)| ≤ v_uCE_uB5)
  (h7 : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (y > 0))) → (((f : ℝ → _) y) = (Real.rpow y (((n : ℝ))⁻¹)))))
  (h8 : y_0 = (a ^ n))
  (h9 : v_uCE_u94_y = x)
  (h10 : DifferentiableOn ℝ f (Set.Ioi 0))
  (h11 : |((f (y_0 + v_uCE_u94_y)) - ((f y_0) + ((iteratedDeriv 1 (fun t => f t) y_0) * v_uCE_u94_y)))| ≤ v_uCE_uB5)
  (h12 : |((Real.rpow ((a ^ n) + x) (((n : ℝ))⁻¹)) - ((Real.rpow (a ^ n) (((n : ℝ))⁻¹)) + (x /. (n * (Real.rpow ((a ^ n) ^ (n - 1)) (((n : ℝ))⁻¹))))))| ≤ v_uCE_uB5)
  (h13 : |((Real.rpow ((a ^ n) + x) (((n : ℝ))⁻¹)) - (a + (x /. (n * (a ^ (n - 1))))))| ≤ v_uCE_uB5)
  (h14 : (Real.rpow (9 : ℝ) (((3 : ℝ))⁻¹)) = (Real.rpow (((2 : ℕ) ^ (3 : ℕ)) + 1) (((3 : ℝ))⁻¹)))
  (h15 : |((Real.rpow (((2 : ℕ) ^ (3 : ℕ)) + 1) (((3 : ℝ))⁻¹)) - (2 + (1 /. (3 * ((2 : ℕ) ^ (2 : ℕ))))))| ≤ v_uCE_uB5)
  : (2 + (1 /. (3 * ((2 : ℕ) ^ (2 : ℕ))))) = (((2083 : ℝ) /. (1000 : ℝ))) := by
  sorry

theorem proof_gap_exercise_1105_1_8
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (n : ℕ)
  (x : ℝ)
  (v_uCE_uB5 : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h3 : (x ∈ (Set.univ : Set ℝ)) ∧ (((a ^ n) + x) > 0))
  (h4 : (v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0))
  (h5 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h6 : |(|(x)| - 0)| ≤ v_uCE_uB5)
  (h7 : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (y > 0))) → (((f : ℝ → _) y) = (Real.rpow y (((n : ℝ))⁻¹)))))
  (h8 : y_0 = (a ^ n))
  (h9 : v_uCE_u94_y = x)
  (h10 : DifferentiableOn ℝ f (Set.Ioi 0))
  (h11 : |((f (y_0 + v_uCE_u94_y)) - ((f y_0) + ((iteratedDeriv 1 (fun t => f t) y_0) * v_uCE_u94_y)))| ≤ v_uCE_uB5)
  (h12 : |((Real.rpow ((a ^ n) + x) (((n : ℝ))⁻¹)) - ((Real.rpow (a ^ n) (((n : ℝ))⁻¹)) + (x /. (n * (Real.rpow ((a ^ n) ^ (n - 1)) (((n : ℝ))⁻¹))))))| ≤ v_uCE_uB5)
  (h13 : |((Real.rpow ((a ^ n) + x) (((n : ℝ))⁻¹)) - (a + (x /. (n * (a ^ (n - 1))))))| ≤ v_uCE_uB5)
  (h14 : (Real.rpow (9 : ℝ) (((3 : ℝ))⁻¹)) = (Real.rpow (((2 : ℕ) ^ (3 : ℕ)) + 1) (((3 : ℝ))⁻¹)))
  (h15 : |((Real.rpow (((2 : ℕ) ^ (3 : ℕ)) + 1) (((3 : ℝ))⁻¹)) - (2 + (1 /. (3 * ((2 : ℕ) ^ (2 : ℕ))))))| ≤ v_uCE_uB5)
  (h16 : (2 + (1 /. (3 * ((2 : ℕ) ^ (2 : ℕ))))) = (((2083 : ℝ) /. (1000 : ℝ))))
  : (Real.rpow (9 : ℝ) (((3 : ℝ))⁻¹)) = (((2080 : ℝ) /. (1000 : ℝ))) := by
  sorry

theorem proof_gap_exercise_1105_1_9
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (n : ℕ)
  (x : ℝ)
  (v_uCE_uB5 : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h3 : (x ∈ (Set.univ : Set ℝ)) ∧ (((a ^ n) + x) > 0))
  (h4 : (v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0))
  (h5 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h6 : |(|(x)| - 0)| ≤ v_uCE_uB5)
  (h7 : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (y > 0))) → (((f : ℝ → _) y) = (Real.rpow y (((n : ℝ))⁻¹)))))
  (h8 : y_0 = (a ^ n))
  (h9 : v_uCE_u94_y = x)
  (h10 : DifferentiableOn ℝ f (Set.Ioi 0))
  (h11 : |((f (y_0 + v_uCE_u94_y)) - ((f y_0) + ((iteratedDeriv 1 (fun t => f t) y_0) * v_uCE_u94_y)))| ≤ v_uCE_uB5)
  (h12 : |((Real.rpow ((a ^ n) + x) (((n : ℝ))⁻¹)) - ((Real.rpow (a ^ n) (((n : ℝ))⁻¹)) + (x /. (n * (Real.rpow ((a ^ n) ^ (n - 1)) (((n : ℝ))⁻¹))))))| ≤ v_uCE_uB5)
  (h13 : |((Real.rpow ((a ^ n) + x) (((n : ℝ))⁻¹)) - (a + (x /. (n * (a ^ (n - 1))))))| ≤ v_uCE_uB5)
  (h14 : (Real.rpow (9 : ℝ) (((3 : ℝ))⁻¹)) = (Real.rpow (((2 : ℕ) ^ (3 : ℕ)) + 1) (((3 : ℝ))⁻¹)))
  (h15 : |((Real.rpow (((2 : ℕ) ^ (3 : ℕ)) + 1) (((3 : ℝ))⁻¹)) - (2 + (1 /. (3 * ((2 : ℕ) ^ (2 : ℕ))))))| ≤ v_uCE_uB5)
  (h16 : (2 + (1 /. (3 * ((2 : ℕ) ^ (2 : ℕ))))) = (((2083 : ℝ) /. (1000 : ℝ))))
  (h17 : (Real.rpow (9 : ℝ) (((3 : ℝ))⁻¹)) = (((2080 : ℝ) /. (1000 : ℝ))))
  : |((Real.rpow ((a ^ n) + x) (((n : ℝ))⁻¹)) - (a + (x /. (n * (a ^ (n - 1))))))| ≤ v_uCE_uB5 := by
  sorry

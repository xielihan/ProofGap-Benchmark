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

-- exercise: exercise_1105_4

theorem proof_gap_exercise_1105_4_1
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (x : ℝ)
  (n : ℕ)
  (v_uCE_uB5 : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : (v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0))
  (h5 : ((a ^ n) + x) > 0)
  (h6 : |(|(x)| - 0)| ≤ v_uCE_uB5)
  (h7 : f = (fun (x_1 : ℝ) (_domain : (x_1 > 0)) => (Real.rpow x_1 (((n : ℝ))⁻¹))))
  (h8 : y_0 = (a ^ n))
  (h9 : v_uCE_u94_y = x)
  : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (y > 0)) → ((f y) = (Real.rpow y (((n : ℝ))⁻¹))))) := by
  sorry

theorem proof_gap_exercise_1105_4_2
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (x : ℝ)
  (n : ℕ)
  (v_uCE_uB5 : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : (v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0))
  (h5 : ((a ^ n) + x) > 0)
  (h6 : |(|(x)| - 0)| ≤ v_uCE_uB5)
  (h7 : f = (fun (x_1 : ℝ) (_domain : (x_1 > 0)) => (Real.rpow x_1 (((n : ℝ))⁻¹))))
  (h8 : y_0 = (a ^ n))
  (h9 : v_uCE_u94_y = x)
  (h10 : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (y > 0)) → ((f y) = (Real.rpow y (((n : ℝ))⁻¹))))))
  : DifferentiableOn ℝ f (Set.Ioi 0) := by
  sorry

theorem proof_gap_exercise_1105_4_3
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (x : ℝ)
  (n : ℕ)
  (v_uCE_uB5 : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : (n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1})))
  (h4 : (v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0))
  (h5 : ((a ^ n) + x) > 0)
  (h6 : |(|(x)| - 0)| ≤ v_uCE_uB5)
  (h7 : f = (fun (y : ℝ) => (Real.rpow y (((n : ℝ))⁻¹))))
  (h8 : y_0 = (a ^ n))
  (h9 : v_uCE_u94_y = x)
  (h10 : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (y > 0)) → ((f y) = (Real.rpow y (((n : ℝ))⁻¹))))))
  (h11 : DifferentiableOn ℝ f (Set.Ioi 0))
  : |((f (y_0 + v_uCE_u94_y)) - ((f y_0) + ((iteratedDeriv 1 (fun t => f t) y_0) * v_uCE_u94_y)))| ≤ v_uCE_uB5 := by
  sorry

theorem proof_gap_exercise_1105_4_4
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (x : ℝ)
  (n : ℕ)
  (v_uCE_uB5 : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : (v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0))
  (h5 : ((a ^ n) + x) > 0)
  (h6 : |(|(x)| - 0)| ≤ v_uCE_uB5)
  (h7 : f = (fun (x_1 : ℝ) (_domain : (x_1 > 0)) => (Real.rpow x_1 (((n : ℝ))⁻¹))))
  (h8 : y_0 = (a ^ n))
  (h9 : v_uCE_u94_y = x)
  (h10 : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (y > 0)) → ((f y) = (Real.rpow y (((n : ℝ))⁻¹))))))
  (h11 : DifferentiableOn ℝ f (Set.Ioi 0))
  (h12 : |((f (y_0 + v_uCE_u94_y)) - ((f y_0) + ((iteratedDeriv 1 (fun t => f t) y_0) * v_uCE_u94_y)))| ≤ v_uCE_uB5)
  : |((Real.rpow ((a ^ n) + x) (((n : ℝ))⁻¹)) - ((Real.rpow (a ^ n) (((n : ℝ))⁻¹)) + (x /. (n * (Real.rpow ((a ^ n) ^ (n - 1)) (((n : ℝ))⁻¹))))))| ≤ v_uCE_uB5 := by
  sorry

theorem proof_gap_exercise_1105_4_5
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (x : ℝ)
  (n : ℕ)
  (v_uCE_uB5 : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : (v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0))
  (h5 : ((a ^ n) + x) > 0)
  (h6 : |(|(x)| - 0)| ≤ v_uCE_uB5)
  (h7 : f = (fun (x_1 : ℝ) (_domain : (x_1 > 0)) => (Real.rpow x_1 (((n : ℝ))⁻¹))))
  (h8 : y_0 = (a ^ n))
  (h9 : v_uCE_u94_y = x)
  (h10 : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (y > 0)) → ((f y) = (Real.rpow y (((n : ℝ))⁻¹))))))
  (h11 : DifferentiableOn ℝ f (Set.Ioi 0))
  (h12 : |((f (y_0 + v_uCE_u94_y)) - ((f y_0) + ((iteratedDeriv 1 (fun t => f t) y_0) * v_uCE_u94_y)))| ≤ v_uCE_uB5)
  (h13 : |((Real.rpow ((a ^ n) + x) (((n : ℝ))⁻¹)) - ((Real.rpow (a ^ n) (((n : ℝ))⁻¹)) + (x /. (n * (Real.rpow ((a ^ n) ^ (n - 1)) (((n : ℝ))⁻¹))))))| ≤ v_uCE_uB5)
  : |((Real.rpow ((a ^ n) + x) (((n : ℝ))⁻¹)) - (a + (x /. (n * (a ^ (n - 1))))))| ≤ v_uCE_uB5 := by
  sorry

theorem proof_gap_exercise_1105_4_6
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (x : ℝ)
  (n : ℕ)
  (v_uCE_uB5 : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : (n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1})))
  (h4 : (v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0))
  (h5 : ((a ^ n) + x) > 0)
  (h6 : |(|(x)| - 0)| ≤ v_uCE_uB5)
  (h7 : f = (fun (y : ℝ) => (Real.rpow y (((n : ℝ))⁻¹))))
  (h8 : y_0 = (a ^ n))
  (h9 : v_uCE_u94_y = x)
  (h10 : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (y > 0)) → ((f y) = (Real.rpow y (((n : ℝ))⁻¹))))))
  (h11 : DifferentiableOn ℝ f (Set.Ioi 0))
  (h12 : |((f (y_0 + v_uCE_u94_y)) - ((f y_0) + ((iteratedDeriv 1 (fun t => f t) y_0) * v_uCE_u94_y)))| ≤ v_uCE_uB5)
  (h13 : |((Real.rpow ((a ^ n) + x) (((n : ℝ))⁻¹)) - ((Real.rpow (a ^ n) (((n : ℝ))⁻¹)) + (x /. (n * (Real.rpow ((a ^ n) ^ (n - 1)) (((n : ℝ))⁻¹))))))| ≤ v_uCE_uB5)
  (h14 : |((Real.rpow ((a ^ n) + x) (((n : ℝ))⁻¹)) - (a + (x /. (n * (a ^ (n - 1))))))| ≤ v_uCE_uB5)
  : (Real.rpow (1000 : ℝ) (((10 : ℝ))⁻¹)) = (Real.rpow (((2 : ℕ) ^ (10 : ℕ)) - 24) (((10 : ℝ))⁻¹)) := by
  sorry

theorem proof_gap_exercise_1105_4_7
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (x : ℝ)
  (n : ℕ)
  (v_uCE_uB5 : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : (n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1})))
  (h4 : (v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0))
  (h5 : ((a ^ n) + x) > 0)
  (h6 : |(|(x)| - 0)| ≤ v_uCE_uB5)
  (h7 : f = (fun (y : ℝ) => (Real.rpow y (((n : ℝ))⁻¹))))
  (h8 : y_0 = (a ^ n))
  (h9 : v_uCE_u94_y = x)
  (h10 : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (y > 0)) → ((f y) = (Real.rpow y (((n : ℝ))⁻¹))))))
  (h11 : DifferentiableOn ℝ f (Set.Ioi 0))
  (h12 : |((f (y_0 + v_uCE_u94_y)) - ((f y_0) + ((iteratedDeriv 1 (fun t => f t) y_0) * v_uCE_u94_y)))| ≤ v_uCE_uB5)
  (h13 : |((Real.rpow ((a ^ n) + x) (((n : ℝ))⁻¹)) - ((Real.rpow (a ^ n) (((n : ℝ))⁻¹)) + (x /. (n * (Real.rpow ((a ^ n) ^ (n - 1)) (((n : ℝ))⁻¹))))))| ≤ v_uCE_uB5)
  (h14 : |((Real.rpow ((a ^ n) + x) (((n : ℝ))⁻¹)) - (a + (x /. (n * (a ^ (n - 1))))))| ≤ v_uCE_uB5)
  (h15 : (Real.rpow (1000 : ℝ) (((10 : ℝ))⁻¹)) = (Real.rpow (((2 : ℕ) ^ (10 : ℕ)) - 24) (((10 : ℝ))⁻¹)))
  : |((Real.rpow (((2 : ℕ) ^ (10 : ℕ)) - 24) (((10 : ℝ))⁻¹)) - (2 - (24 /. (10 * ((2 : ℕ) ^ (9 : ℕ))))))| ≤ v_uCE_uB5 := by
  sorry

theorem proof_gap_exercise_1105_4_8
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (x : ℝ)
  (n : ℕ)
  (v_uCE_uB5 : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : (n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1})))
  (h4 : (v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0))
  (h5 : ((a ^ n) + x) > 0)
  (h6 : |(|(x)| - 0)| ≤ v_uCE_uB5)
  (h7 : f = (fun (y : ℝ) => (Real.rpow y (((n : ℝ))⁻¹))))
  (h8 : y_0 = (a ^ n))
  (h9 : v_uCE_u94_y = x)
  (h10 : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (y > 0)) → ((f y) = (Real.rpow y (((n : ℝ))⁻¹))))))
  (h11 : DifferentiableOn ℝ f (Set.Ioi 0))
  (h12 : |((f (y_0 + v_uCE_u94_y)) - ((f y_0) + ((iteratedDeriv 1 (fun t => f t) y_0) * v_uCE_u94_y)))| ≤ v_uCE_uB5)
  (h13 : |((Real.rpow ((a ^ n) + x) (((n : ℝ))⁻¹)) - ((Real.rpow (a ^ n) (((n : ℝ))⁻¹)) + (x /. (n * (Real.rpow ((a ^ n) ^ (n - 1)) (((n : ℝ))⁻¹))))))| ≤ v_uCE_uB5)
  (h14 : |((Real.rpow ((a ^ n) + x) (((n : ℝ))⁻¹)) - (a + (x /. (n * (a ^ (n - 1))))))| ≤ v_uCE_uB5)
  (h15 : (Real.rpow (1000 : ℝ) (((10 : ℝ))⁻¹)) = (Real.rpow (((2 : ℕ) ^ (10 : ℕ)) - 24) (((10 : ℝ))⁻¹)))
  (h16 : |((Real.rpow (((2 : ℕ) ^ (10 : ℕ)) - 24) (((10 : ℝ))⁻¹)) - (2 - (24 /. (10 * ((2 : ℕ) ^ (9 : ℕ))))))| ≤ v_uCE_uB5)
  : (2 - (24 /. (10 * ((2 : ℕ) ^ (9 : ℕ))))) = (((19953 : ℝ) /. (10000 : ℝ))) := by
  sorry

theorem proof_gap_exercise_1105_4_9
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (x : ℝ)
  (n : ℕ)
  (v_uCE_uB5 : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : (n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1})))
  (h4 : (v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0))
  (h5 : ((a ^ n) + x) > 0)
  (h6 : |(|(x)| - 0)| ≤ v_uCE_uB5)
  (h7 : f = (fun (y : ℝ) => (Real.rpow y (((n : ℝ))⁻¹))))
  (h8 : y_0 = (a ^ n))
  (h9 : v_uCE_u94_y = x)
  (h10 : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (y > 0)) → ((f y) = (Real.rpow y (((n : ℝ))⁻¹))))))
  (h11 : DifferentiableOn ℝ f (Set.Ioi 0))
  (h12 : |((f (y_0 + v_uCE_u94_y)) - ((f y_0) + ((iteratedDeriv 1 (fun t => f t) y_0) * v_uCE_u94_y)))| ≤ v_uCE_uB5)
  (h13 : |((Real.rpow ((a ^ n) + x) (((n : ℝ))⁻¹)) - ((Real.rpow (a ^ n) (((n : ℝ))⁻¹)) + (x /. (n * (Real.rpow ((a ^ n) ^ (n - 1)) (((n : ℝ))⁻¹))))))| ≤ v_uCE_uB5)
  (h14 : |((Real.rpow ((a ^ n) + x) (((n : ℝ))⁻¹)) - (a + (x /. (n * (a ^ (n - 1))))))| ≤ v_uCE_uB5)
  (h15 : (Real.rpow (1000 : ℝ) (((10 : ℝ))⁻¹)) = (Real.rpow (((2 : ℕ) ^ (10 : ℕ)) - 24) (((10 : ℝ))⁻¹)))
  (h16 : |((Real.rpow (((2 : ℕ) ^ (10 : ℕ)) - 24) (((10 : ℝ))⁻¹)) - (2 - (24 /. (10 * ((2 : ℕ) ^ (9 : ℕ))))))| ≤ v_uCE_uB5)
  (h17 : (2 - (24 /. (10 * ((2 : ℕ) ^ (9 : ℕ))))) = (((19953 : ℝ) /. (10000 : ℝ))))
  : (Real.rpow (1000 : ℝ) (((10 : ℝ))⁻¹)) = (((19953 : ℝ) /. (10000 : ℝ))) := by
  sorry

theorem proof_gap_exercise_1105_4_10
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (x : ℝ)
  (n : ℕ)
  (v_uCE_uB5 : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : (n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1})))
  (h4 : (v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0))
  (h5 : ((a ^ n) + x) > 0)
  (h6 : |(|(x)| - 0)| ≤ v_uCE_uB5)
  (h7 : f = (fun (y : ℝ) => (Real.rpow y (((n : ℝ))⁻¹))))
  (h8 : y_0 = (a ^ n))
  (h9 : v_uCE_u94_y = x)
  (h10 : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (y > 0)) → ((f y) = (Real.rpow y (((n : ℝ))⁻¹))))))
  (h11 : DifferentiableOn ℝ f (Set.Ioi 0))
  (h12 : |((f (y_0 + v_uCE_u94_y)) - ((f y_0) + ((iteratedDeriv 1 (fun t => f t) y_0) * v_uCE_u94_y)))| ≤ v_uCE_uB5)
  (h13 : |((Real.rpow ((a ^ n) + x) (((n : ℝ))⁻¹)) - ((Real.rpow (a ^ n) (((n : ℝ))⁻¹)) + (x /. (n * (Real.rpow ((a ^ n) ^ (n - 1)) (((n : ℝ))⁻¹))))))| ≤ v_uCE_uB5)
  (h14 : |((Real.rpow ((a ^ n) + x) (((n : ℝ))⁻¹)) - (a + (x /. (n * (a ^ (n - 1))))))| ≤ v_uCE_uB5)
  (h15 : (Real.rpow (1000 : ℝ) (((10 : ℝ))⁻¹)) = (Real.rpow (((2 : ℕ) ^ (10 : ℕ)) - 24) (((10 : ℝ))⁻¹)))
  (h16 : |((Real.rpow (((2 : ℕ) ^ (10 : ℕ)) - 24) (((10 : ℝ))⁻¹)) - (2 - (24 /. (10 * ((2 : ℕ) ^ (9 : ℕ))))))| ≤ v_uCE_uB5)
  (h17 : (2 - (24 /. (10 * ((2 : ℕ) ^ (9 : ℕ))))) = (((19953 : ℝ) /. (10000 : ℝ))))
  (h18 : (Real.rpow (1000 : ℝ) (((10 : ℝ))⁻¹)) = (((19953 : ℝ) /. (10000 : ℝ))))
  : |((Real.rpow ((a ^ n) + x) (((n : ℝ))⁻¹)) - (a + (x /. (n * (a ^ (n - 1))))))| ≤ v_uCE_uB5 := by
  sorry

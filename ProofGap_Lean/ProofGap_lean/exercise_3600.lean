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

-- exercise: exercise_3600

theorem proof_gap_exercise_3600_1
  (f : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((1 + x) > 0)) ∧ ((1 + y) > 0)) → ((f (x, y)) = ((Real.log (1 + x)) * (Real.log (1 + y)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((Real.log (1 + x)) = (∑' m, if (1 : ℕ) ≤ m then (((-(1 : ℤ)) ^ (m - 1)) * ((x ^ m) /. m)) else 0)))) := by
  sorry

theorem proof_gap_exercise_3600_2
  (f : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((1 + x) > 0)) ∧ ((1 + y) > 0)) → ((f (x, y)) = ((Real.log (1 + x)) * (Real.log (1 + y)))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((Real.log (1 + x)) = (∑' m, if (1 : ℕ) ≤ m then (((-(1 : ℤ)) ^ (m - 1)) * ((x ^ m) /. m)) else 0)))))
  : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (|(y)| < 1)) → ((Real.log (1 + y)) = (∑' n, if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ (n - 1)) * ((y ^ n) /. n)) else 0)))) := by
  sorry

theorem proof_gap_exercise_3600_3
  (f : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((1 + x) > 0)) ∧ ((1 + y) > 0)) → ((f (x, y)) = ((Real.log (1 + x)) * (Real.log (1 + y)))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((Real.log (1 + x)) = (∑' m, if (1 : ℕ) ≤ m then (((-(1 : ℤ)) ^ (m - 1)) * ((x ^ m) /. m)) else 0)))))
  (h3 : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (|(y)| < 1)) → ((Real.log (1 + y)) = (∑' n, if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ (n - 1)) * ((y ^ n) /. n)) else 0)))))
  : (forall (x : ℝ) (y : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (|(y)| < 1)) → ((f (x, y)) = ((∑' m, if (1 : ℕ) ≤ m then (((-(1 : ℤ)) ^ (m - 1)) * ((x ^ m) /. m)) else 0) * (∑' n, if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ (n - 1)) * ((y ^ n) /. n)) else 0))))) := by
  sorry

theorem proof_gap_exercise_3600_4
  (f : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((1 + x) > 0)) ∧ ((1 + y) > 0)) → ((f (x, y)) = ((Real.log (1 + x)) * (Real.log (1 + y)))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((Real.log (1 + x)) = (∑' m, if (1 : ℕ) ≤ m then (((-(1 : ℤ)) ^ (m - 1)) * ((x ^ m) /. m)) else 0)))))
  (h3 : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (|(y)| < 1)) → ((Real.log (1 + y)) = (∑' n, if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ (n - 1)) * ((y ^ n) /. n)) else 0)))))
  (h4 : (forall (x : ℝ) (y : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (|(y)| < 1)) → ((f (x, y)) = ((∑' m, if (1 : ℕ) ≤ m then (((-(1 : ℤ)) ^ (m - 1)) * ((x ^ m) /. m)) else 0) * (∑' n, if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ (n - 1)) * ((y ^ n) /. n)) else 0))))))
  : (forall (x : ℝ) (y : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (|(y)| < 1)) → ((f (x, y)) = (∑' m, if (1 : ℕ) ≤ m then (∑' n, if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ (m + n)) * (((x ^ m) * (y ^ n)) /. (m * n))) else 0) else 0)))) := by
  sorry

theorem proof_gap_exercise_3600_5
  (f : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((1 + x) > 0)) ∧ ((1 + y) > 0)) → ((f (x, y)) = ((Real.log (1 + x)) * (Real.log (1 + y)))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((Real.log (1 + x)) = (∑' m, if (1 : ℕ) ≤ m then (((-(1 : ℤ)) ^ (m - 1)) * ((x ^ m) /. m)) else 0)))))
  (h3 : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (|(y)| < 1)) → ((Real.log (1 + y)) = (∑' n, if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ (n - 1)) * ((y ^ n) /. n)) else 0)))))
  (h4 : (forall (x : ℝ) (y : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (|(y)| < 1)) → ((f (x, y)) = ((∑' m, if (1 : ℕ) ≤ m then (((-(1 : ℤ)) ^ (m - 1)) * ((x ^ m) /. m)) else 0) * (∑' n, if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ (n - 1)) * ((y ^ n) /. n)) else 0))))))
  (h5 : (forall (x : ℝ) (y : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (|(y)| < 1)) → ((f (x, y)) = (∑' m, if (1 : ℕ) ≤ m then (∑' n, if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ (m + n)) * (((x ^ m) * (y ^ n)) /. (m * n))) else 0) else 0)))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (|(x)| < 1))) := by
  sorry

theorem proof_gap_exercise_3600_6
  (f : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((1 + x) > 0)) ∧ ((1 + y) > 0)) → ((f (x, y)) = ((Real.log (1 + x)) * (Real.log (1 + y)))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((Real.log (1 + x)) = (∑' m, if (1 : ℕ) ≤ m then (((-(1 : ℤ)) ^ (m - 1)) * ((x ^ m) /. m)) else 0)))))
  (h3 : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (|(y)| < 1)) → ((Real.log (1 + y)) = (∑' n, if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ (n - 1)) * ((y ^ n) /. n)) else 0)))))
  (h4 : (forall (x : ℝ) (y : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (|(y)| < 1)) → ((f (x, y)) = ((∑' m, if (1 : ℕ) ≤ m then (((-(1 : ℤ)) ^ (m - 1)) * ((x ^ m) /. m)) else 0) * (∑' n, if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ (n - 1)) * ((y ^ n) /. n)) else 0))))))
  (h5 : (forall (x : ℝ) (y : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (|(y)| < 1)) → ((f (x, y)) = (∑' m, if (1 : ℕ) ≤ m then (∑' n, if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ (m + n)) * (((x ^ m) * (y ^ n)) /. (m * n))) else 0) else 0)))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (|(x)| < 1))))
  : (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → (|(y)| < 1))) := by
  sorry

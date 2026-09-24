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

-- exercise: exercise_1208

theorem proof_gap_exercise_1208_1
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (n : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : n ∈ (Set.univ : Set ℕ))
  (h4 : b ≠ 0)
  (h5 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (((a + (b * x)) /. (a - (b * x))) > 0)) ∧ ((a - (b * x)) ≠ 0)) → ((y x) = (Real.log ((a + (b * x)) /. (a - (b * x))))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (((a + (b * x)) /. (a - (b * x))) > 0)) ∧ ((a - (b * x)) ≠ 0)) → ((iteratedDeriv 1 (fun t => y t) x) = ((b /. (a + (b * x))) + (b /. (a - (b * x))))))) := by
  sorry

theorem proof_gap_exercise_1208_2
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (n : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : n ∈ (Set.univ : Set ℕ))
  (h4 : b ≠ 0)
  (h5 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (((a + (b * x)) /. (a - (b * x))) > 0)) ∧ ((a - (b * x)) ≠ 0)) → ((y x) = (Real.log ((a + (b * x)) /. (a - (b * x))))))))
  (h7 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (((a + (b * x)) /. (a - (b * x))) > 0)) ∧ ((a - (b * x)) ≠ 0)) → ((iteratedDeriv 1 (fun t => y t) x) = ((b /. (a + (b * x))) + (b /. (a - (b * x))))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (((a + (b * x)) /. (a - (b * x))) > 0)) ∧ ((a - (b * x)) ≠ 0)) → ((iteratedDeriv n (fun t => y t) x) = (iteratedDeriv ((1 + n) - 1) (fun t => y t) x)))) := by
  sorry

theorem proof_gap_exercise_1208_3
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (n : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : n ∈ (Set.univ : Set ℕ))
  (h4 : b ≠ 0)
  (h5 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (((a + (b * x)) /. (a - (b * x))) > 0)) ∧ ((a - (b * x)) ≠ 0)) → ((y x) = (Real.log ((a + (b * x)) /. (a - (b * x))))))))
  (h7 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (((a + (b * x)) /. (a - (b * x))) > 0)) ∧ ((a - (b * x)) ≠ 0)) → ((iteratedDeriv 1 (fun t => y t) x) = ((b /. (a + (b * x))) + (b /. (a - (b * x))))))))
  (h8 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (((a + (b * x)) /. (a - (b * x))) > 0)) ∧ ((a - (b * x)) ≠ 0)) → ((iteratedDeriv n (fun t => y t) x) = (iteratedDeriv ((1 + n) - 1) (fun t => y t) x)))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (((a + (b * x)) /. (a - (b * x))) > 0)) ∧ ((a - (b * x)) ≠ 0)) → ((iteratedDeriv ((1 + n) - 1) (fun t => y t) x) = ((iteratedDeriv (n - 1) (fun t => (b /. (a + (b * t)))) x) + (iteratedDeriv (n - 1) (fun t => (b /. (a - (b * t)))) x))))) := by
  sorry

theorem proof_gap_exercise_1208_4
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (n : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : n ∈ (Set.univ : Set ℕ))
  (h4 : b ≠ 0)
  (h5 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (((a + (b * x)) /. (a - (b * x))) > 0)) ∧ ((a - (b * x)) ≠ 0)) → ((y x) = (Real.log ((a + (b * x)) /. (a - (b * x))))))))
  (h7 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (((a + (b * x)) /. (a - (b * x))) > 0)) ∧ ((a - (b * x)) ≠ 0)) → ((iteratedDeriv 1 (fun t => y t) x) = ((b /. (a + (b * x))) + (b /. (a - (b * x))))))))
  (h8 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (((a + (b * x)) /. (a - (b * x))) > 0)) ∧ ((a - (b * x)) ≠ 0)) → ((iteratedDeriv n (fun t => y t) x) = (iteratedDeriv ((1 + n) - 1) (fun t => y t) x)))))
  (h9 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (((a + (b * x)) /. (a - (b * x))) > 0)) ∧ ((a - (b * x)) ≠ 0)) → ((iteratedDeriv ((1 + n) - 1) (fun t => y t) x) = ((iteratedDeriv (n - 1) (fun t => (b /. (a + (b * t)))) x) + (iteratedDeriv (n - 1) (fun t => (b /. (a - (b * t)))) x))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (((a + (b * x)) /. (a - (b * x))) > 0)) ∧ ((a - (b * x)) ≠ 0)) → ((iteratedDeriv n (fun t => y t) x) = ((iteratedDeriv (n - 1) (fun t => (b /. (a + (b * t)))) x) + (iteratedDeriv (n - 1) (fun t => (b /. (a - (b * t)))) x))))) := by
  sorry

theorem proof_gap_exercise_1208_5
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (n : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : n ∈ (Set.univ : Set ℕ))
  (h4 : b ≠ 0)
  (h5 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (((a + (b * x)) /. (a - (b * x))) > 0)) ∧ ((a - (b * x)) ≠ 0)) → ((y x) = (Real.log ((a + (b * x)) /. (a - (b * x))))))))
  (h7 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (((a + (b * x)) /. (a - (b * x))) > 0)) ∧ ((a - (b * x)) ≠ 0)) → ((iteratedDeriv 1 (fun t => y t) x) = ((b /. (a + (b * x))) + (b /. (a - (b * x))))))))
  (h8 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (((a + (b * x)) /. (a - (b * x))) > 0)) ∧ ((a - (b * x)) ≠ 0)) → ((iteratedDeriv n (fun t => y t) x) = (iteratedDeriv ((1 + n) - 1) (fun t => y t) x)))))
  (h9 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (((a + (b * x)) /. (a - (b * x))) > 0)) ∧ ((a - (b * x)) ≠ 0)) → ((iteratedDeriv ((1 + n) - 1) (fun t => y t) x) = ((iteratedDeriv (n - 1) (fun t => (b /. (a + (b * t)))) x) + (iteratedDeriv (n - 1) (fun t => (b /. (a - (b * t)))) x))))))
  (h10 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (((a + (b * x)) /. (a - (b * x))) > 0)) ∧ ((a - (b * x)) ≠ 0)) → ((iteratedDeriv n (fun t => y t) x) = ((iteratedDeriv (n - 1) (fun t => (b /. (a + (b * t)))) x) + (iteratedDeriv (n - 1) (fun t => (b /. (a - (b * t)))) x))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (((a + (b * x)) /. (a - (b * x))) > 0)) ∧ ((a - (b * x)) ≠ 0)) → ((iteratedDeriv n (fun t => y t) x) = ((((((-(1 : ℤ)) ^ (n - 1)) * (b ^ n)) * ((n - 1))!) /. ((a + (b * x)) ^ n)) + (((b ^ n) * ((n - 1))!) /. ((a - (b * x)) ^ n)))))) := by
  sorry

theorem proof_gap_exercise_1208_6
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (n : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : n ∈ (Set.univ : Set ℕ))
  (h4 : b ≠ 0)
  (h5 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (((a + (b * x)) /. (a - (b * x))) > 0)) ∧ ((a - (b * x)) ≠ 0)) → ((y x) = (Real.log ((a + (b * x)) /. (a - (b * x))))))))
  (h7 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (((a + (b * x)) /. (a - (b * x))) > 0)) ∧ ((a - (b * x)) ≠ 0)) → ((iteratedDeriv 1 (fun t => y t) x) = ((b /. (a + (b * x))) + (b /. (a - (b * x))))))))
  (h8 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (((a + (b * x)) /. (a - (b * x))) > 0)) ∧ ((a - (b * x)) ≠ 0)) → ((iteratedDeriv n (fun t => y t) x) = (iteratedDeriv ((1 + n) - 1) (fun t => y t) x)))))
  (h9 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (((a + (b * x)) /. (a - (b * x))) > 0)) ∧ ((a - (b * x)) ≠ 0)) → ((iteratedDeriv ((1 + n) - 1) (fun t => y t) x) = ((iteratedDeriv (n - 1) (fun t => (b /. (a + (b * t)))) x) + (iteratedDeriv (n - 1) (fun t => (b /. (a - (b * t)))) x))))))
  (h10 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (((a + (b * x)) /. (a - (b * x))) > 0)) ∧ ((a - (b * x)) ≠ 0)) → ((iteratedDeriv n (fun t => y t) x) = ((iteratedDeriv (n - 1) (fun t => (b /. (a + (b * t)))) x) + (iteratedDeriv (n - 1) (fun t => (b /. (a - (b * t)))) x))))))
  (h11 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (((a + (b * x)) /. (a - (b * x))) > 0)) ∧ ((a - (b * x)) ≠ 0)) → ((iteratedDeriv n (fun t => y t) x) = ((((((-(1 : ℤ)) ^ (n - 1)) * (b ^ n)) * ((n - 1))!) /. ((a + (b * x)) ^ n)) + (((b ^ n) * ((n - 1))!) /. ((a - (b * x)) ^ n)))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (((a + (b * x)) /. (a - (b * x))) > 0)) ∧ ((a - (b * x)) ≠ 0)) → ((iteratedDeriv n (fun t => y t) x) = (((((n - 1))! * (b ^ n)) /. (((a ^ (2 : ℕ)) - ((b ^ (2 : ℕ)) * (x ^ (2 : ℕ)))) ^ n)) * (((a + (b * x)) ^ n) + (((-(1 : ℤ)) ^ (n - 1)) * ((a - (b * x)) ^ n))))))) := by
  sorry

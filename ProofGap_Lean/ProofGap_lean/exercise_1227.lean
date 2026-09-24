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

-- exercise: exercise_1227

theorem proof_gap_exercise_1227_1
  (P : (ℕ × ℝ -> ℝ))
  (h1 : (forall (m : ℕ) (x : ℝ), (((m ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) → ((P (m, x)) = ((1 /. (((2 : ℕ) ^ m) * (m)!)) * (iteratedDeriv m (fun t => (((t ^ (2 : ℕ)) - 1) ^ m)) x))))))
  (h2 : (exists (y : (ℝ -> ℝ)), (forall (m : ℕ), ((m ∈ (Set.univ : Set ℕ)) → (y = (fun (x : ℝ) => (((x ^ (2 : ℕ)) - 1) ^ m)))))))
  : (forall (y : (ℝ -> ℝ)) (m : ℕ) (x : ℝ), (((m ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => y t) x) = (((2 * m) * x) * (((x ^ (2 : ℕ)) - 1) ^ (m - 1)))))) := by
  sorry

theorem proof_gap_exercise_1227_2
  (P : (ℕ × ℝ -> ℝ))
  (h1 : (forall (m : ℕ) (x : ℝ), (((m ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) → ((P (m, x)) = ((1 /. (((2 : ℕ) ^ m) * (m)!)) * (iteratedDeriv m (fun t => (((t ^ (2 : ℕ)) - 1) ^ m)) x))))))
  (h2 : (exists (y : (ℝ -> ℝ)), (forall (m : ℕ), ((m ∈ (Set.univ : Set ℕ)) → (y = (fun (x : ℝ) => (((x ^ (2 : ℕ)) - 1) ^ m)))))))
  (h3 : (forall (y : (ℝ -> ℝ)) (m : ℕ) (x : ℝ), (((m ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => y t) x) = (((2 * m) * x) * (((x ^ (2 : ℕ)) - 1) ^ (m - 1)))))))
  : (forall (y : (ℝ -> ℝ)) (m : ℕ) (x : ℝ), (((m ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) → ((((x ^ (2 : ℕ)) - 1) * (iteratedDeriv 1 (fun t => y t) x)) = (((2 * m) * x) * (y x))))) := by
  sorry

theorem proof_gap_exercise_1227_3
  (P : (ℕ × ℝ -> ℝ))
  (h1 : (forall (m : ℕ) (x : ℝ), (((m ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) → ((P (m, x)) = ((1 /. (((2 : ℕ) ^ m) * (m)!)) * (iteratedDeriv m (fun t => (((t ^ (2 : ℕ)) - 1) ^ m)) x))))))
  (h2 : (exists (y : (ℝ -> ℝ)), (forall (m : ℕ), ((m ∈ (Set.univ : Set ℕ)) → (y = (fun (x : ℝ) => (((x ^ (2 : ℕ)) - 1) ^ m)))))))
  (h3 : (forall (y : (ℝ -> ℝ)) (m : ℕ) (x : ℝ), (((m ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => y t) x) = (((2 * m) * x) * (((x ^ (2 : ℕ)) - 1) ^ (m - 1)))))))
  (h4 : (forall (y : (ℝ -> ℝ)) (m : ℕ) (x : ℝ), (((m ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) → ((((x ^ (2 : ℕ)) - 1) * (iteratedDeriv 1 (fun t => y t) x)) = (((2 * m) * x) * (y x))))))
  : (forall (y : (ℝ -> ℝ)) (m : ℕ) (x : ℝ), (((m ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) → ((((((x ^ (2 : ℕ)) - 1) * (iteratedDeriv (m + 2) (fun t => y t) x)) + (((2 * (m + 1)) * x) * (iteratedDeriv (m + 1) (fun t => y t) x))) + ((m * (m + 1)) * (iteratedDeriv m (fun t => y t) x))) = ((((2 * m) * x) * (iteratedDeriv (m + 1) (fun t => y t) x)) + (((2 * m) * (m + 1)) * (iteratedDeriv m (fun t => y t) x)))))) := by
  sorry

theorem proof_gap_exercise_1227_4
  (P : (ℕ × ℝ -> ℝ))
  (h1 : (forall (m : ℕ) (x : ℝ), (((m ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) → ((P (m, x)) = ((1 /. (((2 : ℕ) ^ m) * (m)!)) * (iteratedDeriv m (fun t => (((t ^ (2 : ℕ)) - 1) ^ m)) x))))))
  (h2 : (exists (y : (ℝ -> ℝ)), (forall (m : ℕ), ((m ∈ (Set.univ : Set ℕ)) → (y = (fun (x : ℝ) => (((x ^ (2 : ℕ)) - 1) ^ m)))))))
  (h3 : (forall (y : (ℝ -> ℝ)) (m : ℕ) (x : ℝ), (((m ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => y t) x) = (((2 * m) * x) * (((x ^ (2 : ℕ)) - 1) ^ (m - 1)))))))
  (h4 : (forall (y : (ℝ -> ℝ)) (m : ℕ) (x : ℝ), (((m ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) → ((((x ^ (2 : ℕ)) - 1) * (iteratedDeriv 1 (fun t => y t) x)) = (((2 * m) * x) * (y x))))))
  (h5 : (forall (y : (ℝ -> ℝ)) (m : ℕ) (x : ℝ), (((m ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) → ((((((x ^ (2 : ℕ)) - 1) * (iteratedDeriv (m + 2) (fun t => y t) x)) + (((2 * (m + 1)) * x) * (iteratedDeriv (m + 1) (fun t => y t) x))) + ((m * (m + 1)) * (iteratedDeriv m (fun t => y t) x))) = ((((2 * m) * x) * (iteratedDeriv (m + 1) (fun t => y t) x)) + (((2 * m) * (m + 1)) * (iteratedDeriv m (fun t => y t) x)))))))
  : (forall (y : (ℝ -> ℝ)) (m : ℕ) (x : ℝ), (((m ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) → ((((((x ^ (2 : ℕ)) - 1) * (iteratedDeriv (m + 2) (fun t => y t) x)) + ((2 * x) * (iteratedDeriv (m + 1) (fun t => y t) x))) - ((m * (m + 1)) * (iteratedDeriv m (fun t => y t) x))) = 0))) := by
  sorry

theorem proof_gap_exercise_1227_5
  (P : (ℕ × ℝ -> ℝ))
  (h1 : (forall (m : ℕ) (x : ℝ), (((m ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) → ((P (m, x)) = ((1 /. (((2 : ℕ) ^ m) * (m)!)) * (iteratedDeriv m (fun t => (((t ^ (2 : ℕ)) - 1) ^ m)) x))))))
  (h2 : (forall (m : ℕ), ((m ∈ (Set.univ : Set ℕ)) → (ContDiff ℝ (2 : ℕ∞) (fun (x : ℝ) => (P (m, x)))))))
  : (forall (m : ℕ) (x : ℝ), (((m ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) → ((((((x ^ (2 : ℕ)) - 1) * (iteratedDeriv 2 (fun t => (P (m, t))) x)) + ((2 * x) * (iteratedDeriv 1 (fun t => (P (m, t))) x))) - ((m * (m + 1)) * (P (m, x)))) = 0))) := by
  sorry

theorem proof_gap_exercise_1227_6
  (P : (ℕ × ℝ -> ℝ))
  (h1 : (forall (m : ℕ) (x : ℝ), (((m ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) → ((P (m, x)) = ((1 /. (((2 : ℕ) ^ m) * (m)!)) * (iteratedDeriv m (fun t => (((t ^ (2 : ℕ)) - 1) ^ m)) x))))))
  (h2 : (exists (y : (ℝ -> ℝ)), (forall (m : ℕ), ((m ∈ (Set.univ : Set ℕ)) → (y = (fun (x : ℝ) => (((x ^ (2 : ℕ)) - 1) ^ m)))))))
  (h3 : (forall (y : (ℝ -> ℝ)) (m : ℕ) (x : ℝ), (((m ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => y t) x) = (((2 * m) * x) * (((x ^ (2 : ℕ)) - 1) ^ (m - 1)))))))
  (h4 : (forall (y : (ℝ -> ℝ)) (m : ℕ) (x : ℝ), (((m ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) → ((((x ^ (2 : ℕ)) - 1) * (iteratedDeriv 1 (fun t => y t) x)) = (((2 * m) * x) * (y x))))))
  (h5 : (forall (y : (ℝ -> ℝ)) (m : ℕ) (x : ℝ), (((m ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) → ((((((x ^ (2 : ℕ)) - 1) * (iteratedDeriv (m + 2) (fun t => y t) x)) + (((2 * (m + 1)) * x) * (iteratedDeriv (m + 1) (fun t => y t) x))) + ((m * (m + 1)) * (iteratedDeriv m (fun t => y t) x))) = ((((2 * m) * x) * (iteratedDeriv (m + 1) (fun t => y t) x)) + (((2 * m) * (m + 1)) * (iteratedDeriv m (fun t => y t) x)))))))
  (h6 : (forall (y : (ℝ -> ℝ)) (m : ℕ) (x : ℝ), (((m ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) → ((((((x ^ (2 : ℕ)) - 1) * (iteratedDeriv (m + 2) (fun t => y t) x)) + ((2 * x) * (iteratedDeriv (m + 1) (fun t => y t) x))) - ((m * (m + 1)) * (iteratedDeriv m (fun t => y t) x))) = 0))))
  (h7 : (forall (m : ℕ) (x : ℝ), (((m ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) → ((((((x ^ (2 : ℕ)) - 1) * (iteratedDeriv 2 (fun t => (P (m, t))) x)) + ((2 * x) * (iteratedDeriv 1 (fun t => (P (m, t))) x))) - ((m * (m + 1)) * (P (m, x)))) = 0))))
  : (forall (m : ℕ) (x : ℝ), (((m ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) → (((((1 - (x ^ (2 : ℕ))) * (iteratedDeriv 2 (fun t => (P (m, t))) x)) - ((2 * x) * (iteratedDeriv 1 (fun t => (P (m, t))) x))) + ((m * (m + 1)) * (P (m, x)))) = 0))) := by
  sorry

theorem proof_gap_exercise_1227_7
  (P : (ℕ × ℝ -> ℝ))
  (h1 : (forall (m : ℕ) (x : ℝ), (((m ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) → ((P (m, x)) = ((1 /. (((2 : ℕ) ^ m) * (m)!)) * (iteratedDeriv m (fun t => (((t ^ (2 : ℕ)) - 1) ^ m)) x))))))
  (h2 : (exists (y : (ℝ -> ℝ)), (forall (m : ℕ), ((m ∈ (Set.univ : Set ℕ)) → (y = (fun (x : ℝ) => (((x ^ (2 : ℕ)) - 1) ^ m)))))))
  (h3 : (forall (y : (ℝ -> ℝ)) (m : ℕ) (x : ℝ), (((m ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => y t) x) = (((2 * m) * x) * (((x ^ (2 : ℕ)) - 1) ^ (m - 1)))))))
  (h4 : (forall (y : (ℝ -> ℝ)) (m : ℕ) (x : ℝ), (((m ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) → ((((x ^ (2 : ℕ)) - 1) * (iteratedDeriv 1 (fun t => y t) x)) = (((2 * m) * x) * (y x))))))
  (h5 : (forall (y : (ℝ -> ℝ)) (m : ℕ) (x : ℝ), (((m ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) → ((((((x ^ (2 : ℕ)) - 1) * (iteratedDeriv (m + 2) (fun t => y t) x)) + (((2 * (m + 1)) * x) * (iteratedDeriv (m + 1) (fun t => y t) x))) + ((m * (m + 1)) * (iteratedDeriv m (fun t => y t) x))) = ((((2 * m) * x) * (iteratedDeriv (m + 1) (fun t => y t) x)) + (((2 * m) * (m + 1)) * (iteratedDeriv m (fun t => y t) x)))))))
  (h6 : (forall (y : (ℝ -> ℝ)) (m : ℕ) (x : ℝ), (((m ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) → ((((((x ^ (2 : ℕ)) - 1) * (iteratedDeriv (m + 2) (fun t => y t) x)) + ((2 * x) * (iteratedDeriv (m + 1) (fun t => y t) x))) - ((m * (m + 1)) * (iteratedDeriv m (fun t => y t) x))) = 0))))
  (h7 : (forall (m : ℕ) (x : ℝ), (((m ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) → ((((((x ^ (2 : ℕ)) - 1) * (iteratedDeriv 2 (fun t => (P (m, t))) x)) + ((2 * x) * (iteratedDeriv 1 (fun t => (P (m, t))) x))) - ((m * (m + 1)) * (P (m, x)))) = 0))))
  (h8 : (forall (m : ℕ) (x : ℝ), (((m ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) → (((((1 - (x ^ (2 : ℕ))) * (iteratedDeriv 2 (fun t => (P (m, t))) x)) - ((2 * x) * (iteratedDeriv 1 (fun t => (P (m, t))) x))) + ((m * (m + 1)) * (P (m, x)))) = 0))))
  : (forall (m : ℕ) (x : ℝ), (((m ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) → (((((1 - (x ^ (2 : ℕ))) * (iteratedDeriv 2 (fun t => (P (m, t))) x)) - ((2 * x) * (iteratedDeriv 1 (fun t => (P (m, t))) x))) + ((m * (m + 1)) * (P (m, x)))) = 0))) := by
  sorry

theorem proof_gap_exercise_1227_8
  (P : (ℕ × ℝ -> ℝ))
  (h1 : (forall (m : ℕ) (x : ℝ), (((m ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) → ((P (m, x)) = ((1 /. (((2 : ℕ) ^ m) * (m)!)) * (iteratedDeriv m (fun t => (((t ^ (2 : ℕ)) - 1) ^ m)) x))))))
  (h2 : (exists (y : (ℝ -> ℝ)), (forall (m : ℕ), ((m ∈ (Set.univ : Set ℕ)) → (y = (fun (x : ℝ) => (((x ^ (2 : ℕ)) - 1) ^ m)))))))
  (h3 : (forall (y : (ℝ -> ℝ)) (m : ℕ) (x : ℝ), (((m ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => y t) x) = (((2 * m) * x) * (((x ^ (2 : ℕ)) - 1) ^ (m - 1)))))))
  (h4 : (forall (y : (ℝ -> ℝ)) (m : ℕ) (x : ℝ), (((m ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) → ((((x ^ (2 : ℕ)) - 1) * (iteratedDeriv 1 (fun t => y t) x)) = (((2 * m) * x) * (y x))))))
  (h5 : (forall (y : (ℝ -> ℝ)) (m : ℕ) (x : ℝ), (((m ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) → ((((((x ^ (2 : ℕ)) - 1) * (iteratedDeriv (m + 2) (fun t => y t) x)) + (((2 * (m + 1)) * x) * (iteratedDeriv (m + 1) (fun t => y t) x))) + ((m * (m + 1)) * (iteratedDeriv m (fun t => y t) x))) = ((((2 * m) * x) * (iteratedDeriv (m + 1) (fun t => y t) x)) + (((2 * m) * (m + 1)) * (iteratedDeriv m (fun t => y t) x)))))))
  (h6 : (forall (y : (ℝ -> ℝ)) (m : ℕ) (x : ℝ), (((m ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) → ((((((x ^ (2 : ℕ)) - 1) * (iteratedDeriv (m + 2) (fun t => y t) x)) + ((2 * x) * (iteratedDeriv (m + 1) (fun t => y t) x))) - ((m * (m + 1)) * (iteratedDeriv m (fun t => y t) x))) = 0))))
  (h7 : (forall (m : ℕ) (x : ℝ), (((m ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) → ((((((x ^ (2 : ℕ)) - 1) * (iteratedDeriv 2 (fun t => (P (m, t))) x)) + ((2 * x) * (iteratedDeriv 1 (fun t => (P (m, t))) x))) - ((m * (m + 1)) * (P (m, x)))) = 0))))
  (h8 : (forall (m : ℕ) (x : ℝ), (((m ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) → (((((1 - (x ^ (2 : ℕ))) * (iteratedDeriv 2 (fun t => (P (m, t))) x)) - ((2 * x) * (iteratedDeriv 1 (fun t => (P (m, t))) x))) + ((m * (m + 1)) * (P (m, x)))) = 0))))
  (h9 : (forall (m : ℕ) (x : ℝ), (((m ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) → (((((1 - (x ^ (2 : ℕ))) * (iteratedDeriv 2 (fun t => (P (m, t))) x)) - ((2 * x) * (iteratedDeriv 1 (fun t => (P (m, t))) x))) + ((m * (m + 1)) * (P (m, x)))) = 0))))
  : (forall (m : ℕ) (x : ℝ), (((m ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) → (((((1 - (x ^ (2 : ℕ))) * (iteratedDeriv 2 (fun t => (P (m, t))) x)) - ((2 * x) * (iteratedDeriv 1 (fun t => (P (m, t))) x))) + ((m * (m + 1)) * (P (m, x)))) = 0))) := by
  sorry

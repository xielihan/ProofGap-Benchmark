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

-- exercise: exercise_2914

theorem proof_gap_exercise_2914_1
  (y : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((x ^ (4 * n_1)) /. ((4 * n_1))!) else 0)))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((x ^ (4 * n_1)) /. ((4 * n_1))!) else 0)))) := by
  sorry

theorem proof_gap_exercise_2914_2
  (y : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((x ^ (4 * n_1)) /. ((4 * n_1))!) else 0)))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((x ^ (4 * n_1)) /. ((4 * n_1))!) else 0)))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then ((x ^ ((4 * n_1) - 1)) /. (((4 * n_1) - 1))!) else 0)))) := by
  sorry

theorem proof_gap_exercise_2914_3
  (y : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((x ^ (4 * n_1)) /. ((4 * n_1))!) else 0)))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((x ^ (4 * n_1)) /. ((4 * n_1))!) else 0)))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then ((x ^ ((4 * n_1) - 1)) /. (((4 * n_1) - 1))!) else 0)))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => y t) x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then ((x ^ ((4 * n_1) - 2)) /. (((4 * n_1) - 2))!) else 0)))) := by
  sorry

theorem proof_gap_exercise_2914_4
  (y : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((x ^ (4 * n_1)) /. ((4 * n_1))!) else 0)))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((x ^ (4 * n_1)) /. ((4 * n_1))!) else 0)))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then ((x ^ ((4 * n_1) - 1)) /. (((4 * n_1) - 1))!) else 0)))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => y t) x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then ((x ^ ((4 * n_1) - 2)) /. (((4 * n_1) - 2))!) else 0)))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 3 (fun t => y t) x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then ((x ^ ((4 * n_1) - 3)) /. (((4 * n_1) - 3))!) else 0)))) := by
  sorry

theorem proof_gap_exercise_2914_5
  (y : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((x ^ (4 * n_1)) /. ((4 * n_1))!) else 0)))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((x ^ (4 * n_1)) /. ((4 * n_1))!) else 0)))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then ((x ^ ((4 * n_1) - 1)) /. (((4 * n_1) - 1))!) else 0)))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => y t) x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then ((x ^ ((4 * n_1) - 2)) /. (((4 * n_1) - 2))!) else 0)))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 3 (fun t => y t) x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then ((x ^ ((4 * n_1) - 3)) /. (((4 * n_1) - 3))!) else 0)))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 4 (fun t => y t) x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then ((x ^ ((4 * n_1) - 4)) /. (((4 * n_1) - 4))!) else 0)))) := by
  sorry

theorem proof_gap_exercise_2914_6
  (y : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((x ^ (4 * n_1)) /. ((4 * n_1))!) else 0)))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((x ^ (4 * n_1)) /. ((4 * n_1))!) else 0)))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then ((x ^ ((4 * n_1) - 1)) /. (((4 * n_1) - 1))!) else 0)))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => y t) x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then ((x ^ ((4 * n_1) - 2)) /. (((4 * n_1) - 2))!) else 0)))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 3 (fun t => y t) x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then ((x ^ ((4 * n_1) - 3)) /. (((4 * n_1) - 3))!) else 0)))))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 4 (fun t => y t) x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then ((x ^ ((4 * n_1) - 4)) /. (((4 * n_1) - 4))!) else 0)))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((∑' n_1, if (1 : ℕ) ≤ n_1 then ((x ^ ((4 * n_1) - 4)) /. (((4 * n_1) - 4))!) else 0) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((x ^ (4 * n_1)) /. ((4 * n_1))!) else 0)))) := by
  sorry

theorem proof_gap_exercise_2914_7
  (y : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((x ^ (4 * n_1)) /. ((4 * n_1))!) else 0)))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((x ^ (4 * n_1)) /. ((4 * n_1))!) else 0)))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then ((x ^ ((4 * n_1) - 1)) /. (((4 * n_1) - 1))!) else 0)))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => y t) x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then ((x ^ ((4 * n_1) - 2)) /. (((4 * n_1) - 2))!) else 0)))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 3 (fun t => y t) x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then ((x ^ ((4 * n_1) - 3)) /. (((4 * n_1) - 3))!) else 0)))))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 4 (fun t => y t) x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then ((x ^ ((4 * n_1) - 4)) /. (((4 * n_1) - 4))!) else 0)))))
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((∑' n_1, if (1 : ℕ) ≤ n_1 then ((x ^ ((4 * n_1) - 4)) /. (((4 * n_1) - 4))!) else 0) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((x ^ (4 * n_1)) /. ((4 * n_1))!) else 0)))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 4 (fun t => y t) x) = (y x)))) := by
  sorry

theorem proof_gap_exercise_2914_8
  (y : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((x ^ (4 * n_1)) /. ((4 * n_1))!) else 0)))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((x ^ (4 * n_1)) /. ((4 * n_1))!) else 0)))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then ((x ^ ((4 * n_1) - 1)) /. (((4 * n_1) - 1))!) else 0)))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => y t) x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then ((x ^ ((4 * n_1) - 2)) /. (((4 * n_1) - 2))!) else 0)))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 3 (fun t => y t) x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then ((x ^ ((4 * n_1) - 3)) /. (((4 * n_1) - 3))!) else 0)))))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 4 (fun t => y t) x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then ((x ^ ((4 * n_1) - 4)) /. (((4 * n_1) - 4))!) else 0)))))
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((∑' n_1, if (1 : ℕ) ≤ n_1 then ((x ^ ((4 * n_1) - 4)) /. (((4 * n_1) - 4))!) else 0) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((x ^ (4 * n_1)) /. ((4 * n_1))!) else 0)))))
  (h9 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 4 (fun t => y t) x) = (y x)))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 4 (fun t => y t) x) = (y x)))) := by
  sorry

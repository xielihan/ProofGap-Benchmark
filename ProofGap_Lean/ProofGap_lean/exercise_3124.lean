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

-- exercise: exercise_3124

theorem proof_gap_exercise_3124_1
  (P : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (P (0 : ℝ)) = 0)
  (h4 : (P (30 : ℝ)) = (1 /. 2))
  (h5 : (P (90 : ℝ)) = 1)
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 90)) → ((P x) = ((a * x) + (b * (x ^ (3 : ℕ))))))))
  : ((30 * a) + (27000 * b)) = (1 /. 2) := by
  sorry

theorem proof_gap_exercise_3124_2
  (P : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (P (0 : ℝ)) = 0)
  (h4 : (P (30 : ℝ)) = (1 /. 2))
  (h5 : (P (90 : ℝ)) = 1)
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 90)) → ((P x) = ((a * x) + (b * (x ^ (3 : ℕ))))))))
  (h7 : ((30 * a) + (27000 * b)) = (1 /. 2))
  : ((90 * a) + (729000 * b)) = 1 := by
  sorry

theorem proof_gap_exercise_3124_3
  (P : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (P (0 : ℝ)) = 0)
  (h4 : (P (30 : ℝ)) = (1 /. 2))
  (h5 : (P (90 : ℝ)) = 1)
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 90)) → ((P x) = ((a * x) + (b * (x ^ (3 : ℕ))))))))
  (h7 : ((30 * a) + (27000 * b)) = (1 /. 2))
  (h8 : ((90 * a) + (729000 * b)) = 1)
  : a = (5 /. 288) := by
  sorry

theorem proof_gap_exercise_3124_4
  (P : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (P (0 : ℝ)) = 0)
  (h4 : (P (30 : ℝ)) = (1 /. 2))
  (h5 : (P (90 : ℝ)) = 1)
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 90)) → ((P x) = ((a * x) + (b * (x ^ (3 : ℕ))))))))
  (h7 : ((30 * a) + (27000 * b)) = (1 /. 2))
  (h8 : ((90 * a) + (729000 * b)) = 1)
  (h9 : a = (5 /. 288))
  : b = ((-(5 /. 288)) * ((1 /. 150) ^ (2 : ℕ))) := by
  sorry

theorem proof_gap_exercise_3124_5
  (P : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (P (0 : ℝ)) = 0)
  (h4 : (P (30 : ℝ)) = (1 /. 2))
  (h5 : (P (90 : ℝ)) = 1)
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 90)) → ((P x) = ((a * x) + (b * (x ^ (3 : ℕ))))))))
  (h7 : ((30 * a) + (27000 * b)) = (1 /. 2))
  (h8 : ((90 * a) + (729000 * b)) = 1)
  (h9 : a = (5 /. 288))
  (h10 : b = ((-(5 /. 288)) * ((1 /. 150) ^ (2 : ℕ))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 90)) → ((P x) = (((5 * x) /. 288) * (1 - ((x /. 150) ^ (2 : ℕ))))))) := by
  sorry

theorem proof_gap_exercise_3124_6
  (P : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (P (0 : ℝ)) = 0)
  (h4 : (P (30 : ℝ)) = (1 /. 2))
  (h5 : (P (90 : ℝ)) = 1)
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 90)) → ((P x) = ((a * x) + (b * (x ^ (3 : ℕ))))))))
  (h7 : ((30 * a) + (27000 * b)) = (1 /. 2))
  (h8 : ((90 * a) + (729000 * b)) = 1)
  (h9 : a = (5 /. 288))
  (h10 : b = ((-(5 /. 288)) * ((1 /. 150) ^ (2 : ℕ))))
  (h11 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 90)) → ((P x) = (((5 * x) /. 288) * (1 - ((x /. 150) ^ (2 : ℕ))))))))
  : (P (20 : ℝ)) = (((0341 : ℝ) /. (1000 : ℝ))) := by
  sorry

theorem proof_gap_exercise_3124_7
  (P : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (P (0 : ℝ)) = 0)
  (h4 : (P (30 : ℝ)) = (1 /. 2))
  (h5 : (P (90 : ℝ)) = 1)
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 90)) → ((P x) = ((a * x) + (b * (x ^ (3 : ℕ))))))))
  (h7 : ((30 * a) + (27000 * b)) = (1 /. 2))
  (h8 : ((90 * a) + (729000 * b)) = 1)
  (h9 : a = (5 /. 288))
  (h10 : b = ((-(5 /. 288)) * ((1 /. 150) ^ (2 : ℕ))))
  (h11 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 90)) → ((P x) = (((5 * x) /. 288) * (1 - ((x /. 150) ^ (2 : ℕ))))))))
  (h12 : (P (20 : ℝ)) = (((0341 : ℝ) /. (1000 : ℝ))))
  : (P (40 : ℝ)) = (((0645 : ℝ) /. (1000 : ℝ))) := by
  sorry

theorem proof_gap_exercise_3124_8
  (P : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (P (0 : ℝ)) = 0)
  (h4 : (P (30 : ℝ)) = (1 /. 2))
  (h5 : (P (90 : ℝ)) = 1)
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 90)) → ((P x) = ((a * x) + (b * (x ^ (3 : ℕ))))))))
  (h7 : ((30 * a) + (27000 * b)) = (1 /. 2))
  (h8 : ((90 * a) + (729000 * b)) = 1)
  (h9 : a = (5 /. 288))
  (h10 : b = ((-(5 /. 288)) * ((1 /. 150) ^ (2 : ℕ))))
  (h11 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 90)) → ((P x) = (((5 * x) /. 288) * (1 - ((x /. 150) ^ (2 : ℕ))))))))
  (h12 : (P (20 : ℝ)) = (((0341 : ℝ) /. (1000 : ℝ))))
  (h13 : (P (40 : ℝ)) = (((0645 : ℝ) /. (1000 : ℝ))))
  : (P (80 : ℝ)) = (((0994 : ℝ) /. (1000 : ℝ))) := by
  sorry

theorem proof_gap_exercise_3124_9
  (P : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (P (0 : ℝ)) = 0)
  (h4 : (P (30 : ℝ)) = (1 /. 2))
  (h5 : (P (90 : ℝ)) = 1)
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 90)) → ((P x) = ((a * x) + (b * (x ^ (3 : ℕ))))))))
  (h7 : ((30 * a) + (27000 * b)) = (1 /. 2))
  (h8 : ((90 * a) + (729000 * b)) = 1)
  (h9 : a = (5 /. 288))
  (h10 : b = ((-(5 /. 288)) * ((1 /. 150) ^ (2 : ℕ))))
  (h11 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 90)) → ((P x) = (((5 * x) /. 288) * (1 - ((x /. 150) ^ (2 : ℕ))))))))
  (h12 : (P (20 : ℝ)) = (((0341 : ℝ) /. (1000 : ℝ))))
  (h13 : (P (40 : ℝ)) = (((0645 : ℝ) /. (1000 : ℝ))))
  (h14 : (P (80 : ℝ)) = (((0994 : ℝ) /. (1000 : ℝ))))
  : ((P (20 : ℝ)), (P (40 : ℝ)), (P (80 : ℝ))) = ((((0341 : ℝ) /. (1000 : ℝ))), (((0645 : ℝ) /. (1000 : ℝ))), (((0994 : ℝ) /. (1000 : ℝ)))) := by
  sorry

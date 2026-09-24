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

-- exercise: exercise_3044

theorem proof_gap_exercise_3044_1
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((1 /. (Real.rpow x x)) = (Real.exp ((-x) * (Real.log x)))))) := by
  sorry

theorem proof_gap_exercise_3044_2
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((1 /. (Real.rpow x x)) = (Real.exp ((-x) * (Real.log x)))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((Real.exp ((-x) * (Real.log x))) = (∑' n, if (0 : ℕ) ≤ n then (((((-(1 : ℤ)) ^ n) * (x ^ n)) * ((Real.log x) ^ n)) /. (n)!) else 0)))) := by
  sorry

theorem proof_gap_exercise_3044_3
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((1 /. (Real.rpow x x)) = (Real.exp ((-x) * (Real.log x)))))))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((Real.exp ((-x) * (Real.log x))) = (∑' n, if (0 : ℕ) ≤ n then (((((-(1 : ℤ)) ^ n) * (x ^ n)) * ((Real.log x) ^ n)) /. (n)!) else 0)))))
  : (∫ x in (0 : ℝ)..(1 : ℝ), (((1 : ℝ) /. (Real.rpow x x)) * (1 : ℝ))) = (∫ x in (0 : ℝ)..(1 : ℝ), ((Real.exp ((-x) * (Real.log x))) * (1 : ℝ))) := by
  sorry

theorem proof_gap_exercise_3044_4
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((1 /. (Real.rpow x x)) = (Real.exp ((-x) * (Real.log x)))))))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((Real.exp ((-x) * (Real.log x))) = (∑' n, if (0 : ℕ) ≤ n then (((((-(1 : ℤ)) ^ n) * (x ^ n)) * ((Real.log x) ^ n)) /. (n)!) else 0)))))
  (h3 : (∫ x in (0 : ℝ)..(1 : ℝ), (((1 : ℝ) /. (Real.rpow x x)) * (1 : ℝ))) = (∫ x in (0 : ℝ)..(1 : ℝ), ((Real.exp ((-x) * (Real.log x))) * (1 : ℝ))))
  : (∫ x in (0 : ℝ)..(1 : ℝ), ((Real.exp ((-x) * (Real.log x))) * (1 : ℝ))) = (∫ x in (0 : ℝ)..(1 : ℝ), ((∑' n, if (0 : ℕ) ≤ n then (((((-(1 : ℤ)) ^ n) * (x ^ n)) * ((Real.log x) ^ n)) /. (n)!) else 0) * (1 : ℝ))) := by
  sorry

theorem proof_gap_exercise_3044_5
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((1 /. (Real.rpow x x)) = (Real.exp ((-x) * (Real.log x)))))))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((Real.exp ((-x) * (Real.log x))) = (∑' n, if (0 : ℕ) ≤ n then (((((-(1 : ℤ)) ^ n) * (x ^ n)) * ((Real.log x) ^ n)) /. (n)!) else 0)))))
  (h3 : (∫ x in (0 : ℝ)..(1 : ℝ), (((1 : ℝ) /. (Real.rpow x x)) * (1 : ℝ))) = (∫ x in (0 : ℝ)..(1 : ℝ), ((Real.exp ((-x) * (Real.log x))) * (1 : ℝ))))
  (h4 : (∫ x in (0 : ℝ)..(1 : ℝ), ((Real.exp ((-x) * (Real.log x))) * (1 : ℝ))) = (∫ x in (0 : ℝ)..(1 : ℝ), ((∑' n, if (0 : ℕ) ≤ n then (((((-(1 : ℤ)) ^ n) * (x ^ n)) * ((Real.log x) ^ n)) /. (n)!) else 0) * (1 : ℝ))))
  : (∫ x in (0 : ℝ)..(1 : ℝ), ((∑' n, if (0 : ℕ) ≤ n then (((((-(1 : ℤ)) ^ n) * (x ^ n)) * ((Real.log x) ^ n)) /. (n)!) else 0) * (1 : ℝ))) = (∑' n, if (0 : ℕ) ≤ n then (∫ x in (0 : ℝ)..(1 : ℝ), ((((((-(1 : ℝ)) ^ n) * (x ^ n)) * ((Real.log x) ^ n)) /. ((n)! : ℝ)) * (1 : ℝ))) else 0) := by
  sorry

theorem proof_gap_exercise_3044_6
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((1 /. (Real.rpow x x)) = (Real.exp ((-x) * (Real.log x)))))))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((Real.exp ((-x) * (Real.log x))) = (∑' n, if (0 : ℕ) ≤ n then (((((-(1 : ℤ)) ^ n) * (x ^ n)) * ((Real.log x) ^ n)) /. (n)!) else 0)))))
  (h3 : (∫ x in (0 : ℝ)..(1 : ℝ), (((1 : ℝ) /. (Real.rpow x x)) * (1 : ℝ))) = (∫ x in (0 : ℝ)..(1 : ℝ), ((Real.exp ((-x) * (Real.log x))) * (1 : ℝ))))
  (h4 : (∫ x in (0 : ℝ)..(1 : ℝ), ((Real.exp ((-x) * (Real.log x))) * (1 : ℝ))) = (∫ x in (0 : ℝ)..(1 : ℝ), ((∑' n, if (0 : ℕ) ≤ n then (((((-(1 : ℤ)) ^ n) * (x ^ n)) * ((Real.log x) ^ n)) /. (n)!) else 0) * (1 : ℝ))))
  (h5 : (∫ x in (0 : ℝ)..(1 : ℝ), ((∑' n, if (0 : ℕ) ≤ n then (((((-(1 : ℤ)) ^ n) * (x ^ n)) * ((Real.log x) ^ n)) /. (n)!) else 0) * (1 : ℝ))) = (∑' n, if (0 : ℕ) ≤ n then (∫ x in (0 : ℝ)..(1 : ℝ), ((((((-(1 : ℝ)) ^ n) * (x ^ n)) * ((Real.log x) ^ n)) /. ((n)! : ℝ)) * (1 : ℝ))) else 0))
  : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((∫ x in (0 : ℝ)..(1 : ℝ), ((((((-(1 : ℝ)) ^ n) * (x ^ n)) * ((Real.log x) ^ n)) /. ((n)! : ℝ)) * (1 : ℝ))) = (1 /. ((n + 1) ^ (n + 1)))))) := by
  sorry

theorem proof_gap_exercise_3044_7
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((1 /. (Real.rpow x x)) = (Real.exp ((-x) * (Real.log x)))))))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((Real.exp ((-x) * (Real.log x))) = (∑' n, if (0 : ℕ) ≤ n then (((((-(1 : ℤ)) ^ n) * (x ^ n)) * ((Real.log x) ^ n)) /. (n)!) else 0)))))
  (h3 : (∫ x in (0 : ℝ)..(1 : ℝ), (((1 : ℝ) /. (Real.rpow x x)) * (1 : ℝ))) = (∫ x in (0 : ℝ)..(1 : ℝ), ((Real.exp ((-x) * (Real.log x))) * (1 : ℝ))))
  (h4 : (∫ x in (0 : ℝ)..(1 : ℝ), ((Real.exp ((-x) * (Real.log x))) * (1 : ℝ))) = (∫ x in (0 : ℝ)..(1 : ℝ), ((∑' n, if (0 : ℕ) ≤ n then (((((-(1 : ℤ)) ^ n) * (x ^ n)) * ((Real.log x) ^ n)) /. (n)!) else 0) * (1 : ℝ))))
  (h5 : (∫ x in (0 : ℝ)..(1 : ℝ), ((∑' n, if (0 : ℕ) ≤ n then (((((-(1 : ℤ)) ^ n) * (x ^ n)) * ((Real.log x) ^ n)) /. (n)!) else 0) * (1 : ℝ))) = (∑' n, if (0 : ℕ) ≤ n then (∫ x in (0 : ℝ)..(1 : ℝ), ((((((-(1 : ℝ)) ^ n) * (x ^ n)) * ((Real.log x) ^ n)) /. ((n)! : ℝ)) * (1 : ℝ))) else 0))
  (h6 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((∫ x in (0 : ℝ)..(1 : ℝ), ((((((-(1 : ℝ)) ^ n) * (x ^ n)) * ((Real.log x) ^ n)) /. ((n)! : ℝ)) * (1 : ℝ))) = (1 /. ((n + 1) ^ (n + 1)))))))
  : (∑' n, if (0 : ℕ) ≤ n then (1 /. ((n + 1) ^ (n + 1))) else 0) = (∑' n, if (1 : ℕ) ≤ n then (1 /. (n ^ n)) else 0) := by
  sorry

theorem proof_gap_exercise_3044_8
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((1 /. (Real.rpow x x)) = (Real.exp ((-x) * (Real.log x)))))))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((Real.exp ((-x) * (Real.log x))) = (∑' n, if (0 : ℕ) ≤ n then (((((-(1 : ℤ)) ^ n) * (x ^ n)) * ((Real.log x) ^ n)) /. (n)!) else 0)))))
  (h3 : (∫ x in (0 : ℝ)..(1 : ℝ), (((1 : ℝ) /. (Real.rpow x x)) * (1 : ℝ))) = (∫ x in (0 : ℝ)..(1 : ℝ), ((Real.exp ((-x) * (Real.log x))) * (1 : ℝ))))
  (h4 : (∫ x in (0 : ℝ)..(1 : ℝ), ((Real.exp ((-x) * (Real.log x))) * (1 : ℝ))) = (∫ x in (0 : ℝ)..(1 : ℝ), ((∑' n, if (0 : ℕ) ≤ n then (((((-(1 : ℤ)) ^ n) * (x ^ n)) * ((Real.log x) ^ n)) /. (n)!) else 0) * (1 : ℝ))))
  (h5 : (∫ x in (0 : ℝ)..(1 : ℝ), ((∑' n, if (0 : ℕ) ≤ n then (((((-(1 : ℤ)) ^ n) * (x ^ n)) * ((Real.log x) ^ n)) /. (n)!) else 0) * (1 : ℝ))) = (∑' n, if (0 : ℕ) ≤ n then (∫ x in (0 : ℝ)..(1 : ℝ), ((((((-(1 : ℝ)) ^ n) * (x ^ n)) * ((Real.log x) ^ n)) /. ((n)! : ℝ)) * (1 : ℝ))) else 0))
  (h6 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((∫ x in (0 : ℝ)..(1 : ℝ), ((((((-(1 : ℝ)) ^ n) * (x ^ n)) * ((Real.log x) ^ n)) /. ((n)! : ℝ)) * (1 : ℝ))) = (1 /. ((n + 1) ^ (n + 1)))))))
  (h7 : (∑' n, if (0 : ℕ) ≤ n then (1 /. ((n + 1) ^ (n + 1))) else 0) = (∑' n, if (1 : ℕ) ≤ n then (1 /. (n ^ n)) else 0))
  : (∫ x in (0 : ℝ)..(1 : ℝ), (((1 : ℝ) /. (Real.rpow x x)) * (1 : ℝ))) = (∑' n, if (1 : ℕ) ≤ n then (1 /. (n ^ n)) else 0) := by
  sorry

theorem proof_gap_exercise_3044_9
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((1 /. (Real.rpow x x)) = (Real.exp ((-x) * (Real.log x)))))))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((Real.exp ((-x) * (Real.log x))) = (∑' n, if (0 : ℕ) ≤ n then (((((-(1 : ℤ)) ^ n) * (x ^ n)) * ((Real.log x) ^ n)) /. (n)!) else 0)))))
  (h3 : (∫ x in (0 : ℝ)..(1 : ℝ), (((1 : ℝ) /. (Real.rpow x x)) * (1 : ℝ))) = (∫ x in (0 : ℝ)..(1 : ℝ), ((Real.exp ((-x) * (Real.log x))) * (1 : ℝ))))
  (h4 : (∫ x in (0 : ℝ)..(1 : ℝ), ((Real.exp ((-x) * (Real.log x))) * (1 : ℝ))) = (∫ x in (0 : ℝ)..(1 : ℝ), ((∑' n, if (0 : ℕ) ≤ n then (((((-(1 : ℤ)) ^ n) * (x ^ n)) * ((Real.log x) ^ n)) /. (n)!) else 0) * (1 : ℝ))))
  (h5 : (∫ x in (0 : ℝ)..(1 : ℝ), ((∑' n, if (0 : ℕ) ≤ n then (((((-(1 : ℤ)) ^ n) * (x ^ n)) * ((Real.log x) ^ n)) /. (n)!) else 0) * (1 : ℝ))) = (∑' n, if (0 : ℕ) ≤ n then (∫ x in (0 : ℝ)..(1 : ℝ), ((((((-(1 : ℝ)) ^ n) * (x ^ n)) * ((Real.log x) ^ n)) /. ((n)! : ℝ)) * (1 : ℝ))) else 0))
  (h6 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((∫ x in (0 : ℝ)..(1 : ℝ), ((((((-(1 : ℝ)) ^ n) * (x ^ n)) * ((Real.log x) ^ n)) /. ((n)! : ℝ)) * (1 : ℝ))) = (1 /. ((n + 1) ^ (n + 1)))))))
  (h7 : (∑' n, if (0 : ℕ) ≤ n then (1 /. ((n + 1) ^ (n + 1))) else 0) = (∑' n, if (1 : ℕ) ≤ n then (1 /. (n ^ n)) else 0))
  (h8 : (∫ x in (0 : ℝ)..(1 : ℝ), (((1 : ℝ) /. (Real.rpow x x)) * (1 : ℝ))) = (∑' n, if (1 : ℕ) ≤ n then (1 /. (n ^ n)) else 0))
  : (∫ x in (0 : ℝ)..(1 : ℝ), (((1 : ℝ) /. (Real.rpow x x)) * (1 : ℝ))) = (∑' n, if (1 : ℕ) ≤ n then (1 /. (n ^ n)) else 0) := by
  sorry

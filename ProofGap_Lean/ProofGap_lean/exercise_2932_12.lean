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

-- exercise: exercise_2932_12

theorem proof_gap_exercise_2932_12_1
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((Real.rpow x x) = (Real.exp (x * (Real.log x)))))) := by
  sorry

theorem proof_gap_exercise_2932_12_2
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((Real.rpow x x) = (Real.exp (x * (Real.log x)))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((Real.exp (x * (Real.log x))) = (∑' n, if (0 : ℕ) ≤ n then (((x * (Real.log x)) ^ n) /. (n)!) else 0)))) := by
  sorry

theorem proof_gap_exercise_2932_12_3
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((Real.rpow x x) = (Real.exp (x * (Real.log x)))))))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((Real.exp (x * (Real.log x))) = (∑' n, if (0 : ℕ) ≤ n then (((x * (Real.log x)) ^ n) /. (n)!) else 0)))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((Real.rpow x x) = (∑' n, if (0 : ℕ) ≤ n then (((x * (Real.log x)) ^ n) /. (n)!) else 0)))) := by
  sorry

theorem proof_gap_exercise_2932_12_4
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((Real.rpow x x) = (Real.exp (x * (Real.log x)))))))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((Real.exp (x * (Real.log x))) = (∑' n, if (0 : ℕ) ≤ n then (((x * (Real.log x)) ^ n) /. (n)!) else 0)))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((Real.rpow x x) = (∑' n, if (0 : ℕ) ≤ n then (((x * (Real.log x)) ^ n) /. (n)!) else 0)))))
  : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((∫ x in (0 : ℝ)..(1 : ℝ), (((x ^ n) * ((Real.log x) ^ n)) * (1 : ℝ))) = (((-(1 : ℤ)) ^ n) * ((n)! /. ((n + 1) ^ (n + 1))))))) := by
  sorry

theorem proof_gap_exercise_2932_12_5
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((Real.rpow x x) = (Real.exp (x * (Real.log x)))))))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((Real.exp (x * (Real.log x))) = (∑' n, if (0 : ℕ) ≤ n then (((x * (Real.log x)) ^ n) /. (n)!) else 0)))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((Real.rpow x x) = (∑' n, if (0 : ℕ) ≤ n then (((x * (Real.log x)) ^ n) /. (n)!) else 0)))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((∫ x in (0 : ℝ)..(1 : ℝ), (((x ^ n) * ((Real.log x) ^ n)) * (1 : ℝ))) = (((-(1 : ℤ)) ^ n) * ((n)! /. ((n + 1) ^ (n + 1))))))))
  : (∫ x in (0 : ℝ)..(1 : ℝ), ((Real.rpow x x) * (1 : ℝ))) = (∑' n, if (0 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) /. ((n + 1) ^ (n + 1))) else 0) := by
  sorry

theorem proof_gap_exercise_2932_12_6
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((Real.rpow x x) = (Real.exp (x * (Real.log x)))))))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((Real.exp (x * (Real.log x))) = (∑' n, if (0 : ℕ) ≤ n then (((x * (Real.log x)) ^ n) /. (n)!) else 0)))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((Real.rpow x x) = (∑' n, if (0 : ℕ) ≤ n then (((x * (Real.log x)) ^ n) /. (n)!) else 0)))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((∫ x in (0 : ℝ)..(1 : ℝ), (((x ^ n) * ((Real.log x) ^ n)) * (1 : ℝ))) = (((-(1 : ℤ)) ^ n) * ((n)! /. ((n + 1) ^ (n + 1))))))))
  (h5 : (∫ x in (0 : ℝ)..(1 : ℝ), ((Real.rpow x x) * (1 : ℝ))) = (∑' n, if (0 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) /. ((n + 1) ^ (n + 1))) else 0))
  : (exists (v_uCE_u94 : ℝ), ((v_uCE_u94 ∈ (Set.univ : Set ℝ)) ∧ ((∫ x in (0 : ℝ)..(1 : ℝ), ((Real.rpow x x) * (1 : ℝ))) = ((((1 - (1 /. 4)) + (1 /. 27)) - (1 /. 256)) + v_uCE_u94)))) := by
  sorry

theorem proof_gap_exercise_2932_12_7
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((Real.rpow x x) = (Real.exp (x * (Real.log x)))))))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((Real.exp (x * (Real.log x))) = (∑' n, if (0 : ℕ) ≤ n then (((x * (Real.log x)) ^ n) /. (n)!) else 0)))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((Real.rpow x x) = (∑' n, if (0 : ℕ) ≤ n then (((x * (Real.log x)) ^ n) /. (n)!) else 0)))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((∫ x in (0 : ℝ)..(1 : ℝ), (((x ^ n) * ((Real.log x) ^ n)) * (1 : ℝ))) = (((-(1 : ℤ)) ^ n) * ((n)! /. ((n + 1) ^ (n + 1))))))))
  (h5 : (∫ x in (0 : ℝ)..(1 : ℝ), ((Real.rpow x x) * (1 : ℝ))) = (∑' n, if (0 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) /. ((n + 1) ^ (n + 1))) else 0))
  (h6 : (exists (v_uCE_u94 : ℝ), ((v_uCE_u94 ∈ (Set.univ : Set ℝ)) ∧ ((∫ x in (0 : ℝ)..(1 : ℝ), ((Real.rpow x x) * (1 : ℝ))) = ((((1 - (1 /. 4)) + (1 /. 27)) - (1 /. 256)) + v_uCE_u94)))))
  : (exists (v_uCE_u94 : ℝ), ((v_uCE_u94 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_u94))) := by
  sorry

theorem proof_gap_exercise_2932_12_8
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((Real.rpow x x) = (Real.exp (x * (Real.log x)))))))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((Real.exp (x * (Real.log x))) = (∑' n, if (0 : ℕ) ≤ n then (((x * (Real.log x)) ^ n) /. (n)!) else 0)))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((Real.rpow x x) = (∑' n, if (0 : ℕ) ≤ n then (((x * (Real.log x)) ^ n) /. (n)!) else 0)))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((∫ x in (0 : ℝ)..(1 : ℝ), (((x ^ n) * ((Real.log x) ^ n)) * (1 : ℝ))) = (((-(1 : ℤ)) ^ n) * ((n)! /. ((n + 1) ^ (n + 1))))))))
  (h5 : (∫ x in (0 : ℝ)..(1 : ℝ), ((Real.rpow x x) * (1 : ℝ))) = (∑' n, if (0 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) /. ((n + 1) ^ (n + 1))) else 0))
  (h6 : (exists (v_uCE_u94 : ℝ), ((v_uCE_u94 ∈ (Set.univ : Set ℝ)) ∧ ((∫ x in (0 : ℝ)..(1 : ℝ), ((Real.rpow x x) * (1 : ℝ))) = ((((1 - (1 /. 4)) + (1 /. 27)) - (1 /. 256)) + v_uCE_u94)))))
  (h7 : (exists (v_uCE_u94 : ℝ), ((v_uCE_u94 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_u94))))
  : (exists (v_uCE_u94 : ℝ), ((v_uCE_u94 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_u94 < (((4 : ℕ))! /. (((4 : ℕ))! * ((4 + 1) ^ (4 + 1))))))) := by
  sorry

theorem proof_gap_exercise_2932_12_9
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((Real.rpow x x) = (Real.exp (x * (Real.log x)))))))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((Real.exp (x * (Real.log x))) = (∑' n, if (0 : ℕ) ≤ n then (((x * (Real.log x)) ^ n) /. (n)!) else 0)))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((Real.rpow x x) = (∑' n, if (0 : ℕ) ≤ n then (((x * (Real.log x)) ^ n) /. (n)!) else 0)))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((∫ x in (0 : ℝ)..(1 : ℝ), (((x ^ n) * ((Real.log x) ^ n)) * (1 : ℝ))) = (((-(1 : ℤ)) ^ n) * ((n)! /. ((n + 1) ^ (n + 1))))))))
  (h5 : (∫ x in (0 : ℝ)..(1 : ℝ), ((Real.rpow x x) * (1 : ℝ))) = (∑' n, if (0 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) /. ((n + 1) ^ (n + 1))) else 0))
  (h6 : (exists (v_uCE_u94 : ℝ), ((v_uCE_u94 ∈ (Set.univ : Set ℝ)) ∧ ((∫ x in (0 : ℝ)..(1 : ℝ), ((Real.rpow x x) * (1 : ℝ))) = ((((1 - (1 /. 4)) + (1 /. 27)) - (1 /. 256)) + v_uCE_u94)))))
  (h7 : (exists (v_uCE_u94 : ℝ), ((v_uCE_u94 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_u94))))
  (h8 : (exists (v_uCE_u94 : ℝ), ((v_uCE_u94 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_u94 < (((4 : ℕ))! /. (((4 : ℕ))! * ((4 + 1) ^ (4 + 1))))))))
  : (((4 : ℕ))! /. (((4 : ℕ))! * ((4 + 1) ^ (4 + 1)))) = (1 /. ((5 : ℕ) ^ (5 : ℕ))) := by
  sorry

theorem proof_gap_exercise_2932_12_10
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((Real.rpow x x) = (Real.exp (x * (Real.log x)))))))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((Real.exp (x * (Real.log x))) = (∑' n, if (0 : ℕ) ≤ n then (((x * (Real.log x)) ^ n) /. (n)!) else 0)))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((Real.rpow x x) = (∑' n, if (0 : ℕ) ≤ n then (((x * (Real.log x)) ^ n) /. (n)!) else 0)))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((∫ x in (0 : ℝ)..(1 : ℝ), (((x ^ n) * ((Real.log x) ^ n)) * (1 : ℝ))) = (((-(1 : ℤ)) ^ n) * ((n)! /. ((n + 1) ^ (n + 1))))))))
  (h5 : (∫ x in (0 : ℝ)..(1 : ℝ), ((Real.rpow x x) * (1 : ℝ))) = (∑' n, if (0 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) /. ((n + 1) ^ (n + 1))) else 0))
  (h6 : (exists (v_uCE_u94 : ℝ), ((v_uCE_u94 ∈ (Set.univ : Set ℝ)) ∧ ((∫ x in (0 : ℝ)..(1 : ℝ), ((Real.rpow x x) * (1 : ℝ))) = ((((1 - (1 /. 4)) + (1 /. 27)) - (1 /. 256)) + v_uCE_u94)))))
  (h7 : (exists (v_uCE_u94 : ℝ), ((v_uCE_u94 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_u94))))
  (h8 : (exists (v_uCE_u94 : ℝ), ((v_uCE_u94 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_u94 < (((4 : ℕ))! /. (((4 : ℕ))! * ((4 + 1) ^ (4 + 1))))))))
  (h9 : (((4 : ℕ))! /. (((4 : ℕ))! * ((4 + 1) ^ (4 + 1)))) = (1 /. ((5 : ℕ) ^ (5 : ℕ))))
  : (1 /. ((5 : ℕ) ^ (5 : ℕ))) < (1 /. ((10 : ℕ) ^ (3 : ℕ))) := by
  sorry

theorem proof_gap_exercise_2932_12_11
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((Real.rpow x x) = (Real.exp (x * (Real.log x)))))))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((Real.exp (x * (Real.log x))) = (∑' n, if (0 : ℕ) ≤ n then (((x * (Real.log x)) ^ n) /. (n)!) else 0)))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((Real.rpow x x) = (∑' n, if (0 : ℕ) ≤ n then (((x * (Real.log x)) ^ n) /. (n)!) else 0)))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((∫ x in (0 : ℝ)..(1 : ℝ), (((x ^ n) * ((Real.log x) ^ n)) * (1 : ℝ))) = (((-(1 : ℤ)) ^ n) * ((n)! /. ((n + 1) ^ (n + 1))))))))
  (h5 : (∫ x in (0 : ℝ)..(1 : ℝ), ((Real.rpow x x) * (1 : ℝ))) = (∑' n, if (0 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) /. ((n + 1) ^ (n + 1))) else 0))
  (h6 : (exists (v_uCE_u94 : ℝ), ((v_uCE_u94 ∈ (Set.univ : Set ℝ)) ∧ ((∫ x in (0 : ℝ)..(1 : ℝ), ((Real.rpow x x) * (1 : ℝ))) = ((((1 - (1 /. 4)) + (1 /. 27)) - (1 /. 256)) + v_uCE_u94)))))
  (h7 : (exists (v_uCE_u94 : ℝ), ((v_uCE_u94 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_u94))))
  (h8 : (exists (v_uCE_u94 : ℝ), ((v_uCE_u94 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_u94 < (((4 : ℕ))! /. (((4 : ℕ))! * ((4 + 1) ^ (4 + 1))))))))
  (h9 : (((4 : ℕ))! /. (((4 : ℕ))! * ((4 + 1) ^ (4 + 1)))) = (1 /. ((5 : ℕ) ^ (5 : ℕ))))
  (h10 : (1 /. ((5 : ℕ) ^ (5 : ℕ))) < (1 /. ((10 : ℕ) ^ (3 : ℕ))))
  : 0 < (1 /. ((10 : ℕ) ^ (3 : ℕ))) := by
  sorry

theorem proof_gap_exercise_2932_12_12
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((Real.rpow x x) = (Real.exp (x * (Real.log x)))))))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((Real.exp (x * (Real.log x))) = (∑' n, if (0 : ℕ) ≤ n then (((x * (Real.log x)) ^ n) /. (n)!) else 0)))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x ≤ 1)) → ((Real.rpow x x) = (∑' n, if (0 : ℕ) ≤ n then (((x * (Real.log x)) ^ n) /. (n)!) else 0)))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((∫ x in (0 : ℝ)..(1 : ℝ), (((x ^ n) * ((Real.log x) ^ n)) * (1 : ℝ))) = (((-(1 : ℤ)) ^ n) * ((n)! /. ((n + 1) ^ (n + 1))))))))
  (h5 : (∫ x in (0 : ℝ)..(1 : ℝ), ((Real.rpow x x) * (1 : ℝ))) = (∑' n, if (0 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) /. ((n + 1) ^ (n + 1))) else 0))
  (h6 : (exists (v_uCE_u94 : ℝ), ((v_uCE_u94 ∈ (Set.univ : Set ℝ)) ∧ ((∫ x in (0 : ℝ)..(1 : ℝ), ((Real.rpow x x) * (1 : ℝ))) = ((((1 - (1 /. 4)) + (1 /. 27)) - (1 /. 256)) + v_uCE_u94)))))
  (h7 : (exists (v_uCE_u94 : ℝ), ((v_uCE_u94 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_u94))))
  (h8 : (exists (v_uCE_u94 : ℝ), ((v_uCE_u94 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_u94 < (((4 : ℕ))! /. (((4 : ℕ))! * ((4 + 1) ^ (4 + 1))))))))
  (h9 : (((4 : ℕ))! /. (((4 : ℕ))! * ((4 + 1) ^ (4 + 1)))) = (1 /. ((5 : ℕ) ^ (5 : ℕ))))
  (h10 : (1 /. ((5 : ℕ) ^ (5 : ℕ))) < (1 /. ((10 : ℕ) ^ (3 : ℕ))))
  (h11 : 0 < (1 /. ((10 : ℕ) ^ (3 : ℕ))))
  : |((∫ x in (0 : ℝ)..(1 : ℝ), ((Real.rpow x x) * (1 : ℝ))) - (((0783 : ℝ) /. (1000 : ℝ))))| ≤ (((0001 : ℝ) /. (1000 : ℝ))) := by
  sorry

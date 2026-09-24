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

-- exercise: exercise_794

theorem proof_gap_exercise_794_1
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((f x) = (x /. (4 - (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((4 - (x ^ (2 : ℕ))) ≠ 0))))
  : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((4 - (x_1 ^ (2 : ℕ))) ≠ 0))))) := by
  sorry

theorem proof_gap_exercise_794_2
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((f x) = (x /. (4 - (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((4 - (x ^ (2 : ℕ))) ≠ 0))))
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((4 - (x_1 ^ (2 : ℕ))) ≠ 0))))))
  : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((4 - (x_2 ^ (2 : ℕ))) ≠ 0))))) := by
  sorry

theorem proof_gap_exercise_794_3
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((f x) = (x /. (4 - (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((4 - (x ^ (2 : ℕ))) ≠ 0))))
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((4 - (x_1 ^ (2 : ℕ))) ≠ 0))))))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((4 - (x_2 ^ (2 : ℕ))) ≠ 0))))))
  : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → (|(((f x_1) - (f x_2)))| = |(((x_1 /. (4 - (x_1 ^ (2 : ℕ)))) - (x_2 /. (4 - (x_2 ^ (2 : ℕ))))))|))))) := by
  sorry

theorem proof_gap_exercise_794_4
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((f x) = (x /. (4 - (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((4 - (x ^ (2 : ℕ))) ≠ 0))))
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((4 - (x_1 ^ (2 : ℕ))) ≠ 0))))))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((4 - (x_2 ^ (2 : ℕ))) ≠ 0))))))
  (h5 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → (|(((f x_1) - (f x_2)))| = |(((x_1 /. (4 - (x_1 ^ (2 : ℕ)))) - (x_2 /. (4 - (x_2 ^ (2 : ℕ))))))|))))))
  : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → (|(((f x_1) - (f x_2)))| = (|(((4 + (x_1 * x_2)) /. ((4 - (x_1 ^ (2 : ℕ))) * (4 - (x_2 ^ (2 : ℕ))))))| * |((x_1 - x_2))|)))))) := by
  sorry

theorem proof_gap_exercise_794_5
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((f x) = (x /. (4 - (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((4 - (x ^ (2 : ℕ))) ≠ 0))))
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((4 - (x_1 ^ (2 : ℕ))) ≠ 0))))))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((4 - (x_2 ^ (2 : ℕ))) ≠ 0))))))
  (h5 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → (|(((f x_1) - (f x_2)))| = |(((x_1 /. (4 - (x_1 ^ (2 : ℕ)))) - (x_2 /. (4 - (x_2 ^ (2 : ℕ))))))|))))))
  (h6 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → (|(((f x_1) - (f x_2)))| = (|(((4 + (x_1 * x_2)) /. ((4 - (x_1 ^ (2 : ℕ))) * (4 - (x_2 ^ (2 : ℕ))))))| * |((x_1 - x_2))|)))))))
  : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → (|(((4 + (x_1 * x_2)) /. ((4 - (x_1 ^ (2 : ℕ))) * (4 - (x_2 ^ (2 : ℕ))))))| < (5 /. 9)))))) := by
  sorry

theorem proof_gap_exercise_794_6
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((f x) = (x /. (4 - (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((4 - (x ^ (2 : ℕ))) ≠ 0))))
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((4 - (x_1 ^ (2 : ℕ))) ≠ 0))))))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((4 - (x_2 ^ (2 : ℕ))) ≠ 0))))))
  (h5 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → (|(((f x_1) - (f x_2)))| = |(((x_1 /. (4 - (x_1 ^ (2 : ℕ)))) - (x_2 /. (4 - (x_2 ^ (2 : ℕ))))))|))))))
  (h6 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → (|(((f x_1) - (f x_2)))| = (|(((4 + (x_1 * x_2)) /. ((4 - (x_1 ^ (2 : ℕ))) * (4 - (x_2 ^ (2 : ℕ))))))| * |((x_1 - x_2))|)))))))
  (h7 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → (|(((4 + (x_1 * x_2)) /. ((4 - (x_1 ^ (2 : ℕ))) * (4 - (x_2 ^ (2 : ℕ))))))| < (5 /. 9)))))))
  : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → (|(((f x_1) - (f x_2)))| < |((x_1 - x_2))|))))) := by
  sorry

theorem proof_gap_exercise_794_7
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((f x) = (x /. (4 - (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((4 - (x ^ (2 : ℕ))) ≠ 0))))
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((4 - (x_1 ^ (2 : ℕ))) ≠ 0))))))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((4 - (x_2 ^ (2 : ℕ))) ≠ 0))))))
  (h5 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → (|(((f x_1) - (f x_2)))| = |(((x_1 /. (4 - (x_1 ^ (2 : ℕ)))) - (x_2 /. (4 - (x_2 ^ (2 : ℕ))))))|))))))
  (h6 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → (|(((f x_1) - (f x_2)))| = (|(((4 + (x_1 * x_2)) /. ((4 - (x_1 ^ (2 : ℕ))) * (4 - (x_2 ^ (2 : ℕ))))))| * |((x_1 - x_2))|)))))))
  (h7 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → (|(((4 + (x_1 * x_2)) /. ((4 - (x_1 ^ (2 : ℕ))) * (4 - (x_2 ^ (2 : ℕ))))))| < (5 /. 9)))))))
  (h8 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → (|(((f x_1) - (f x_2)))| < |((x_1 - x_2))|))))))
  : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4 : ℝ), ((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ ((v_uCE_uB4 = v_uCE_uB5) → (v_uCE_uB4 > 0)))))) := by
  sorry

theorem proof_gap_exercise_794_8
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((f x) = (x /. (4 - (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((4 - (x ^ (2 : ℕ))) ≠ 0))))
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((4 - (x_1 ^ (2 : ℕ))) ≠ 0))))))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((4 - (x_2 ^ (2 : ℕ))) ≠ 0))))))
  (h5 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → (|(((f x_1) - (f x_2)))| = |(((x_1 /. (4 - (x_1 ^ (2 : ℕ)))) - (x_2 /. (4 - (x_2 ^ (2 : ℕ))))))|))))))
  (h6 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → (|(((f x_1) - (f x_2)))| = (|(((4 + (x_1 * x_2)) /. ((4 - (x_1 ^ (2 : ℕ))) * (4 - (x_2 ^ (2 : ℕ))))))| * |((x_1 - x_2))|)))))))
  (h7 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → (|(((4 + (x_1 * x_2)) /. ((4 - (x_1 ^ (2 : ℕ))) * (4 - (x_2 ^ (2 : ℕ))))))| < (5 /. 9)))))))
  (h8 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → (|(((f x_1) - (f x_2)))| < |((x_1 - x_2))|))))))
  (h9 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4 : ℝ), ((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ ((v_uCE_uB4 = v_uCE_uB5) → (v_uCE_uB4 > 0)))))))
  : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4 : ℝ), ((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ ((v_uCE_uB4 = v_uCE_uB5) → (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (|((x_1 - x_2))| < v_uCE_uB4)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → (|(((f x_1) - (f x_2)))| < v_uCE_uB5)))))))))) := by
  sorry

theorem proof_gap_exercise_794_9
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((f x) = (x /. (4 - (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((4 - (x ^ (2 : ℕ))) ≠ 0))))
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((4 - (x_1 ^ (2 : ℕ))) ≠ 0))))))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((4 - (x_2 ^ (2 : ℕ))) ≠ 0))))))
  (h5 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → (|(((f x_1) - (f x_2)))| = |(((x_1 /. (4 - (x_1 ^ (2 : ℕ)))) - (x_2 /. (4 - (x_2 ^ (2 : ℕ))))))|))))))
  (h6 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → (|(((f x_1) - (f x_2)))| = (|(((4 + (x_1 * x_2)) /. ((4 - (x_1 ^ (2 : ℕ))) * (4 - (x_2 ^ (2 : ℕ))))))| * |((x_1 - x_2))|)))))))
  (h7 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → (|(((4 + (x_1 * x_2)) /. ((4 - (x_1 ^ (2 : ℕ))) * (4 - (x_2 ^ (2 : ℕ))))))| < (5 /. 9)))))))
  (h8 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → (|(((f x_1) - (f x_2)))| < |((x_1 - x_2))|))))))
  (h9 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4 : ℝ), ((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ ((v_uCE_uB4 = v_uCE_uB5) → (v_uCE_uB4 > 0)))))))
  (h10 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4 : ℝ), ((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ ((v_uCE_uB4 = v_uCE_uB5) → (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (|((x_1 - x_2))| < v_uCE_uB4)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → (|(((f x_1) - (f x_2)))| < v_uCE_uB5)))))))))))
  : UniformContinuousOn f (Set.Icc (-(1 : ℝ)) 1) := by
  sorry

theorem proof_gap_exercise_794_10
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((f x) = (x /. (4 - (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((4 - (x ^ (2 : ℕ))) ≠ 0))))
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((4 - (x_1 ^ (2 : ℕ))) ≠ 0))))))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((4 - (x_2 ^ (2 : ℕ))) ≠ 0))))))
  (h5 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → (|(((f x_1) - (f x_2)))| = |(((x_1 /. (4 - (x_1 ^ (2 : ℕ)))) - (x_2 /. (4 - (x_2 ^ (2 : ℕ))))))|))))))
  (h6 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → (|(((f x_1) - (f x_2)))| = (|(((4 + (x_1 * x_2)) /. ((4 - (x_1 ^ (2 : ℕ))) * (4 - (x_2 ^ (2 : ℕ))))))| * |((x_1 - x_2))|)))))))
  (h7 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → (|(((4 + (x_1 * x_2)) /. ((4 - (x_1 ^ (2 : ℕ))) * (4 - (x_2 ^ (2 : ℕ))))))| < (5 /. 9)))))))
  (h8 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → (|(((f x_1) - (f x_2)))| < |((x_1 - x_2))|))))))
  (h9 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4 : ℝ), ((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ ((v_uCE_uB4 = v_uCE_uB5) → (v_uCE_uB4 > 0)))))))
  (h10 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4 : ℝ), ((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ ((v_uCE_uB4 = v_uCE_uB5) → (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (|((x_1 - x_2))| < v_uCE_uB4)) ∧ (x_1 ∈ (Set.Icc (-(1 : ℝ)) 1))) ∧ (x_2 ∈ (Set.Icc (-(1 : ℝ)) 1))) → (|(((f x_1) - (f x_2)))| < v_uCE_uB5)))))))))))
  (h11 : UniformContinuousOn f (Set.Icc (-(1 : ℝ)) 1))
  : UniformContinuousOn f (Set.Icc (-(1 : ℝ)) 1) := by
  sorry

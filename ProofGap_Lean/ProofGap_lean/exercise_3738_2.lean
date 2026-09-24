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

-- exercise: exercise_3738_2

theorem proof_gap_exercise_3738_2_1
  (a : ℝ)
  (b : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (b ∈ (Set.univ : Set ℝ)) ∧ (b > 0))
  : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 1))) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((((Real.rpow x b) - (Real.rpow x a)) /. (Real.log x)) = (∫ y in a..b, ((Real.rpow x y) * (1 : ℝ)))))) := by
  sorry

theorem proof_gap_exercise_3738_2_2
  (a : ℝ)
  (b : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (b ∈ (Set.univ : Set ℝ)) ∧ (b > 0))
  (h3 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 1))) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((((Real.rpow x b) - (Real.rpow x a)) /. (Real.log x)) = (∫ y in a..b, ((Real.rpow x y) * (1 : ℝ)))))))
  : (∫ x in (0 : ℝ)..(1 : ℝ), (((Real.cos (Real.log (1 /. x))) * (((Real.rpow x b) - (Real.rpow x a)) /. (Real.log x))) * (1 : ℝ))) = (∫ x in (0 : ℝ)..(1 : ℝ), (((Real.cos (Real.log (1 /. x))) * (∫ y in a..b, ((Real.rpow x y) * (1 : ℝ)))) * (1 : ℝ))) := by
  sorry

theorem proof_gap_exercise_3738_2_3
  (a : ℝ)
  (b : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (b ∈ (Set.univ : Set ℝ)) ∧ (b > 0))
  (h3 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 1))) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((((Real.rpow x b) - (Real.rpow x a)) /. (Real.log x)) = (∫ y in a..b, ((Real.rpow x y) * (1 : ℝ)))))))
  (h4 : (∫ x in (0 : ℝ)..(1 : ℝ), (((Real.cos (Real.log (1 /. x))) * (((Real.rpow x b) - (Real.rpow x a)) /. (Real.log x))) * (1 : ℝ))) = (∫ x in (0 : ℝ)..(1 : ℝ), (((Real.cos (Real.log (1 /. x))) * (∫ y in a..b, ((Real.rpow x y) * (1 : ℝ)))) * (1 : ℝ))))
  : (∫ x in (0 : ℝ)..(1 : ℝ), (((Real.cos (Real.log (1 /. x))) * (∫ y in a..b, ((Real.rpow x y) * (1 : ℝ)))) * (1 : ℝ))) = (∫ y in a..b, ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.cos (Real.log (1 /. x))) * (Real.rpow x y)) * (1 : ℝ))) * (1 : ℝ))) := by
  sorry

theorem proof_gap_exercise_3738_2_4
  (a : ℝ)
  (b : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (b ∈ (Set.univ : Set ℝ)) ∧ (b > 0))
  (h3 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 1))) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((((Real.rpow x b) - (Real.rpow x a)) /. (Real.log x)) = (∫ y in a..b, ((Real.rpow x y) * (1 : ℝ)))))))
  (h4 : (∫ x in (0 : ℝ)..(1 : ℝ), (((Real.cos (Real.log (1 /. x))) * (((Real.rpow x b) - (Real.rpow x a)) /. (Real.log x))) * (1 : ℝ))) = (∫ x in (0 : ℝ)..(1 : ℝ), (((Real.cos (Real.log (1 /. x))) * (∫ y in a..b, ((Real.rpow x y) * (1 : ℝ)))) * (1 : ℝ))))
  (h5 : (∫ x in (0 : ℝ)..(1 : ℝ), (((Real.cos (Real.log (1 /. x))) * (∫ y in a..b, ((Real.rpow x y) * (1 : ℝ)))) * (1 : ℝ))) = (∫ y in a..b, ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.cos (Real.log (1 /. x))) * (Real.rpow x y)) * (1 : ℝ))) * (1 : ℝ))))
  : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.Icc a b))) → ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.cos (Real.log (1 /. x))) * (Real.rpow x y)) * (1 : ℝ))) = ((1 + y) /. (1 + ((1 + y) ^ (2 : ℕ))))))) := by
  sorry

theorem proof_gap_exercise_3738_2_5
  (a : ℝ)
  (b : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (b ∈ (Set.univ : Set ℝ)) ∧ (b > 0))
  (h3 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 1))) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((((Real.rpow x b) - (Real.rpow x a)) /. (Real.log x)) = (∫ y in a..b, ((Real.rpow x y) * (1 : ℝ)))))))
  (h4 : (∫ x in (0 : ℝ)..(1 : ℝ), (((Real.cos (Real.log (1 /. x))) * (((Real.rpow x b) - (Real.rpow x a)) /. (Real.log x))) * (1 : ℝ))) = (∫ x in (0 : ℝ)..(1 : ℝ), (((Real.cos (Real.log (1 /. x))) * (∫ y in a..b, ((Real.rpow x y) * (1 : ℝ)))) * (1 : ℝ))))
  (h5 : (∫ x in (0 : ℝ)..(1 : ℝ), (((Real.cos (Real.log (1 /. x))) * (∫ y in a..b, ((Real.rpow x y) * (1 : ℝ)))) * (1 : ℝ))) = (∫ y in a..b, ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.cos (Real.log (1 /. x))) * (Real.rpow x y)) * (1 : ℝ))) * (1 : ℝ))))
  (h6 : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.Icc a b))) → ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.cos (Real.log (1 /. x))) * (Real.rpow x y)) * (1 : ℝ))) = ((1 + y) /. (1 + ((1 + y) ^ (2 : ℕ))))))))
  : (∫ y in a..b, ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.cos (Real.log (1 /. x))) * (Real.rpow x y)) * (1 : ℝ))) * (1 : ℝ))) = (∫ y in a..b, ((((1 : ℝ) + y) /. ((1 : ℝ) + ((1 + y) ^ (2 : ℕ)))) * (1 : ℝ))) := by
  sorry

theorem proof_gap_exercise_3738_2_6
  (a : ℝ)
  (b : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (b ∈ (Set.univ : Set ℝ)) ∧ (b > 0))
  (h3 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 1))) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((((Real.rpow x b) - (Real.rpow x a)) /. (Real.log x)) = (∫ y in a..b, ((Real.rpow x y) * (1 : ℝ)))))))
  (h4 : (∫ x in (0 : ℝ)..(1 : ℝ), (((Real.cos (Real.log (1 /. x))) * (((Real.rpow x b) - (Real.rpow x a)) /. (Real.log x))) * (1 : ℝ))) = (∫ x in (0 : ℝ)..(1 : ℝ), (((Real.cos (Real.log (1 /. x))) * (∫ y in a..b, ((Real.rpow x y) * (1 : ℝ)))) * (1 : ℝ))))
  (h5 : (∫ x in (0 : ℝ)..(1 : ℝ), (((Real.cos (Real.log (1 /. x))) * (∫ y in a..b, ((Real.rpow x y) * (1 : ℝ)))) * (1 : ℝ))) = (∫ y in a..b, ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.cos (Real.log (1 /. x))) * (Real.rpow x y)) * (1 : ℝ))) * (1 : ℝ))))
  (h6 : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.Icc a b))) → ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.cos (Real.log (1 /. x))) * (Real.rpow x y)) * (1 : ℝ))) = ((1 + y) /. (1 + ((1 + y) ^ (2 : ℕ))))))))
  (h7 : (∫ y in a..b, ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.cos (Real.log (1 /. x))) * (Real.rpow x y)) * (1 : ℝ))) * (1 : ℝ))) = (∫ y in a..b, ((((1 : ℝ) + y) /. ((1 : ℝ) + ((1 + y) ^ (2 : ℕ)))) * (1 : ℝ))))
  : (∫ y in a..b, ((((1 : ℝ) + y) /. ((1 : ℝ) + ((1 + y) ^ (2 : ℕ)))) * (1 : ℝ))) = ((1 /. 2) * (Real.log ((((b ^ (2 : ℕ)) + (2 * b)) + 2) /. (((a ^ (2 : ℕ)) + (2 * a)) + 2)))) := by
  sorry

theorem proof_gap_exercise_3738_2_7
  (a : ℝ)
  (b : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (b ∈ (Set.univ : Set ℝ)) ∧ (b > 0))
  (h3 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 1))) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((((Real.rpow x b) - (Real.rpow x a)) /. (Real.log x)) = (∫ y in a..b, ((Real.rpow x y) * (1 : ℝ)))))))
  (h4 : (∫ x in (0 : ℝ)..(1 : ℝ), (((Real.cos (Real.log (1 /. x))) * (((Real.rpow x b) - (Real.rpow x a)) /. (Real.log x))) * (1 : ℝ))) = (∫ x in (0 : ℝ)..(1 : ℝ), (((Real.cos (Real.log (1 /. x))) * (∫ y in a..b, ((Real.rpow x y) * (1 : ℝ)))) * (1 : ℝ))))
  (h5 : (∫ x in (0 : ℝ)..(1 : ℝ), (((Real.cos (Real.log (1 /. x))) * (∫ y in a..b, ((Real.rpow x y) * (1 : ℝ)))) * (1 : ℝ))) = (∫ y in a..b, ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.cos (Real.log (1 /. x))) * (Real.rpow x y)) * (1 : ℝ))) * (1 : ℝ))))
  (h6 : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.Icc a b))) → ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.cos (Real.log (1 /. x))) * (Real.rpow x y)) * (1 : ℝ))) = ((1 + y) /. (1 + ((1 + y) ^ (2 : ℕ))))))))
  (h7 : (∫ y in a..b, ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.cos (Real.log (1 /. x))) * (Real.rpow x y)) * (1 : ℝ))) * (1 : ℝ))) = (∫ y in a..b, ((((1 : ℝ) + y) /. ((1 : ℝ) + ((1 + y) ^ (2 : ℕ)))) * (1 : ℝ))))
  (h8 : (∫ y in a..b, ((((1 : ℝ) + y) /. ((1 : ℝ) + ((1 + y) ^ (2 : ℕ)))) * (1 : ℝ))) = ((1 /. 2) * (Real.log ((((b ^ (2 : ℕ)) + (2 * b)) + 2) /. (((a ^ (2 : ℕ)) + (2 * a)) + 2)))))
  : (∫ x in (0 : ℝ)..(1 : ℝ), (((Real.cos (Real.log (1 /. x))) * (((Real.rpow x b) - (Real.rpow x a)) /. (Real.log x))) * (1 : ℝ))) = ((1 /. 2) * (Real.log ((((b ^ (2 : ℕ)) + (2 * b)) + 2) /. (((a ^ (2 : ℕ)) + (2 * a)) + 2)))) := by
  sorry

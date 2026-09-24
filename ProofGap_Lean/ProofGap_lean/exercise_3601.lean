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

-- exercise: exercise_3601

theorem proof_gap_exercise_3601_1
  (f : (ℝ × ℝ -> ℝ))
  (Index_higher_order_terms : ℝ)
  (h1 : Index_higher_order_terms ∈ (Set.univ : Set ℝ))
  (h2 : (forall (t : ℝ) (x : ℝ) (y : ℝ), (((((t ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((1 + x) > 0)) → ((f (x, y)) = (∫ t_1 in (0 : ℝ)..(1 : ℝ), ((Real.rpow (1 + x) ((t_1 ^ (2 : ℕ)) * y)) * (1 : ℝ)))))))
  : (forall (x : ℝ) (t : ℝ) (y : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ ((1 + x) > 0)) ∧ (t ∈ (Set.univ : Set ℝ))) ∧ (y ∈ (Set.univ : Set ℝ))) → ((Real.rpow (1 + x) ((t ^ (2 : ℕ)) * y)) = (Real.exp (((t ^ (2 : ℕ)) * y) * (Real.log (1 + x))))))) := by
  sorry

theorem proof_gap_exercise_3601_2
  (f : (ℝ × ℝ -> ℝ))
  (Index_higher_order_terms : ℝ)
  (h1 : Index_higher_order_terms ∈ (Set.univ : Set ℝ))
  (h2 : (forall (t : ℝ) (x : ℝ) (y : ℝ), (((((t ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((1 + x) > 0)) → ((f (x, y)) = (∫ t_1 in (0 : ℝ)..(1 : ℝ), ((Real.rpow (1 + x) ((t_1 ^ (2 : ℕ)) * y)) * (1 : ℝ)))))))
  (h3 : (forall (x : ℝ) (t : ℝ) (y : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ ((1 + x) > 0)) ∧ (t ∈ (Set.univ : Set ℝ))) ∧ (y ∈ (Set.univ : Set ℝ))) → ((Real.rpow (1 + x) ((t ^ (2 : ℕ)) * y)) = (Real.exp (((t ^ (2 : ℕ)) * y) * (Real.log (1 + x))))))))
  : (forall (t : ℝ) (y : ℝ) (x : ℝ), (((((t ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ ((1 + x) > 0)) → (|((Real.exp (((t ^ (2 : ℕ)) * y) * (Real.log (1 + x)))) - ((1 + (((t ^ (2 : ℕ)) * y) * (Real.log (1 + x)))) + ((1 /. ((2 : ℕ))!) * ((((t ^ (2 : ℕ)) * y) * (Real.log (1 + x))) ^ (2 : ℕ)))))| ≤ Index_higher_order_terms))) := by
  sorry

theorem proof_gap_exercise_3601_3
  (f : (ℝ × ℝ -> ℝ))
  (Index_higher_order_terms : ℝ)
  (h1 : Index_higher_order_terms ∈ (Set.univ : Set ℝ))
  (h2 : (forall (t : ℝ) (x : ℝ) (y : ℝ), (((((t ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((1 + x) > 0)) → ((f (x, y)) = (∫ t_1 in (0 : ℝ)..(1 : ℝ), ((Real.rpow (1 + x) ((t_1 ^ (2 : ℕ)) * y)) * (1 : ℝ)))))))
  (h3 : (forall (x : ℝ) (t : ℝ) (y : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ ((1 + x) > 0)) ∧ (t ∈ (Set.univ : Set ℝ))) ∧ (y ∈ (Set.univ : Set ℝ))) → ((Real.rpow (1 + x) ((t ^ (2 : ℕ)) * y)) = (Real.exp (((t ^ (2 : ℕ)) * y) * (Real.log (1 + x))))))))
  (h4 : (forall (t : ℝ) (y : ℝ) (x : ℝ), (((((t ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ ((1 + x) > 0)) → (|((Real.exp (((t ^ (2 : ℕ)) * y) * (Real.log (1 + x)))) - ((1 + (((t ^ (2 : ℕ)) * y) * (Real.log (1 + x)))) + ((1 /. ((2 : ℕ))!) * ((((t ^ (2 : ℕ)) * y) * (Real.log (1 + x))) ^ (2 : ℕ)))))| ≤ Index_higher_order_terms))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((1 + x) > 0)) → (|((Real.log (1 + x)) - (x - ((x ^ (2 : ℕ)) /. 2)))| ≤ Index_higher_order_terms))) := by
  sorry

theorem proof_gap_exercise_3601_4
  (f : (ℝ × ℝ -> ℝ))
  (Index_higher_order_terms : ℝ)
  (h1 : Index_higher_order_terms ∈ (Set.univ : Set ℝ))
  (h2 : (forall (t : ℝ) (x : ℝ) (y : ℝ), (((((t ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((1 + x) > 0)) → ((f (x, y)) = (∫ t_1 in (0 : ℝ)..(1 : ℝ), ((Real.rpow (1 + x) ((t_1 ^ (2 : ℕ)) * y)) * (1 : ℝ)))))))
  (h3 : (forall (x : ℝ) (t : ℝ) (y : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ ((1 + x) > 0)) ∧ (t ∈ (Set.univ : Set ℝ))) ∧ (y ∈ (Set.univ : Set ℝ))) → ((Real.rpow (1 + x) ((t ^ (2 : ℕ)) * y)) = (Real.exp (((t ^ (2 : ℕ)) * y) * (Real.log (1 + x))))))))
  (h4 : (forall (t : ℝ) (y : ℝ) (x : ℝ), (((((t ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ ((1 + x) > 0)) → (|((Real.exp (((t ^ (2 : ℕ)) * y) * (Real.log (1 + x)))) - ((1 + (((t ^ (2 : ℕ)) * y) * (Real.log (1 + x)))) + ((1 /. ((2 : ℕ))!) * ((((t ^ (2 : ℕ)) * y) * (Real.log (1 + x))) ^ (2 : ℕ)))))| ≤ Index_higher_order_terms))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((1 + x) > 0)) → (|((Real.log (1 + x)) - (x - ((x ^ (2 : ℕ)) /. 2)))| ≤ Index_higher_order_terms))))
  : (forall (x : ℝ) (t : ℝ) (y : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ ((1 + x) > 0)) ∧ (t ∈ (Set.univ : Set ℝ))) ∧ (y ∈ (Set.univ : Set ℝ))) → (|((Real.rpow (1 + x) ((t ^ (2 : ℕ)) * y)) - ((1 + (((t ^ (2 : ℕ)) * x) * y)) - ((((t ^ (2 : ℕ)) * (x ^ (2 : ℕ))) * y) /. 2)))| ≤ Index_higher_order_terms))) := by
  sorry

theorem proof_gap_exercise_3601_5
  (f : (ℝ × ℝ -> ℝ))
  (Index_higher_order_terms : ℝ)
  (h1 : Index_higher_order_terms ∈ (Set.univ : Set ℝ))
  (h2 : (forall (t : ℝ) (x : ℝ) (y : ℝ), (((((t ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((1 + x) > 0)) → ((f (x, y)) = (∫ t_1 in (0 : ℝ)..(1 : ℝ), ((Real.rpow (1 + x) ((t_1 ^ (2 : ℕ)) * y)) * (1 : ℝ)))))))
  (h3 : (forall (x : ℝ) (t : ℝ) (y : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ ((1 + x) > 0)) ∧ (t ∈ (Set.univ : Set ℝ))) ∧ (y ∈ (Set.univ : Set ℝ))) → ((Real.rpow (1 + x) ((t ^ (2 : ℕ)) * y)) = (Real.exp (((t ^ (2 : ℕ)) * y) * (Real.log (1 + x))))))))
  (h4 : (forall (t : ℝ) (y : ℝ) (x : ℝ), (((((t ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ ((1 + x) > 0)) → (|((Real.exp (((t ^ (2 : ℕ)) * y) * (Real.log (1 + x)))) - ((1 + (((t ^ (2 : ℕ)) * y) * (Real.log (1 + x)))) + ((1 /. ((2 : ℕ))!) * ((((t ^ (2 : ℕ)) * y) * (Real.log (1 + x))) ^ (2 : ℕ)))))| ≤ Index_higher_order_terms))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((1 + x) > 0)) → (|((Real.log (1 + x)) - (x - ((x ^ (2 : ℕ)) /. 2)))| ≤ Index_higher_order_terms))))
  (h6 : (forall (x : ℝ) (t : ℝ) (y : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ ((1 + x) > 0)) ∧ (t ∈ (Set.univ : Set ℝ))) ∧ (y ∈ (Set.univ : Set ℝ))) → (|((Real.rpow (1 + x) ((t ^ (2 : ℕ)) * y)) - ((1 + (((t ^ (2 : ℕ)) * x) * y)) - ((((t ^ (2 : ℕ)) * (x ^ (2 : ℕ))) * y) /. 2)))| ≤ Index_higher_order_terms))))
  : (forall (x : ℝ) (y : ℝ) (t : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ ((1 + x) > 0)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (t ∈ (Set.univ : Set ℝ))) → (|((f (x, y)) - (∫ t_1 in (0 : ℝ)..(1 : ℝ), ((((1 : ℝ) + (((t_1 ^ (2 : ℕ)) * x) * y)) - ((((t_1 ^ (2 : ℕ)) * (x ^ (2 : ℕ))) * y) /. (2 : ℝ))) * (1 : ℝ))))| ≤ Index_higher_order_terms))) := by
  sorry

theorem proof_gap_exercise_3601_6
  (f : (ℝ × ℝ -> ℝ))
  (Index_higher_order_terms : ℝ)
  (h1 : Index_higher_order_terms ∈ (Set.univ : Set ℝ))
  (h2 : (forall (t : ℝ) (x : ℝ) (y : ℝ), (((((t ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((1 + x) > 0)) → ((f (x, y)) = (∫ t_1 in (0 : ℝ)..(1 : ℝ), ((Real.rpow (1 + x) ((t_1 ^ (2 : ℕ)) * y)) * (1 : ℝ)))))))
  (h3 : (forall (x : ℝ) (t : ℝ) (y : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ ((1 + x) > 0)) ∧ (t ∈ (Set.univ : Set ℝ))) ∧ (y ∈ (Set.univ : Set ℝ))) → ((Real.rpow (1 + x) ((t ^ (2 : ℕ)) * y)) = (Real.exp (((t ^ (2 : ℕ)) * y) * (Real.log (1 + x))))))))
  (h4 : (forall (t : ℝ) (y : ℝ) (x : ℝ), (((((t ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ ((1 + x) > 0)) → (|((Real.exp (((t ^ (2 : ℕ)) * y) * (Real.log (1 + x)))) - ((1 + (((t ^ (2 : ℕ)) * y) * (Real.log (1 + x)))) + ((1 /. ((2 : ℕ))!) * ((((t ^ (2 : ℕ)) * y) * (Real.log (1 + x))) ^ (2 : ℕ)))))| ≤ Index_higher_order_terms))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((1 + x) > 0)) → (|((Real.log (1 + x)) - (x - ((x ^ (2 : ℕ)) /. 2)))| ≤ Index_higher_order_terms))))
  (h6 : (forall (x : ℝ) (t : ℝ) (y : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ ((1 + x) > 0)) ∧ (t ∈ (Set.univ : Set ℝ))) ∧ (y ∈ (Set.univ : Set ℝ))) → (|((Real.rpow (1 + x) ((t ^ (2 : ℕ)) * y)) - ((1 + (((t ^ (2 : ℕ)) * x) * y)) - ((((t ^ (2 : ℕ)) * (x ^ (2 : ℕ))) * y) /. 2)))| ≤ Index_higher_order_terms))))
  (h7 : (forall (x : ℝ) (y : ℝ) (t : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ ((1 + x) > 0)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (t ∈ (Set.univ : Set ℝ))) → (|((f (x, y)) - (∫ t_1 in (0 : ℝ)..(1 : ℝ), ((((1 : ℝ) + (((t_1 ^ (2 : ℕ)) * x) * y)) - ((((t_1 ^ (2 : ℕ)) * (x ^ (2 : ℕ))) * y) /. (2 : ℝ))) * (1 : ℝ))))| ≤ Index_higher_order_terms))))
  : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((1 + x) > 0)) ∧ (y ∈ (Set.univ : Set ℝ))) → (|((f (x, y)) - (1 + (((1 /. 3) * y) * (x - ((x ^ (2 : ℕ)) /. 2)))))| ≤ Index_higher_order_terms))) := by
  sorry

theorem proof_gap_exercise_3601_7
  (f : (ℝ × ℝ -> ℝ))
  (Index_higher_order_terms : ℝ)
  (h1 : Index_higher_order_terms ∈ (Set.univ : Set ℝ))
  (h2 : (forall (t : ℝ) (x : ℝ) (y : ℝ), (((((t ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ ((1 + x) > 0)) → ((f (x, y)) = (∫ t_1 in (0 : ℝ)..(1 : ℝ), ((Real.rpow (1 + x) ((t_1 ^ (2 : ℕ)) * y)) * (1 : ℝ)))))))
  (h3 : (forall (x : ℝ) (t : ℝ) (y : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ ((1 + x) > 0)) ∧ (t ∈ (Set.univ : Set ℝ))) ∧ (y ∈ (Set.univ : Set ℝ))) → ((Real.rpow (1 + x) ((t ^ (2 : ℕ)) * y)) = (Real.exp (((t ^ (2 : ℕ)) * y) * (Real.log (1 + x))))))))
  (h4 : (forall (t : ℝ) (y : ℝ) (x : ℝ), (((((t ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ ((1 + x) > 0)) → (|((Real.exp (((t ^ (2 : ℕ)) * y) * (Real.log (1 + x)))) - ((1 + (((t ^ (2 : ℕ)) * y) * (Real.log (1 + x)))) + ((1 /. ((2 : ℕ))!) * ((((t ^ (2 : ℕ)) * y) * (Real.log (1 + x))) ^ (2 : ℕ)))))| ≤ Index_higher_order_terms))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((1 + x) > 0)) → (|((Real.log (1 + x)) - (x - ((x ^ (2 : ℕ)) /. 2)))| ≤ Index_higher_order_terms))))
  (h6 : (forall (x : ℝ) (t : ℝ) (y : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ ((1 + x) > 0)) ∧ (t ∈ (Set.univ : Set ℝ))) ∧ (y ∈ (Set.univ : Set ℝ))) → (|((Real.rpow (1 + x) ((t ^ (2 : ℕ)) * y)) - ((1 + (((t ^ (2 : ℕ)) * x) * y)) - ((((t ^ (2 : ℕ)) * (x ^ (2 : ℕ))) * y) /. 2)))| ≤ Index_higher_order_terms))))
  (h7 : (forall (x : ℝ) (y : ℝ) (t : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ ((1 + x) > 0)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (t ∈ (Set.univ : Set ℝ))) → (|((f (x, y)) - (∫ t_1 in (0 : ℝ)..(1 : ℝ), ((((1 : ℝ) + (((t_1 ^ (2 : ℕ)) * x) * y)) - ((((t_1 ^ (2 : ℕ)) * (x ^ (2 : ℕ))) * y) /. (2 : ℝ))) * (1 : ℝ))))| ≤ Index_higher_order_terms))))
  (h8 : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((1 + x) > 0)) ∧ (y ∈ (Set.univ : Set ℝ))) → (|((f (x, y)) - (1 + (((1 /. 3) * y) * (x - ((x ^ (2 : ℕ)) /. 2)))))| ≤ Index_higher_order_terms))))
  : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((1 + x) > 0)) ∧ (y ∈ (Set.univ : Set ℝ))) → (|((f (x, y)) - ((1 + (((1 /. 3) * x) * y)) - (((1 /. 6) * (x ^ (2 : ℕ))) * y)))| ≤ Index_higher_order_terms))) := by
  sorry

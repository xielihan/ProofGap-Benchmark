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

-- exercise: exercise_204

theorem proof_gap_exercise_204_1
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a ∈ ({x_1 : ℝ | 0 < x_1})))
  (h2 : a ≠ 1)
  (h3 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((f t) = ((1 /. 2) * ((Real.rpow a t) + (Real.rpow a (-t))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (((f (x + y)) + (f (x - y))) = (((1 /. 2) * ((Real.rpow a (x + y)) + (Real.rpow a ((-x) - y)))) + ((1 /. 2) * ((Real.rpow a (x - y)) + (Real.rpow a ((-x) + y)))))))))) := by
  sorry

theorem proof_gap_exercise_204_2
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a ∈ ({x_1 : ℝ | 0 < x_1})))
  (h2 : a ≠ 1)
  (h3 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((f t) = ((1 /. 2) * ((Real.rpow a t) + (Real.rpow a (-t))))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (((f (x + y)) + (f (x - y))) = (((1 /. 2) * ((Real.rpow a (x + y)) + (Real.rpow a ((-x) - y)))) + ((1 /. 2) * ((Real.rpow a (x - y)) + (Real.rpow a ((-x) + y)))))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (((f (x + y)) + (f (x - y))) = (((1 /. 2) * (((Real.rpow a x) * (Real.rpow a y)) + ((Real.rpow a (-x)) * (Real.rpow a (-y))))) + ((1 /. 2) * (((Real.rpow a x) * (Real.rpow a (-y))) + ((Real.rpow a (-x)) * (Real.rpow a y)))))))))) := by
  sorry

theorem proof_gap_exercise_204_3
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a ∈ ({x_1 : ℝ | 0 < x_1})))
  (h2 : a ≠ 1)
  (h3 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((f t) = ((1 /. 2) * ((Real.rpow a t) + (Real.rpow a (-t))))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (((f (x + y)) + (f (x - y))) = (((1 /. 2) * ((Real.rpow a (x + y)) + (Real.rpow a ((-x) - y)))) + ((1 /. 2) * ((Real.rpow a (x - y)) + (Real.rpow a ((-x) + y)))))))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (((f (x + y)) + (f (x - y))) = (((1 /. 2) * (((Real.rpow a x) * (Real.rpow a y)) + ((Real.rpow a (-x)) * (Real.rpow a (-y))))) + ((1 /. 2) * (((Real.rpow a x) * (Real.rpow a (-y))) + ((Real.rpow a (-x)) * (Real.rpow a y)))))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (((f (x + y)) + (f (x - y))) = ((((1 /. 2) * (Real.rpow a x)) * ((Real.rpow a y) + (Real.rpow a (-y)))) + (((1 /. 2) * (Real.rpow a (-x))) * ((Real.rpow a (-y)) + (Real.rpow a y))))))))) := by
  sorry

theorem proof_gap_exercise_204_4
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a ∈ ({x_1 : ℝ | 0 < x_1})))
  (h2 : a ≠ 1)
  (h3 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((f t) = ((1 /. 2) * ((Real.rpow a t) + (Real.rpow a (-t))))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (((f (x + y)) + (f (x - y))) = (((1 /. 2) * ((Real.rpow a (x + y)) + (Real.rpow a ((-x) - y)))) + ((1 /. 2) * ((Real.rpow a (x - y)) + (Real.rpow a ((-x) + y)))))))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (((f (x + y)) + (f (x - y))) = (((1 /. 2) * (((Real.rpow a x) * (Real.rpow a y)) + ((Real.rpow a (-x)) * (Real.rpow a (-y))))) + ((1 /. 2) * (((Real.rpow a x) * (Real.rpow a (-y))) + ((Real.rpow a (-x)) * (Real.rpow a y)))))))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (((f (x + y)) + (f (x - y))) = ((((1 /. 2) * (Real.rpow a x)) * ((Real.rpow a y) + (Real.rpow a (-y)))) + (((1 /. 2) * (Real.rpow a (-x))) * ((Real.rpow a (-y)) + (Real.rpow a y))))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (((f (x + y)) + (f (x - y))) = (((1 /. 2) * ((Real.rpow a x) + (Real.rpow a (-x)))) * ((Real.rpow a y) + (Real.rpow a (-y))))))))) := by
  sorry

theorem proof_gap_exercise_204_5
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a ∈ ({x_1 : ℝ | 0 < x_1})))
  (h2 : a ≠ 1)
  (h3 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((f t) = ((1 /. 2) * ((Real.rpow a t) + (Real.rpow a (-t))))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (((f (x + y)) + (f (x - y))) = (((1 /. 2) * ((Real.rpow a (x + y)) + (Real.rpow a ((-x) - y)))) + ((1 /. 2) * ((Real.rpow a (x - y)) + (Real.rpow a ((-x) + y)))))))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (((f (x + y)) + (f (x - y))) = (((1 /. 2) * (((Real.rpow a x) * (Real.rpow a y)) + ((Real.rpow a (-x)) * (Real.rpow a (-y))))) + ((1 /. 2) * (((Real.rpow a x) * (Real.rpow a (-y))) + ((Real.rpow a (-x)) * (Real.rpow a y)))))))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (((f (x + y)) + (f (x - y))) = ((((1 /. 2) * (Real.rpow a x)) * ((Real.rpow a y) + (Real.rpow a (-y)))) + (((1 /. 2) * (Real.rpow a (-x))) * ((Real.rpow a (-y)) + (Real.rpow a y))))))))))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (((f (x + y)) + (f (x - y))) = (((1 /. 2) * ((Real.rpow a x) + (Real.rpow a (-x)))) * ((Real.rpow a y) + (Real.rpow a (-y))))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((((1 /. 2) * ((Real.rpow a x) + (Real.rpow a (-x)))) * ((Real.rpow a y) + (Real.rpow a (-y)))) = ((2 * (f x)) * (f y))))))) := by
  sorry

theorem proof_gap_exercise_204_6
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a ∈ ({x_1 : ℝ | 0 < x_1})))
  (h2 : a ≠ 1)
  (h3 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((f t) = ((1 /. 2) * ((Real.rpow a t) + (Real.rpow a (-t))))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (((f (x + y)) + (f (x - y))) = (((1 /. 2) * ((Real.rpow a (x + y)) + (Real.rpow a ((-x) - y)))) + ((1 /. 2) * ((Real.rpow a (x - y)) + (Real.rpow a ((-x) + y)))))))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (((f (x + y)) + (f (x - y))) = (((1 /. 2) * (((Real.rpow a x) * (Real.rpow a y)) + ((Real.rpow a (-x)) * (Real.rpow a (-y))))) + ((1 /. 2) * (((Real.rpow a x) * (Real.rpow a (-y))) + ((Real.rpow a (-x)) * (Real.rpow a y)))))))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (((f (x + y)) + (f (x - y))) = ((((1 /. 2) * (Real.rpow a x)) * ((Real.rpow a y) + (Real.rpow a (-y)))) + (((1 /. 2) * (Real.rpow a (-x))) * ((Real.rpow a (-y)) + (Real.rpow a y))))))))))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (((f (x + y)) + (f (x - y))) = (((1 /. 2) * ((Real.rpow a x) + (Real.rpow a (-x)))) * ((Real.rpow a y) + (Real.rpow a (-y))))))))))
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((((1 /. 2) * ((Real.rpow a x) + (Real.rpow a (-x)))) * ((Real.rpow a y) + (Real.rpow a (-y)))) = ((2 * (f x)) * (f y))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (((f (x + y)) + (f (x - y))) = ((2 * (f x)) * (f y))))))) := by
  sorry

theorem proof_gap_exercise_204_7
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a ∈ ({x_1 : ℝ | 0 < x_1})))
  (h2 : a ≠ 1)
  (h3 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((f t) = ((1 /. 2) * ((Real.rpow a t) + (Real.rpow a (-t))))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (((f (x + y)) + (f (x - y))) = (((1 /. 2) * ((Real.rpow a (x + y)) + (Real.rpow a ((-x) - y)))) + ((1 /. 2) * ((Real.rpow a (x - y)) + (Real.rpow a ((-x) + y)))))))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (((f (x + y)) + (f (x - y))) = (((1 /. 2) * (((Real.rpow a x) * (Real.rpow a y)) + ((Real.rpow a (-x)) * (Real.rpow a (-y))))) + ((1 /. 2) * (((Real.rpow a x) * (Real.rpow a (-y))) + ((Real.rpow a (-x)) * (Real.rpow a y)))))))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (((f (x + y)) + (f (x - y))) = ((((1 /. 2) * (Real.rpow a x)) * ((Real.rpow a y) + (Real.rpow a (-y)))) + (((1 /. 2) * (Real.rpow a (-x))) * ((Real.rpow a (-y)) + (Real.rpow a y))))))))))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (((f (x + y)) + (f (x - y))) = (((1 /. 2) * ((Real.rpow a x) + (Real.rpow a (-x)))) * ((Real.rpow a y) + (Real.rpow a (-y))))))))))
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((((1 /. 2) * ((Real.rpow a x) + (Real.rpow a (-x)))) * ((Real.rpow a y) + (Real.rpow a (-y)))) = ((2 * (f x)) * (f y))))))))
  (h9 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (((f (x + y)) + (f (x - y))) = ((2 * (f x)) * (f y))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (((f (x + y)) + (f (x - y))) = ((2 * (f x)) * (f y))))))) := by
  sorry

theorem proof_gap_exercise_204_8
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a ∈ ({x_1 : ℝ | 0 < x_1})))
  (h2 : a ≠ 1)
  (h3 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((f t) = ((1 /. 2) * ((Real.rpow a t) + (Real.rpow a (-t))))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (((f (x + y)) + (f (x - y))) = (((1 /. 2) * ((Real.rpow a (x + y)) + (Real.rpow a ((-x) - y)))) + ((1 /. 2) * ((Real.rpow a (x - y)) + (Real.rpow a ((-x) + y)))))))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (((f (x + y)) + (f (x - y))) = (((1 /. 2) * (((Real.rpow a x) * (Real.rpow a y)) + ((Real.rpow a (-x)) * (Real.rpow a (-y))))) + ((1 /. 2) * (((Real.rpow a x) * (Real.rpow a (-y))) + ((Real.rpow a (-x)) * (Real.rpow a y)))))))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (((f (x + y)) + (f (x - y))) = ((((1 /. 2) * (Real.rpow a x)) * ((Real.rpow a y) + (Real.rpow a (-y)))) + (((1 /. 2) * (Real.rpow a (-x))) * ((Real.rpow a (-y)) + (Real.rpow a y))))))))))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (((f (x + y)) + (f (x - y))) = (((1 /. 2) * ((Real.rpow a x) + (Real.rpow a (-x)))) * ((Real.rpow a y) + (Real.rpow a (-y))))))))))
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((((1 /. 2) * ((Real.rpow a x) + (Real.rpow a (-x)))) * ((Real.rpow a y) + (Real.rpow a (-y)))) = ((2 * (f x)) * (f y))))))))
  (h9 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (((f (x + y)) + (f (x - y))) = ((2 * (f x)) * (f y))))))))
  (h10 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (((f (x + y)) + (f (x - y))) = ((2 * (f x)) * (f y))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (((f (x + y)) + (f (x - y))) = ((2 * (f x)) * (f y))))))) := by
  sorry

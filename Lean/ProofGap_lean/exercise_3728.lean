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

-- exercise: exercise_3728

theorem proof_gap_exercise_3728_1
  (u : (ℝ -> ℝ))
  (v : (ℝ -> ℝ))
  (K : (ℝ × ℝ -> ℝ))
  (h1 : ContinuousOn v (Set.Icc 0 1))
  (h2 : (forall (x : ℝ) (y : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Icc 0 1))) ∧ (y ∈ (Set.Icc 0 1))) → ((K (x, y)) = (if (x ≤ y) then (x * (1 - y)) else (if (x > y) then (y * (1 - x)) else (y * (1 - x))))))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((u x) = (∫ y in (0 : ℝ)..(1 : ℝ), (((K (x, y)) * (v y)) * (1 : ℝ)))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((u x) = ((∫ y in (0 : ℝ)..x, (((y * ((1 : ℝ) - x)) * (v y)) * (1 : ℝ))) + (∫ y in x..(1 : ℝ), (((x * ((1 : ℝ) - y)) * (v y)) * (1 : ℝ))))))) := by
  sorry

theorem proof_gap_exercise_3728_2
  (u : (ℝ -> ℝ))
  (v : (ℝ -> ℝ))
  (K : (ℝ × ℝ -> ℝ))
  (h1 : ContinuousOn v (Set.Icc 0 1))
  (h2 : (forall (x : ℝ) (y : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Icc 0 1))) ∧ (y ∈ (Set.Icc 0 1))) → ((K (x, y)) = (if (x ≤ y) then (x * (1 - y)) else (if (x > y) then (y * (1 - x)) else (y * (1 - x))))))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((u x) = (∫ y in (0 : ℝ)..(1 : ℝ), (((K (x, y)) * (v y)) * (1 : ℝ)))))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((u x) = ((∫ y in (0 : ℝ)..x, (((y * ((1 : ℝ) - x)) * (v y)) * (1 : ℝ))) + (∫ y in x..(1 : ℝ), (((x * ((1 : ℝ) - y)) * (v y)) * (1 : ℝ))))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((iteratedDeriv 1 (fun t => u t) x) = (((((x * (1 - x)) * (v x)) - (∫ y in (0 : ℝ)..x, ((y * (v y)) * (1 : ℝ)))) - ((x * (1 - x)) * (v x))) + (∫ y in x..(1 : ℝ), ((((1 : ℝ) - y) * (v y)) * (1 : ℝ))))))) := by
  sorry

theorem proof_gap_exercise_3728_3
  (u : (ℝ -> ℝ))
  (v : (ℝ -> ℝ))
  (K : (ℝ × ℝ -> ℝ))
  (h1 : ContinuousOn v (Set.Icc 0 1))
  (h2 : (forall (x : ℝ) (y : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Icc 0 1))) ∧ (y ∈ (Set.Icc 0 1))) → ((K (x, y)) = (if (x ≤ y) then (x * (1 - y)) else (if (x > y) then (y * (1 - x)) else (y * (1 - x))))))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((u x) = (∫ y in (0 : ℝ)..(1 : ℝ), (((K (x, y)) * (v y)) * (1 : ℝ)))))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((u x) = ((∫ y in (0 : ℝ)..x, (((y * ((1 : ℝ) - x)) * (v y)) * (1 : ℝ))) + (∫ y in x..(1 : ℝ), (((x * ((1 : ℝ) - y)) * (v y)) * (1 : ℝ))))))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((iteratedDeriv 1 (fun t => u t) x) = (((((x * (1 - x)) * (v x)) - (∫ y in (0 : ℝ)..x, ((y * (v y)) * (1 : ℝ)))) - ((x * (1 - x)) * (v x))) + (∫ y in x..(1 : ℝ), ((((1 : ℝ) - y) * (v y)) * (1 : ℝ))))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((iteratedDeriv 1 (fun t => u t) x) = ((-(∫ y in (0 : ℝ)..x, ((y * (v y)) * (1 : ℝ)))) + (∫ y in x..(1 : ℝ), ((((1 : ℝ) - y) * (v y)) * (1 : ℝ))))))) := by
  sorry

theorem proof_gap_exercise_3728_4
  (u : (ℝ -> ℝ))
  (v : (ℝ -> ℝ))
  (K : (ℝ × ℝ -> ℝ))
  (h1 : ContinuousOn v (Set.Icc 0 1))
  (h2 : (forall (x : ℝ) (y : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Icc 0 1))) ∧ (y ∈ (Set.Icc 0 1))) → ((K (x, y)) = (if (x ≤ y) then (x * (1 - y)) else (if (x > y) then (y * (1 - x)) else (y * (1 - x))))))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((u x) = (∫ y in (0 : ℝ)..(1 : ℝ), (((K (x, y)) * (v y)) * (1 : ℝ)))))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((u x) = ((∫ y in (0 : ℝ)..x, (((y * ((1 : ℝ) - x)) * (v y)) * (1 : ℝ))) + (∫ y in x..(1 : ℝ), (((x * ((1 : ℝ) - y)) * (v y)) * (1 : ℝ))))))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((iteratedDeriv 1 (fun t => u t) x) = (((((x * (1 - x)) * (v x)) - (∫ y in (0 : ℝ)..x, ((y * (v y)) * (1 : ℝ)))) - ((x * (1 - x)) * (v x))) + (∫ y in x..(1 : ℝ), ((((1 : ℝ) - y) * (v y)) * (1 : ℝ))))))))
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((iteratedDeriv 1 (fun t => u t) x) = ((-(∫ y in (0 : ℝ)..x, ((y * (v y)) * (1 : ℝ)))) + (∫ y in x..(1 : ℝ), ((((1 : ℝ) - y) * (v y)) * (1 : ℝ))))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((iteratedDeriv 2 (fun t => u t) x) = (((-x) * (v x)) - ((1 - x) * (v x)))))) := by
  sorry

theorem proof_gap_exercise_3728_5
  (u : (ℝ -> ℝ))
  (v : (ℝ -> ℝ))
  (K : (ℝ × ℝ -> ℝ))
  (h1 : ContinuousOn v (Set.Icc 0 1))
  (h2 : (forall (x : ℝ) (y : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Icc 0 1))) ∧ (y ∈ (Set.Icc 0 1))) → ((K (x, y)) = (if (x ≤ y) then (x * (1 - y)) else (if (x > y) then (y * (1 - x)) else (y * (1 - x))))))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((u x) = (∫ y in (0 : ℝ)..(1 : ℝ), (((K (x, y)) * (v y)) * (1 : ℝ)))))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((u x) = ((∫ y in (0 : ℝ)..x, (((y * ((1 : ℝ) - x)) * (v y)) * (1 : ℝ))) + (∫ y in x..(1 : ℝ), (((x * ((1 : ℝ) - y)) * (v y)) * (1 : ℝ))))))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((iteratedDeriv 1 (fun t => u t) x) = (((((x * (1 - x)) * (v x)) - (∫ y in (0 : ℝ)..x, ((y * (v y)) * (1 : ℝ)))) - ((x * (1 - x)) * (v x))) + (∫ y in x..(1 : ℝ), ((((1 : ℝ) - y) * (v y)) * (1 : ℝ))))))))
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((iteratedDeriv 1 (fun t => u t) x) = ((-(∫ y in (0 : ℝ)..x, ((y * (v y)) * (1 : ℝ)))) + (∫ y in x..(1 : ℝ), ((((1 : ℝ) - y) * (v y)) * (1 : ℝ))))))))
  (h7 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((iteratedDeriv 2 (fun t => u t) x) = (((-x) * (v x)) - ((1 - x) * (v x)))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((iteratedDeriv 2 (fun t => u t) x) = (-(v x))))) := by
  sorry

theorem proof_gap_exercise_3728_6
  (u : (ℝ -> ℝ))
  (v : (ℝ -> ℝ))
  (K : (ℝ × ℝ -> ℝ))
  (h1 : ContinuousOn v (Set.Icc 0 1))
  (h2 : (forall (x : ℝ) (y : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Icc 0 1))) ∧ (y ∈ (Set.Icc 0 1))) → ((K (x, y)) = (if (x ≤ y) then (x * (1 - y)) else (if (x > y) then (y * (1 - x)) else (y * (1 - x))))))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((u x) = (∫ y in (0 : ℝ)..(1 : ℝ), (((K (x, y)) * (v y)) * (1 : ℝ)))))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((u x) = ((∫ y in (0 : ℝ)..x, (((y * ((1 : ℝ) - x)) * (v y)) * (1 : ℝ))) + (∫ y in x..(1 : ℝ), (((x * ((1 : ℝ) - y)) * (v y)) * (1 : ℝ))))))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((iteratedDeriv 1 (fun t => u t) x) = (((((x * (1 - x)) * (v x)) - (∫ y in (0 : ℝ)..x, ((y * (v y)) * (1 : ℝ)))) - ((x * (1 - x)) * (v x))) + (∫ y in x..(1 : ℝ), ((((1 : ℝ) - y) * (v y)) * (1 : ℝ))))))))
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((iteratedDeriv 1 (fun t => u t) x) = ((-(∫ y in (0 : ℝ)..x, ((y * (v y)) * (1 : ℝ)))) + (∫ y in x..(1 : ℝ), ((((1 : ℝ) - y) * (v y)) * (1 : ℝ))))))))
  (h7 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((iteratedDeriv 2 (fun t => u t) x) = (((-x) * (v x)) - ((1 - x) * (v x)))))))
  (h8 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((iteratedDeriv 2 (fun t => u t) x) = (-(v x))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((iteratedDeriv 2 (fun t => u t) x) = (-(v x))))) := by
  sorry

theorem proof_gap_exercise_3728_7
  (u : (ℝ -> ℝ))
  (v : (ℝ -> ℝ))
  (K : (ℝ × ℝ -> ℝ))
  (h1 : ContinuousOn v (Set.Icc 0 1))
  (h2 : (forall (x : ℝ) (y : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Icc 0 1))) ∧ (y ∈ (Set.Icc 0 1))) → ((K (x, y)) = (if (x ≤ y) then (x * (1 - y)) else (if (x > y) then (y * (1 - x)) else (y * (1 - x))))))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((u x) = (∫ y in (0 : ℝ)..(1 : ℝ), (((K (x, y)) * (v y)) * (1 : ℝ)))))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((u x) = ((∫ y in (0 : ℝ)..x, (((y * ((1 : ℝ) - x)) * (v y)) * (1 : ℝ))) + (∫ y in x..(1 : ℝ), (((x * ((1 : ℝ) - y)) * (v y)) * (1 : ℝ))))))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((iteratedDeriv 1 (fun t => u t) x) = (((((x * (1 - x)) * (v x)) - (∫ y in (0 : ℝ)..x, ((y * (v y)) * (1 : ℝ)))) - ((x * (1 - x)) * (v x))) + (∫ y in x..(1 : ℝ), ((((1 : ℝ) - y) * (v y)) * (1 : ℝ))))))))
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((iteratedDeriv 1 (fun t => u t) x) = ((-(∫ y in (0 : ℝ)..x, ((y * (v y)) * (1 : ℝ)))) + (∫ y in x..(1 : ℝ), ((((1 : ℝ) - y) * (v y)) * (1 : ℝ))))))))
  (h7 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((iteratedDeriv 2 (fun t => u t) x) = (((-x) * (v x)) - ((1 - x) * (v x)))))))
  (h8 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((iteratedDeriv 2 (fun t => u t) x) = (-(v x))))))
  (h9 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((iteratedDeriv 2 (fun t => u t) x) = (-(v x))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((iteratedDeriv 2 (fun t => u t) x) = (-(v x))))) := by
  sorry

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

-- exercise: exercise_1305

theorem proof_gap_exercise_1305_1
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (Real.log (1 + (x ^ (2 : ℕ))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = ((2 * x) /. (1 + (x ^ (2 : ℕ))))))) := by
  sorry

theorem proof_gap_exercise_1305_2
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (Real.log (1 + (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = ((2 * x) /. (1 + (x ^ (2 : ℕ))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => y t) x) = ((2 * (1 - (x ^ (2 : ℕ)))) /. ((1 + (x ^ (2 : ℕ))) ^ (2 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_1305_3
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (Real.log (1 + (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = ((2 * x) /. (1 + (x ^ (2 : ℕ))))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => y t) x) = ((2 * (1 - (x ^ (2 : ℕ)))) /. ((1 + (x ^ (2 : ℕ))) ^ (2 : ℕ)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((iteratedDeriv 2 (fun t => y t) x) > 0))) := by
  sorry

theorem proof_gap_exercise_1305_4
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (Real.log (1 + (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = ((2 * x) /. (1 + (x ^ (2 : ℕ))))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => y t) x) = ((2 * (1 - (x ^ (2 : ℕ)))) /. ((1 + (x ^ (2 : ℕ))) ^ (2 : ℕ)))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((iteratedDeriv 2 (fun t => y t) x) > 0))))
  : ConvexOn ℝ (Set.Ioo (-(1 : ℝ)) 1) y := by
  sorry

theorem proof_gap_exercise_1305_5
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (Real.log (1 + (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = ((2 * x) /. (1 + (x ^ (2 : ℕ))))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => y t) x) = ((2 * (1 - (x ^ (2 : ℕ)))) /. ((1 + (x ^ (2 : ℕ))) ^ (2 : ℕ)))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((iteratedDeriv 2 (fun t => y t) x) > 0))))
  (h5 : ConvexOn ℝ (Set.Ioo (-(1 : ℝ)) 1) y)
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| > 1)) → ((iteratedDeriv 2 (fun t => y t) x) < 0))) := by
  sorry

theorem proof_gap_exercise_1305_6
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (Real.log (1 + (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = ((2 * x) /. (1 + (x ^ (2 : ℕ))))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => y t) x) = ((2 * (1 - (x ^ (2 : ℕ)))) /. ((1 + (x ^ (2 : ℕ))) ^ (2 : ℕ)))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((iteratedDeriv 2 (fun t => y t) x) > 0))))
  (h5 : ConvexOn ℝ (Set.Ioo (-(1 : ℝ)) 1) y)
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| > 1)) → ((iteratedDeriv 2 (fun t => y t) x) < 0))))
  : ConcaveOn ℝ (Set.Iio (-(1 : ℝ))) y := by
  sorry

theorem proof_gap_exercise_1305_7
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (Real.log (1 + (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = ((2 * x) /. (1 + (x ^ (2 : ℕ))))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => y t) x) = ((2 * (1 - (x ^ (2 : ℕ)))) /. ((1 + (x ^ (2 : ℕ))) ^ (2 : ℕ)))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((iteratedDeriv 2 (fun t => y t) x) > 0))))
  (h5 : ConvexOn ℝ (Set.Ioo (-(1 : ℝ)) 1) y)
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| > 1)) → ((iteratedDeriv 2 (fun t => y t) x) < 0))))
  (h7 : ConcaveOn ℝ (Set.Iio (-(1 : ℝ))) y)
  : ConcaveOn ℝ (Set.Ioi 1) y := by
  sorry

theorem proof_gap_exercise_1305_8
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (Real.log (1 + (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = ((2 * x) /. (1 + (x ^ (2 : ℕ))))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => y t) x) = ((2 * (1 - (x ^ (2 : ℕ)))) /. ((1 + (x ^ (2 : ℕ))) ^ (2 : ℕ)))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((iteratedDeriv 2 (fun t => y t) x) > 0))))
  (h5 : ConvexOn ℝ (Set.Ioo (-(1 : ℝ)) 1) y)
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| > 1)) → ((iteratedDeriv 2 (fun t => y t) x) < 0))))
  (h7 : ConcaveOn ℝ (Set.Iio (-(1 : ℝ))) y)
  (h8 : ConcaveOn ℝ (Set.Ioi 1) y)
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 2 (fun t => y t) x) = 0) ↔ ((x = (-(1 : ℝ))) ∨ (x = 1))))) := by
  sorry

theorem proof_gap_exercise_1305_9
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (Real.log (1 + (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = ((2 * x) /. (1 + (x ^ (2 : ℕ))))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => y t) x) = ((2 * (1 - (x ^ (2 : ℕ)))) /. ((1 + (x ^ (2 : ℕ))) ^ (2 : ℕ)))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((iteratedDeriv 2 (fun t => y t) x) > 0))))
  (h5 : ConvexOn ℝ (Set.Ioo (-(1 : ℝ)) 1) y)
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| > 1)) → ((iteratedDeriv 2 (fun t => y t) x) < 0))))
  (h7 : ConcaveOn ℝ (Set.Iio (-(1 : ℝ))) y)
  (h8 : ConcaveOn ℝ (Set.Ioi 1) y)
  (h9 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 2 (fun t => y t) x) = 0) ↔ ((x = (-(1 : ℝ))) ∨ (x = 1))))))
  : ({p | (exists (x : ℝ), p = (x, (y x)) ∧ (x ∈ (Set.univ : Set ℝ)) ∧ ((iteratedDeriv 2 (fun t => y t) x) = 0))}) = ({x | x = ((-(1 : ℝ)), (Real.log (2 : ℝ))) ∨ x = (1, (Real.log (2 : ℝ)))}) := by
  sorry

theorem proof_gap_exercise_1305_10
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (Real.log (1 + (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = ((2 * x) /. (1 + (x ^ (2 : ℕ))))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => y t) x) = ((2 * (1 - (x ^ (2 : ℕ)))) /. ((1 + (x ^ (2 : ℕ))) ^ (2 : ℕ)))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((iteratedDeriv 2 (fun t => y t) x) > 0))))
  (h5 : ConvexOn ℝ (Set.Ioo (-(1 : ℝ)) 1) y)
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| > 1)) → ((iteratedDeriv 2 (fun t => y t) x) < 0))))
  (h7 : ConcaveOn ℝ (Set.Iio (-(1 : ℝ))) y)
  (h8 : ConcaveOn ℝ (Set.Ioi 1) y)
  (h9 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 2 (fun t => y t) x) = 0) ↔ ((x = (-(1 : ℝ))) ∨ (x = 1))))))
  (h10 : ({p | (exists (x : ℝ), p = (x, (y x)) ∧ (x ∈ (Set.univ : Set ℝ)) ∧ ((iteratedDeriv 2 (fun t => y t) x) = 0))}) = ({x | x = ((-(1 : ℝ)), (Real.log (2 : ℝ))) ∨ x = (1, (Real.log (2 : ℝ)))}))
  : (forall (x : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (ConvexOn ℝ (Set.Ioo (-(1 : ℝ)) 1) y)) ∧ (ConcaveOn ℝ (Set.Iio (-(1 : ℝ))) y)) ∧ (ConcaveOn ℝ (Set.Ioi 1) y)) ∧ (({p | (exists (x_1 : ℝ), p = (x_1, (y x_1)) ∧ (x_1 ∈ (Set.univ : Set ℝ)) ∧ ((iteratedDeriv 2 (fun t => y t) x_1) = 0))}) = ({x | x = ((-(1 : ℝ)), (Real.log (2 : ℝ))) ∨ x = (1, (Real.log (2 : ℝ)))}))) → ((((ConvexOn ℝ (Set.Ioo (-(1 : ℝ)) 1) y) ∧ (ConcaveOn ℝ (Set.Iio (-(1 : ℝ))) y)) ∧ (ConcaveOn ℝ (Set.Ioi 1) y)) ∧ (((iteratedDeriv 2 (fun t => y t) x) = 0) ↔ ((x = (-(1 : ℝ))) ∨ (x = 1)))))) := by
  sorry

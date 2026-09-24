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

-- exercise: exercise_844

theorem proof_gap_exercise_844_1
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (d : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : d ∈ (Set.univ : Set ℝ))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((y x) = (((1 /. x) + (2 /. (x ^ (2 : ℕ)))) + (3 /. (x ^ (3 : ℕ))))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((iteratedDeriv 1 (fun t => (((a * t) + b) /. ((c * t) + d))) x) = (((a * ((c * x) + d)) - (c * ((a * x) + b))) /. (((c * x) + d) ^ (2 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_844_2
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (d : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : d ∈ (Set.univ : Set ℝ))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((y x) = (((1 /. x) + (2 /. (x ^ (2 : ℕ)))) + (3 /. (x ^ (3 : ℕ))))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((iteratedDeriv 1 (fun t => (((a * t) + b) /. ((c * t) + d))) x) = (((a * ((c * x) + d)) - (c * ((a * x) + b))) /. (((c * x) + d) ^ (2 : ℕ)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((((a * ((c * x) + d)) - (c * ((a * x) + b))) /. (((c * x) + d) ^ (2 : ℕ))) = (((a * d) - (b * c)) /. (((c * x) + d) ^ (2 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_844_3
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (d : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : d ∈ (Set.univ : Set ℝ))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((y x) = (((1 /. x) + (2 /. (x ^ (2 : ℕ)))) + (3 /. (x ^ (3 : ℕ))))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((iteratedDeriv 1 (fun t => (((a * t) + b) /. ((c * t) + d))) x) = (((a * ((c * x) + d)) - (c * ((a * x) + b))) /. (((c * x) + d) ^ (2 : ℕ)))))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((((a * ((c * x) + d)) - (c * ((a * x) + b))) /. (((c * x) + d) ^ (2 : ℕ))) = (((a * d) - (b * c)) /. (((c * x) + d) ^ (2 : ℕ)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((iteratedDeriv 1 (fun t => (((a * t) + b) /. ((c * t) + d))) x) = (((a * d) - (b * c)) /. (((c * x) + d) ^ (2 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_844_4
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (d : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : d ∈ (Set.univ : Set ℝ))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((y x) = (((1 /. x) + (2 /. (x ^ (2 : ℕ)))) + (3 /. (x ^ (3 : ℕ))))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((iteratedDeriv 1 (fun t => (((a * t) + b) /. ((c * t) + d))) x) = (((a * ((c * x) + d)) - (c * ((a * x) + b))) /. (((c * x) + d) ^ (2 : ℕ)))))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((((a * ((c * x) + d)) - (c * ((a * x) + b))) /. (((c * x) + d) ^ (2 : ℕ))) = (((a * d) - (b * c)) /. (((c * x) + d) ^ (2 : ℕ)))))))
  (h8 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((iteratedDeriv 1 (fun t => (((a * t) + b) /. ((c * t) + d))) x) = (((a * d) - (b * c)) /. (((c * x) + d) ^ (2 : ℕ)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => y t) x) = (-(((1 /. (x ^ (2 : ℕ))) + (4 /. (x ^ (3 : ℕ)))) + (9 /. (x ^ (4 : ℕ)))))))) := by
  sorry

theorem proof_gap_exercise_844_5
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (d : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : d ∈ (Set.univ : Set ℝ))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((y x) = (((1 /. x) + (2 /. (x ^ (2 : ℕ)))) + (3 /. (x ^ (3 : ℕ))))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((iteratedDeriv 1 (fun t => (((a * t) + b) /. ((c * t) + d))) x) = (((a * ((c * x) + d)) - (c * ((a * x) + b))) /. (((c * x) + d) ^ (2 : ℕ)))))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((((a * ((c * x) + d)) - (c * ((a * x) + b))) /. (((c * x) + d) ^ (2 : ℕ))) = (((a * d) - (b * c)) /. (((c * x) + d) ^ (2 : ℕ)))))))
  (h8 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((iteratedDeriv 1 (fun t => (((a * t) + b) /. ((c * t) + d))) x) = (((a * d) - (b * c)) /. (((c * x) + d) ^ (2 : ℕ)))))))
  (h9 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => y t) x) = (-(((1 /. (x ^ (2 : ℕ))) + (4 /. (x ^ (3 : ℕ)))) + (9 /. (x ^ (4 : ℕ)))))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → (((iteratedDeriv 1 (fun t => (((a * t) + b) /. ((c * t) + d))) x) = (((a * d) - (b * c)) /. (((c * x) + d) ^ (2 : ℕ)))) ∧ ((x ≠ 0) → ((iteratedDeriv 1 (fun t => y t) x) = (-(((1 /. (x ^ (2 : ℕ))) + (4 /. (x ^ (3 : ℕ)))) + (9 /. (x ^ (4 : ℕ)))))))))) := by
  sorry

theorem proof_gap_exercise_844_6
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (d : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : d ∈ (Set.univ : Set ℝ))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((y x) = (((1 /. x) + (2 /. (x ^ (2 : ℕ)))) + (3 /. (x ^ (3 : ℕ))))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((iteratedDeriv 1 (fun t => (((a * t) + b) /. ((c * t) + d))) x) = (((a * ((c * x) + d)) - (c * ((a * x) + b))) /. (((c * x) + d) ^ (2 : ℕ)))))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((((a * ((c * x) + d)) - (c * ((a * x) + b))) /. (((c * x) + d) ^ (2 : ℕ))) = (((a * d) - (b * c)) /. (((c * x) + d) ^ (2 : ℕ)))))))
  (h8 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((iteratedDeriv 1 (fun t => (((a * t) + b) /. ((c * t) + d))) x) = (((a * d) - (b * c)) /. (((c * x) + d) ^ (2 : ℕ)))))))
  (h9 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => y t) x) = (-(((1 /. (x ^ (2 : ℕ))) + (4 /. (x ^ (3 : ℕ)))) + (9 /. (x ^ (4 : ℕ)))))))))
  (h10 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → (((iteratedDeriv 1 (fun t => (((a * t) + b) /. ((c * t) + d))) x) = (((a * d) - (b * c)) /. (((c * x) + d) ^ (2 : ℕ)))) ∧ ((x ≠ 0) → ((iteratedDeriv 1 (fun t => y t) x) = (-(((1 /. (x ^ (2 : ℕ))) + (4 /. (x ^ (3 : ℕ)))) + (9 /. (x ^ (4 : ℕ)))))))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → (((iteratedDeriv 1 (fun t => (((a * t) + b) /. ((c * t) + d))) x) = (((a * d) - (b * c)) /. (((c * x) + d) ^ (2 : ℕ)))) ∧ ((x ≠ 0) → ((iteratedDeriv 1 (fun t => y t) x) = (-(((1 /. (x ^ (2 : ℕ))) + (4 /. (x ^ (3 : ℕ)))) + (9 /. (x ^ (4 : ℕ)))))))))) := by
  sorry

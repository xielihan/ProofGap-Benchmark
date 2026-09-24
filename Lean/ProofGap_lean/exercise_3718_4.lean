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

-- exercise: exercise_3718_4

theorem proof_gap_exercise_3718_4_1
  (F : (ℝ -> ℝ))
  (f : (ℝ × ℝ -> ℝ))
  (u : (ℝ -> ℝ))
  (v : (ℝ -> ℝ))
  (h1 : D ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h2 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → ((F v_uCE_uB1) = (∫ x in (0 : ℝ)..v_uCE_uB1, ((f ((x + v_uCE_uB1), (x - v_uCE_uB1))) * (1 : ℝ)))))))
  (h3 : ContDiffOn ℝ (1 : ℕ∞) f D)
  (h4 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ v_uCE_uB1)) → (((x + v_uCE_uB1), (x - v_uCE_uB1)) ∈ D))))))
  (h5 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((u x) = (x + v_uCE_uB1)))))))
  (h6 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v x) = (x - v_uCE_uB1)))))))
  : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → ((F v_uCE_uB1) = (∫ x in (0 : ℝ)..v_uCE_uB1, ((f ((u x), (v x))) * (1 : ℝ)))))) := by
  sorry

theorem proof_gap_exercise_3718_4_2
  (F : (ℝ -> ℝ))
  (f : (ℝ × ℝ -> ℝ))
  (u : (ℝ -> ℝ))
  (v : (ℝ -> ℝ))
  (h1 : D ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h2 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → ((F v_uCE_uB1) = (∫ x in (0 : ℝ)..v_uCE_uB1, ((f ((x + v_uCE_uB1), (x - v_uCE_uB1))) * (1 : ℝ)))))))
  (h3 : ContDiffOn ℝ (1 : ℕ∞) f D)
  (h4 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ v_uCE_uB1)) → (((x + v_uCE_uB1), (x - v_uCE_uB1)) ∈ D))))))
  (h5 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((u x) = (x + v_uCE_uB1)))))))
  (h6 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v x) = (x - v_uCE_uB1)))))))
  (h7 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → ((F v_uCE_uB1) = (∫ x in (0 : ℝ)..v_uCE_uB1, ((f ((u x), (v x))) * (1 : ℝ)))))))
  : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F t) v_uCE_uB1) = ((f ((2 * v_uCE_uB1), (0 : ℝ))) + (∫ x in (0 : ℝ)..v_uCE_uB1, (((iteratedDeriv 1 (fun t => f (t, (v x))) (u x)) - (iteratedDeriv 1 (fun t => f ((u x), t)) (v x))) * (1 : ℝ))))))) := by
  sorry

theorem proof_gap_exercise_3718_4_3
  (F : (ℝ -> ℝ))
  (f : (ℝ × ℝ -> ℝ))
  (u : (ℝ -> ℝ))
  (v : (ℝ -> ℝ))
  (h1 : D ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h2 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → ((F v_uCE_uB1) = (∫ x in (0 : ℝ)..v_uCE_uB1, ((f ((x + v_uCE_uB1), (x - v_uCE_uB1))) * (1 : ℝ)))))))
  (h3 : ContDiffOn ℝ (1 : ℕ∞) f D)
  (h4 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ v_uCE_uB1)) → (((x + v_uCE_uB1), (x - v_uCE_uB1)) ∈ D))))))
  (h5 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((u x) = (x + v_uCE_uB1)))))))
  (h6 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v x) = (x - v_uCE_uB1)))))))
  (h7 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → ((F v_uCE_uB1) = (∫ x in (0 : ℝ)..v_uCE_uB1, ((f ((u x), (v x))) * (1 : ℝ)))))))
  (h8 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F t) v_uCE_uB1) = ((f ((2 * v_uCE_uB1), (0 : ℝ))) + (∫ x in (0 : ℝ)..v_uCE_uB1, (((iteratedDeriv 1 (fun t => f (t, (v x))) (u x)) - (iteratedDeriv 1 (fun t => f ((u x), t)) (v x))) * (1 : ℝ))))))))
  : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F t) v_uCE_uB1) = (((f ((2 * v_uCE_uB1), (0 : ℝ))) + (2 * (∫ x in (0 : ℝ)..v_uCE_uB1, ((iteratedDeriv 1 (fun t => f (t, (v x))) (u x)) * (1 : ℝ))))) - (∫ x in (0 : ℝ)..v_uCE_uB1, (((iteratedDeriv 1 (fun t => f (t, (v x))) (u x)) + (iteratedDeriv 1 (fun t => f ((u x), t)) (v x))) * (1 : ℝ))))))) := by
  sorry

theorem proof_gap_exercise_3718_4_4
  (F : (ℝ -> ℝ))
  (f : (ℝ × ℝ -> ℝ))
  (u : (ℝ -> ℝ))
  (v : (ℝ -> ℝ))
  (h1 : D ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h2 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → ((F v_uCE_uB1) = (∫ x in (0 : ℝ)..v_uCE_uB1, ((f ((x + v_uCE_uB1), (x - v_uCE_uB1))) * (1 : ℝ)))))))
  (h3 : ContDiffOn ℝ (1 : ℕ∞) f D)
  (h4 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ v_uCE_uB1)) → (((x + v_uCE_uB1), (x - v_uCE_uB1)) ∈ D))))))
  (h5 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((u x) = (x + v_uCE_uB1)))))))
  (h6 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v x) = (x - v_uCE_uB1)))))))
  (h7 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → ((F v_uCE_uB1) = (∫ x in (0 : ℝ)..v_uCE_uB1, ((f ((u x), (v x))) * (1 : ℝ)))))))
  (h8 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F t) v_uCE_uB1) = ((f ((2 * v_uCE_uB1), (0 : ℝ))) + (∫ x in (0 : ℝ)..v_uCE_uB1, (((iteratedDeriv 1 (fun t => f (t, (v x))) (u x)) - (iteratedDeriv 1 (fun t => f ((u x), t)) (v x))) * (1 : ℝ))))))))
  (h9 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F t) v_uCE_uB1) = (((f ((2 * v_uCE_uB1), (0 : ℝ))) + (2 * (∫ x in (0 : ℝ)..v_uCE_uB1, ((iteratedDeriv 1 (fun t => f (t, (v x))) (u x)) * (1 : ℝ))))) - (∫ x in (0 : ℝ)..v_uCE_uB1, (((iteratedDeriv 1 (fun t => f (t, (v x))) (u x)) + (iteratedDeriv 1 (fun t => f ((u x), t)) (v x))) * (1 : ℝ))))))))
  : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F t) v_uCE_uB1) = (((f ((2 * v_uCE_uB1), (0 : ℝ))) + (2 * (∫ x in (0 : ℝ)..v_uCE_uB1, ((iteratedDeriv 1 (fun t => f (t, (v x))) (u x)) * (1 : ℝ))))) - (∫ x in (0 : ℝ)..v_uCE_uB1, ((iteratedDeriv 1 (fun t => (f ((u t), (v t)))) x) * (1 : ℝ))))))) := by
  sorry

theorem proof_gap_exercise_3718_4_5
  (F : (ℝ -> ℝ))
  (f : (ℝ × ℝ -> ℝ))
  (u : (ℝ -> ℝ))
  (v : (ℝ -> ℝ))
  (h1 : D ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h2 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → ((F v_uCE_uB1) = (∫ x in (0 : ℝ)..v_uCE_uB1, ((f ((x + v_uCE_uB1), (x - v_uCE_uB1))) * (1 : ℝ)))))))
  (h3 : ContDiffOn ℝ (1 : ℕ∞) f D)
  (h4 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ v_uCE_uB1)) → (((x + v_uCE_uB1), (x - v_uCE_uB1)) ∈ D))))))
  (h5 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((u x) = (x + v_uCE_uB1)))))))
  (h6 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v x) = (x - v_uCE_uB1)))))))
  (h7 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → ((F v_uCE_uB1) = (∫ x in (0 : ℝ)..v_uCE_uB1, ((f ((u x), (v x))) * (1 : ℝ)))))))
  (h8 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F t) v_uCE_uB1) = ((f ((2 * v_uCE_uB1), (0 : ℝ))) + (∫ x in (0 : ℝ)..v_uCE_uB1, (((iteratedDeriv 1 (fun t => f (t, (v x))) (u x)) - (iteratedDeriv 1 (fun t => f ((u x), t)) (v x))) * (1 : ℝ))))))))
  (h9 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F t) v_uCE_uB1) = (((f ((2 * v_uCE_uB1), (0 : ℝ))) + (2 * (∫ x in (0 : ℝ)..v_uCE_uB1, ((iteratedDeriv 1 (fun t => f (t, (v x))) (u x)) * (1 : ℝ))))) - (∫ x in (0 : ℝ)..v_uCE_uB1, (((iteratedDeriv 1 (fun t => f (t, (v x))) (u x)) + (iteratedDeriv 1 (fun t => f ((u x), t)) (v x))) * (1 : ℝ))))))))
  (h10 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F t) v_uCE_uB1) = (((f ((2 * v_uCE_uB1), (0 : ℝ))) + (2 * (∫ x in (0 : ℝ)..v_uCE_uB1, ((iteratedDeriv 1 (fun t => f (t, (v x))) (u x)) * (1 : ℝ))))) - (∫ x in (0 : ℝ)..v_uCE_uB1, ((iteratedDeriv 1 (fun t => (f ((u t), (v t)))) x) * (1 : ℝ))))))))
  : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F t) v_uCE_uB1) = (((f ((2 * v_uCE_uB1), (0 : ℝ))) + (2 * (∫ x in (0 : ℝ)..v_uCE_uB1, ((iteratedDeriv 1 (fun t => f (t, (v x))) (u x)) * (1 : ℝ))))) - ((f ((2 * v_uCE_uB1), (0 : ℝ))) - (f (v_uCE_uB1, (-v_uCE_uB1)))))))) := by
  sorry

theorem proof_gap_exercise_3718_4_6
  (F : (ℝ -> ℝ))
  (f : (ℝ × ℝ -> ℝ))
  (u : (ℝ -> ℝ))
  (v : (ℝ -> ℝ))
  (h1 : D ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h2 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → ((F v_uCE_uB1) = (∫ x in (0 : ℝ)..v_uCE_uB1, ((f ((x + v_uCE_uB1), (x - v_uCE_uB1))) * (1 : ℝ)))))))
  (h3 : ContDiffOn ℝ (1 : ℕ∞) f D)
  (h4 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ v_uCE_uB1)) → (((x + v_uCE_uB1), (x - v_uCE_uB1)) ∈ D))))))
  (h5 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((u x) = (x + v_uCE_uB1)))))))
  (h6 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v x) = (x - v_uCE_uB1)))))))
  (h7 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → ((F v_uCE_uB1) = (∫ x in (0 : ℝ)..v_uCE_uB1, ((f ((u x), (v x))) * (1 : ℝ)))))))
  (h8 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F t) v_uCE_uB1) = ((f ((2 * v_uCE_uB1), (0 : ℝ))) + (∫ x in (0 : ℝ)..v_uCE_uB1, (((iteratedDeriv 1 (fun t => f (t, (v x))) (u x)) - (iteratedDeriv 1 (fun t => f ((u x), t)) (v x))) * (1 : ℝ))))))))
  (h9 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F t) v_uCE_uB1) = (((f ((2 * v_uCE_uB1), (0 : ℝ))) + (2 * (∫ x in (0 : ℝ)..v_uCE_uB1, ((iteratedDeriv 1 (fun t => f (t, (v x))) (u x)) * (1 : ℝ))))) - (∫ x in (0 : ℝ)..v_uCE_uB1, (((iteratedDeriv 1 (fun t => f (t, (v x))) (u x)) + (iteratedDeriv 1 (fun t => f ((u x), t)) (v x))) * (1 : ℝ))))))))
  (h10 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F t) v_uCE_uB1) = (((f ((2 * v_uCE_uB1), (0 : ℝ))) + (2 * (∫ x in (0 : ℝ)..v_uCE_uB1, ((iteratedDeriv 1 (fun t => f (t, (v x))) (u x)) * (1 : ℝ))))) - (∫ x in (0 : ℝ)..v_uCE_uB1, ((iteratedDeriv 1 (fun t => (f ((u t), (v t)))) x) * (1 : ℝ))))))))
  (h11 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F t) v_uCE_uB1) = (((f ((2 * v_uCE_uB1), (0 : ℝ))) + (2 * (∫ x in (0 : ℝ)..v_uCE_uB1, ((iteratedDeriv 1 (fun t => f (t, (v x))) (u x)) * (1 : ℝ))))) - ((f ((2 * v_uCE_uB1), (0 : ℝ))) - (f (v_uCE_uB1, (-v_uCE_uB1)))))))))
  : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F t) v_uCE_uB1) = ((f (v_uCE_uB1, (-v_uCE_uB1))) + (2 * (∫ x in (0 : ℝ)..v_uCE_uB1, ((iteratedDeriv 1 (fun t => f (t, (v x))) (u x)) * (1 : ℝ)))))))) := by
  sorry

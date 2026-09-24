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

-- exercise: exercise_3387

theorem proof_gap_exercise_3387_1
  (z : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h2 : (forall (y : ℝ), (y ∈ (Set.univ : Set ℝ))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → ((z (x, y)) ∈ (Set.univ : Set ℝ)))))))
  (h4 : ContDiff ℝ (2 : ℕ∞) z)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → (((x + y) + (z (x, y))) = (Real.exp (-((x + y) + (z (x, y)))))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → ((1 + (iteratedDeriv 1 (fun t => z (t, y)) x)) = ((Real.exp (-((x + y) + (z (x, y))))) * ((-(1 : ℝ)) - (iteratedDeriv 1 (fun t => z (t, y)) x)))))))) := by
  sorry

theorem proof_gap_exercise_3387_2
  (z : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h2 : (forall (y : ℝ), (y ∈ (Set.univ : Set ℝ))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → ((z (x, y)) ∈ (Set.univ : Set ℝ)))))))
  (h4 : ContDiff ℝ (2 : ℕ∞) z)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → (((x + y) + (z (x, y))) = (Real.exp (-((x + y) + (z (x, y)))))))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → ((1 + (iteratedDeriv 1 (fun t => z (t, y)) x)) = ((Real.exp (-((x + y) + (z (x, y))))) * ((-(1 : ℝ)) - (iteratedDeriv 1 (fun t => z (t, y)) x)))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => z (t, y)) x) = (-(1 : ℝ))))))) := by
  sorry

theorem proof_gap_exercise_3387_3
  (z : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h2 : (forall (y : ℝ), (y ∈ (Set.univ : Set ℝ))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → ((z (x, y)) ∈ (Set.univ : Set ℝ)))))))
  (h4 : ContDiff ℝ (2 : ℕ∞) z)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → (((x + y) + (z (x, y))) = (Real.exp (-((x + y) + (z (x, y)))))))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → ((1 + (iteratedDeriv 1 (fun t => z (t, y)) x)) = ((Real.exp (-((x + y) + (z (x, y))))) * ((-(1 : ℝ)) - (iteratedDeriv 1 (fun t => z (t, y)) x)))))))))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => z (t, y)) x) = (-(1 : ℝ))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => z (x, t)) y) = (-(1 : ℝ))))))) := by
  sorry

theorem proof_gap_exercise_3387_4
  (z : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h2 : (forall (y : ℝ), (y ∈ (Set.univ : Set ℝ))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → ((z (x, y)) ∈ (Set.univ : Set ℝ)))))))
  (h4 : ContDiff ℝ (2 : ℕ∞) z)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → (((x + y) + (z (x, y))) = (Real.exp (-((x + y) + (z (x, y)))))))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → ((1 + (iteratedDeriv 1 (fun t => z (t, y)) x)) = ((Real.exp (-((x + y) + (z (x, y))))) * ((-(1 : ℝ)) - (iteratedDeriv 1 (fun t => z (t, y)) x)))))))))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => z (t, y)) x) = (-(1 : ℝ))))))))
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => z (x, t)) y) = (-(1 : ℝ))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => z (t, y)) x) = 0))))) := by
  sorry

theorem proof_gap_exercise_3387_5
  (z : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h2 : (forall (y : ℝ), (y ∈ (Set.univ : Set ℝ))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → ((z (x, y)) ∈ (Set.univ : Set ℝ)))))))
  (h4 : ContDiff ℝ (2 : ℕ∞) z)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → (((x + y) + (z (x, y))) = (Real.exp (-((x + y) + (z (x, y)))))))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → ((1 + (iteratedDeriv 1 (fun t => z (t, y)) x)) = ((Real.exp (-((x + y) + (z (x, y))))) * ((-(1 : ℝ)) - (iteratedDeriv 1 (fun t => z (t, y)) x)))))))))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => z (t, y)) x) = (-(1 : ℝ))))))))
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => z (x, t)) y) = (-(1 : ℝ))))))))
  (h9 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => z (t, y)) x) = 0))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => z (t, p.2)) p.1)) (x, t)) y) = 0))))) := by
  sorry

theorem proof_gap_exercise_3387_6
  (z : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h2 : (forall (y : ℝ), (y ∈ (Set.univ : Set ℝ))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → ((z (x, y)) ∈ (Set.univ : Set ℝ)))))))
  (h4 : ContDiff ℝ (2 : ℕ∞) z)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → (((x + y) + (z (x, y))) = (Real.exp (-((x + y) + (z (x, y)))))))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → ((1 + (iteratedDeriv 1 (fun t => z (t, y)) x)) = ((Real.exp (-((x + y) + (z (x, y))))) * ((-(1 : ℝ)) - (iteratedDeriv 1 (fun t => z (t, y)) x)))))))))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => z (t, y)) x) = (-(1 : ℝ))))))))
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => z (x, t)) y) = (-(1 : ℝ))))))))
  (h9 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => z (t, y)) x) = 0))))))
  (h10 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => z (t, p.2)) p.1)) (x, t)) y) = 0))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => z (x, t)) y) = 0))))) := by
  sorry

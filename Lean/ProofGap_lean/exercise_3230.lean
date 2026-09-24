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

-- exercise: exercise_3230

theorem proof_gap_exercise_3230_1
  (f : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((f (x, y)) = (if (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) ≠ 0) then ((x * y) * (((x ^ (2 : ℕ)) - (y ^ (2 : ℕ))) /. ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))))) else (if (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) = 0) then 0 else 0))))))
  : (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → (∃ L : ℝ, Tendsto (fun x : ℝ => ((((x * y) * (((x ^ (2 : ℕ)) - (y ^ (2 : ℕ))) /. ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))))) - 0) /. x)) (𝓝[≠] 0) (𝓝 L) ∧ ((Tendsto (fun x : ℝ => (((f (x, y)) - (f ((0 : ℝ), y))) /. x)) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((x * y) * (((x ^ (2 : ℕ)) - (y ^ (2 : ℕ))) /. ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))))) - 0) /. x))))) ∧ (Tendsto (fun x : ℝ => ((((x * y) * (((x ^ (2 : ℕ)) - (y ^ (2 : ℕ))) /. ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))))) - 0) /. x)) (𝓝[≠] 0) (𝓝 (-y))))))) := by
  sorry

theorem proof_gap_exercise_3230_2
  (f : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((f (x, y)) = (if (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) ≠ 0) then ((x * y) * (((x ^ (2 : ℕ)) - (y ^ (2 : ℕ))) /. ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))))) else (if (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) = 0) then 0 else 0))))))
  (h2 : (forall (y : ℝ), (∃ L : ℝ, Tendsto (fun x : ℝ => ((((x * y) * (((x ^ (2 : ℕ)) - (y ^ (2 : ℕ))) /. ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))))) - 0) /. x)) (𝓝[≠] 0) (𝓝 L) ∧ ((y ∈ (Set.univ : Set ℝ)) → ((Tendsto (fun x : ℝ => (((f (x, y)) - (f ((0 : ℝ), y))) /. x)) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((x * y) * (((x ^ (2 : ℕ)) - (y ^ (2 : ℕ))) /. ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))))) - 0) /. x))))) ∧ (Tendsto (fun x : ℝ => ((((x * y) * (((x ^ (2 : ℕ)) - (y ^ (2 : ℕ))) /. ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))))) - 0) /. x)) (𝓝[≠] 0) (𝓝 (-y))))))))
  : (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => f (t, y)) 0) = (-y)))) := by
  sorry

theorem proof_gap_exercise_3230_3
  (f : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((f (x, y)) = (if (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) ≠ 0) then ((x * y) * (((x ^ (2 : ℕ)) - (y ^ (2 : ℕ))) /. ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))))) else (if (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) = 0) then 0 else 0))))))
  (h2 : (forall (y : ℝ), (∃ L : ℝ, Tendsto (fun x : ℝ => ((((x * y) * (((x ^ (2 : ℕ)) - (y ^ (2 : ℕ))) /. ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))))) - 0) /. x)) (𝓝[≠] 0) (𝓝 L) ∧ ((y ∈ (Set.univ : Set ℝ)) → ((Tendsto (fun x : ℝ => (((f (x, y)) - (f ((0 : ℝ), y))) /. x)) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((x * y) * (((x ^ (2 : ℕ)) - (y ^ (2 : ℕ))) /. ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))))) - 0) /. x))))) ∧ (Tendsto (fun x : ℝ => ((((x * y) * (((x ^ (2 : ℕ)) - (y ^ (2 : ℕ))) /. ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))))) - 0) /. x)) (𝓝[≠] 0) (𝓝 (-y))))))))
  (h3 : (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => f (t, y)) 0) = (-y)))))
  : (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => f (t, p.2)) p.1)) (0, t)) 0) = (-(1 : ℝ)) := by
  sorry

theorem proof_gap_exercise_3230_4
  (f : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((f (x, y)) = (if (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) ≠ 0) then ((x * y) * (((x ^ (2 : ℕ)) - (y ^ (2 : ℕ))) /. ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))))) else (if (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) = 0) then 0 else 0))))))
  (h2 : (forall (y : ℝ), (∃ L : ℝ, Tendsto (fun x : ℝ => ((((x * y) * (((x ^ (2 : ℕ)) - (y ^ (2 : ℕ))) /. ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))))) - 0) /. x)) (𝓝[≠] 0) (𝓝 L) ∧ ((y ∈ (Set.univ : Set ℝ)) → ((Tendsto (fun x : ℝ => (((f (x, y)) - (f ((0 : ℝ), y))) /. x)) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((x * y) * (((x ^ (2 : ℕ)) - (y ^ (2 : ℕ))) /. ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))))) - 0) /. x))))) ∧ (Tendsto (fun x : ℝ => ((((x * y) * (((x ^ (2 : ℕ)) - (y ^ (2 : ℕ))) /. ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))))) - 0) /. x)) (𝓝[≠] 0) (𝓝 (-y))))))))
  (h3 : (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => f (t, y)) 0) = (-y)))))
  (h4 : (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => f (t, p.2)) p.1)) (0, t)) 0) = (-(1 : ℝ)))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => f (x, t)) 0) = x))) := by
  sorry

theorem proof_gap_exercise_3230_5
  (f : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((f (x, y)) = (if (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) ≠ 0) then ((x * y) * (((x ^ (2 : ℕ)) - (y ^ (2 : ℕ))) /. ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))))) else (if (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) = 0) then 0 else 0))))))
  (h2 : (forall (y : ℝ), (∃ L : ℝ, Tendsto (fun x : ℝ => ((((x * y) * (((x ^ (2 : ℕ)) - (y ^ (2 : ℕ))) /. ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))))) - 0) /. x)) (𝓝[≠] 0) (𝓝 L) ∧ ((y ∈ (Set.univ : Set ℝ)) → ((Tendsto (fun x : ℝ => (((f (x, y)) - (f ((0 : ℝ), y))) /. x)) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((x * y) * (((x ^ (2 : ℕ)) - (y ^ (2 : ℕ))) /. ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))))) - 0) /. x))))) ∧ (Tendsto (fun x : ℝ => ((((x * y) * (((x ^ (2 : ℕ)) - (y ^ (2 : ℕ))) /. ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))))) - 0) /. x)) (𝓝[≠] 0) (𝓝 (-y))))))))
  (h3 : (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => f (t, y)) 0) = (-y)))))
  (h4 : (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => f (t, p.2)) p.1)) (0, t)) 0) = (-(1 : ℝ)))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => f (x, t)) 0) = x))))
  : (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => f (p.1, t)) p.2)) (t, 0)) 0) = 1 := by
  sorry

theorem proof_gap_exercise_3230_6
  (f : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((f (x, y)) = (if (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) ≠ 0) then ((x * y) * (((x ^ (2 : ℕ)) - (y ^ (2 : ℕ))) /. ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))))) else (if (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) = 0) then 0 else 0))))))
  (h2 : (forall (y : ℝ), (∃ L : ℝ, Tendsto (fun x : ℝ => ((((x * y) * (((x ^ (2 : ℕ)) - (y ^ (2 : ℕ))) /. ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))))) - 0) /. x)) (𝓝[≠] 0) (𝓝 L) ∧ ((y ∈ (Set.univ : Set ℝ)) → ((Tendsto (fun x : ℝ => (((f (x, y)) - (f ((0 : ℝ), y))) /. x)) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((x * y) * (((x ^ (2 : ℕ)) - (y ^ (2 : ℕ))) /. ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))))) - 0) /. x))))) ∧ (Tendsto (fun x : ℝ => ((((x * y) * (((x ^ (2 : ℕ)) - (y ^ (2 : ℕ))) /. ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))))) - 0) /. x)) (𝓝[≠] 0) (𝓝 (-y))))))))
  (h3 : (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => f (t, y)) 0) = (-y)))))
  (h4 : (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => f (t, p.2)) p.1)) (0, t)) 0) = (-(1 : ℝ)))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => f (x, t)) 0) = x))))
  (h6 : (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => f (p.1, t)) p.2)) (t, 0)) 0) = 1)
  : (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => f (t, p.2)) p.1)) (0, t)) 0) ≠ (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => f (p.1, t)) p.2)) (t, 0)) 0) := by
  sorry

theorem proof_gap_exercise_3230_7
  (f : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((f (x, y)) = (if (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) ≠ 0) then ((x * y) * (((x ^ (2 : ℕ)) - (y ^ (2 : ℕ))) /. ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))))) else (if (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) = 0) then 0 else 0))))))
  (h2 : (forall (y : ℝ), (∃ L : ℝ, Tendsto (fun x : ℝ => ((((x * y) * (((x ^ (2 : ℕ)) - (y ^ (2 : ℕ))) /. ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))))) - 0) /. x)) (𝓝[≠] 0) (𝓝 L) ∧ ((y ∈ (Set.univ : Set ℝ)) → ((Tendsto (fun x : ℝ => (((f (x, y)) - (f ((0 : ℝ), y))) /. x)) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((x * y) * (((x ^ (2 : ℕ)) - (y ^ (2 : ℕ))) /. ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))))) - 0) /. x))))) ∧ (Tendsto (fun x : ℝ => ((((x * y) * (((x ^ (2 : ℕ)) - (y ^ (2 : ℕ))) /. ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))))) - 0) /. x)) (𝓝[≠] 0) (𝓝 (-y))))))))
  (h3 : (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => f (t, y)) 0) = (-y)))))
  (h4 : (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => f (t, p.2)) p.1)) (0, t)) 0) = (-(1 : ℝ)))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => f (x, t)) 0) = x))))
  (h6 : (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => f (p.1, t)) p.2)) (t, 0)) 0) = 1)
  (h7 : (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => f (t, p.2)) p.1)) (0, t)) 0) ≠ (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => f (p.1, t)) p.2)) (t, 0)) 0))
  : (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => f (t, p.2)) p.1)) (0, t)) 0) ≠ (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => f (p.1, t)) p.2)) (t, 0)) 0) := by
  sorry

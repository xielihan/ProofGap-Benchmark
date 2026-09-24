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

-- exercise: exercise_3624

theorem proof_gap_exercise_3624_1
  (z : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((z (x, y)) = (((((x ^ (2 : ℕ)) - (x * y)) + (y ^ (2 : ℕ))) - (2 * x)) + y)))))
  : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => z (t, y)) x) = (((2 * x) - y) - 2)))) := by
  sorry

theorem proof_gap_exercise_3624_2
  (z : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((z (x, y)) = (((((x ^ (2 : ℕ)) - (x * y)) + (y ^ (2 : ℕ))) - (2 * x)) + y)))))
  (h2 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => z (t, y)) x) = (((2 * x) - y) - 2)))))
  : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => z (x, t)) y) = (((-x) + (2 * y)) + 1)))) := by
  sorry

theorem proof_gap_exercise_3624_3
  (z : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((z (x, y)) = (((((x ^ (2 : ℕ)) - (x * y)) + (y ^ (2 : ℕ))) - (2 * x)) + y)))))
  (h2 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => z (t, y)) x) = (((2 * x) - y) - 2)))))
  (h3 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => z (x, t)) y) = (((-x) + (2 * y)) + 1)))))
  : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((((iteratedDeriv 1 (fun t => z (t, y)) x) = 0) ∧ ((iteratedDeriv 1 (fun t => z (x, t)) y) = 0)) ↔ ((x, y) = (1, 0))))) := by
  sorry

theorem proof_gap_exercise_3624_4
  (z : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((z (x, y)) = (((((x ^ (2 : ℕ)) - (x * y)) + (y ^ (2 : ℕ))) - (2 * x)) + y)))))
  (h2 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => z (t, y)) x) = (((2 * x) - y) - 2)))))
  (h3 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => z (x, t)) y) = (((-x) + (2 * y)) + 1)))))
  (h4 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((((iteratedDeriv 1 (fun t => z (t, y)) x) = 0) ∧ ((iteratedDeriv 1 (fun t => z (x, t)) y) = 0)) ↔ ((x, y) = (1, 0))))))
  (h5 : A = (iteratedDeriv 2 (fun t => z (t, (0 : ℝ))) 1))
  (h6 : B = (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => z (t, p.2)) p.1)) (1, t)) 0))
  (h7 : C = (iteratedDeriv 2 (fun t => z ((1 : ℝ), t)) 0))
  : A = 2 := by
  sorry

theorem proof_gap_exercise_3624_5
  (z : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((z (x, y)) = (((((x ^ (2 : ℕ)) - (x * y)) + (y ^ (2 : ℕ))) - (2 * x)) + y)))))
  (h2 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => z (t, y)) x) = (((2 * x) - y) - 2)))))
  (h3 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => z (x, t)) y) = (((-x) + (2 * y)) + 1)))))
  (h4 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((((iteratedDeriv 1 (fun t => z (t, y)) x) = 0) ∧ ((iteratedDeriv 1 (fun t => z (x, t)) y) = 0)) ↔ ((x, y) = (1, 0))))))
  (h5 : A = (iteratedDeriv 2 (fun t => z (t, (0 : ℝ))) 1))
  (h6 : B = (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => z (t, p.2)) p.1)) (1, t)) 0))
  (h7 : C = (iteratedDeriv 2 (fun t => z ((1 : ℝ), t)) 0))
  (h8 : A = 2)
  : B = (-(1 : ℝ)) := by
  sorry

theorem proof_gap_exercise_3624_6
  (z : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((z (x, y)) = (((((x ^ (2 : ℕ)) - (x * y)) + (y ^ (2 : ℕ))) - (2 * x)) + y)))))
  (h2 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => z (t, y)) x) = (((2 * x) - y) - 2)))))
  (h3 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => z (x, t)) y) = (((-x) + (2 * y)) + 1)))))
  (h4 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((((iteratedDeriv 1 (fun t => z (t, y)) x) = 0) ∧ ((iteratedDeriv 1 (fun t => z (x, t)) y) = 0)) ↔ ((x, y) = (1, 0))))))
  (h5 : A = (iteratedDeriv 2 (fun t => z (t, (0 : ℝ))) 1))
  (h6 : B = (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => z (t, p.2)) p.1)) (1, t)) 0))
  (h7 : C = (iteratedDeriv 2 (fun t => z ((1 : ℝ), t)) 0))
  (h8 : A = 2)
  (h9 : B = (-(1 : ℝ)))
  : C = 2 := by
  sorry

theorem proof_gap_exercise_3624_7
  (z : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((z (x, y)) = (((((x ^ (2 : ℕ)) - (x * y)) + (y ^ (2 : ℕ))) - (2 * x)) + y)))))
  (h2 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => z (t, y)) x) = (((2 * x) - y) - 2)))))
  (h3 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => z (x, t)) y) = (((-x) + (2 * y)) + 1)))))
  (h4 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((((iteratedDeriv 1 (fun t => z (t, y)) x) = 0) ∧ ((iteratedDeriv 1 (fun t => z (x, t)) y) = 0)) ↔ ((x, y) = (1, 0))))))
  (h5 : A = (iteratedDeriv 2 (fun t => z (t, (0 : ℝ))) 1))
  (h6 : B = (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => z (t, p.2)) p.1)) (1, t)) 0))
  (h7 : C = (iteratedDeriv 2 (fun t => z ((1 : ℝ), t)) 0))
  (h8 : A = 2)
  (h9 : B = (-(1 : ℝ)))
  (h10 : C = 2)
  : ((A * C) - (B ^ (2 : ℕ))) = 3 := by
  sorry

theorem proof_gap_exercise_3624_8
  (z : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((z (x, y)) = (((((x ^ (2 : ℕ)) - (x * y)) + (y ^ (2 : ℕ))) - (2 * x)) + y)))))
  (h2 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => z (t, y)) x) = (((2 * x) - y) - 2)))))
  (h3 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => z (x, t)) y) = (((-x) + (2 * y)) + 1)))))
  (h4 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((((iteratedDeriv 1 (fun t => z (t, y)) x) = 0) ∧ ((iteratedDeriv 1 (fun t => z (x, t)) y) = 0)) ↔ ((x, y) = (1, 0))))))
  (h5 : A = (iteratedDeriv 2 (fun t => z (t, (0 : ℝ))) 1))
  (h6 : B = (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => z (t, p.2)) p.1)) (1, t)) 0))
  (h7 : C = (iteratedDeriv 2 (fun t => z ((1 : ℝ), t)) 0))
  (h8 : A = 2)
  (h9 : B = (-(1 : ℝ)))
  (h10 : C = 2)
  (h11 : ((A * C) - (B ^ (2 : ℕ))) = 3)
  : 3 > 0 := by
  sorry

theorem proof_gap_exercise_3624_9
  (z : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((z (x, y)) = (((((x ^ (2 : ℕ)) - (x * y)) + (y ^ (2 : ℕ))) - (2 * x)) + y)))))
  (h2 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => z (t, y)) x) = (((2 * x) - y) - 2)))))
  (h3 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => z (x, t)) y) = (((-x) + (2 * y)) + 1)))))
  (h4 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((((iteratedDeriv 1 (fun t => z (t, y)) x) = 0) ∧ ((iteratedDeriv 1 (fun t => z (x, t)) y) = 0)) ↔ ((x, y) = (1, 0))))))
  (h5 : A = (iteratedDeriv 2 (fun t => z (t, (0 : ℝ))) 1))
  (h6 : B = (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => z (t, p.2)) p.1)) (1, t)) 0))
  (h7 : C = (iteratedDeriv 2 (fun t => z ((1 : ℝ), t)) 0))
  (h8 : A = 2)
  (h9 : B = (-(1 : ℝ)))
  (h10 : C = 2)
  (h11 : ((A * C) - (B ^ (2 : ℕ))) = 3)
  (h12 : 3 > 0)
  : ((A * C) - (B ^ (2 : ℕ))) > 0 := by
  sorry

theorem proof_gap_exercise_3624_10
  (z : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((z (x, y)) = (((((x ^ (2 : ℕ)) - (x * y)) + (y ^ (2 : ℕ))) - (2 * x)) + y)))))
  (h2 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => z (t, y)) x) = (((2 * x) - y) - 2)))))
  (h3 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => z (x, t)) y) = (((-x) + (2 * y)) + 1)))))
  (h4 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((((iteratedDeriv 1 (fun t => z (t, y)) x) = 0) ∧ ((iteratedDeriv 1 (fun t => z (x, t)) y) = 0)) ↔ ((x, y) = (1, 0))))))
  (h5 : A = (iteratedDeriv 2 (fun t => z (t, (0 : ℝ))) 1))
  (h6 : B = (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => z (t, p.2)) p.1)) (1, t)) 0))
  (h7 : C = (iteratedDeriv 2 (fun t => z ((1 : ℝ), t)) 0))
  (h8 : A = 2)
  (h9 : B = (-(1 : ℝ)))
  (h10 : C = 2)
  (h11 : ((A * C) - (B ^ (2 : ℕ))) = 3)
  (h12 : 3 > 0)
  (h13 : ((A * C) - (B ^ (2 : ℕ))) > 0)
  : (z ((1 : ℝ), (0 : ℝ))) = (-(1 : ℝ)) := by
  sorry

theorem proof_gap_exercise_3624_11
  (z : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((z (x, y)) = (((((x ^ (2 : ℕ)) - (x * y)) + (y ^ (2 : ℕ))) - (2 * x)) + y)))))
  (h2 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => z (t, y)) x) = (((2 * x) - y) - 2)))))
  (h3 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => z (x, t)) y) = (((-x) + (2 * y)) + 1)))))
  (h4 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((((iteratedDeriv 1 (fun t => z (t, y)) x) = 0) ∧ ((iteratedDeriv 1 (fun t => z (x, t)) y) = 0)) ↔ ((x, y) = (1, 0))))))
  (h5 : A = (iteratedDeriv 2 (fun t => z (t, (0 : ℝ))) 1))
  (h6 : B = (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => z (t, p.2)) p.1)) (1, t)) 0))
  (h7 : C = (iteratedDeriv 2 (fun t => z ((1 : ℝ), t)) 0))
  (h8 : A = 2)
  (h9 : B = (-(1 : ℝ)))
  (h10 : C = 2)
  (h11 : ((A * C) - (B ^ (2 : ℕ))) = 3)
  (h12 : 3 > 0)
  (h13 : ((A * C) - (B ^ (2 : ℕ))) > 0)
  (h14 : (z ((1 : ℝ), (0 : ℝ))) = (-(1 : ℝ)))
  : (lpMinimumPoints z) = ({x | x = (1, 0)}) := by
  sorry

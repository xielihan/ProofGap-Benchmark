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

-- exercise: exercise_3388_1

theorem proof_gap_exercise_3388_1_1
  (F : (ℝ × (ℝ × ℝ) -> ℝ))
  (f : (ℝ × (ℝ × ℝ) -> ℝ))
  (z : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ) (z_1 : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z_1 ∈ (Set.univ : Set ℝ))) → ((F (x, (y, z_1))) = ((((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) + (z_1 ^ (2 : ℕ))) - (((3 * x) * y) * z_1))))))
  (h2 : (forall (x : ℝ) (y : ℝ) (z_1 : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z_1 ∈ (Set.univ : Set ℝ))) → ((f (x, (y, z_1))) = ((x * (y ^ (2 : ℕ))) * (z_1 ^ (3 : ℕ)))))))
  (h3 : (F ((1 : ℝ), ((1 : ℝ), (1 : ℝ)))) = 0)
  (h4 : (iteratedDeriv 1 (fun t => F ((1 : ℝ), ((1 : ℝ), t))) 1) ≠ 0)
  (h5 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((F (x, (y, (z (x, y))))) = 0))))
  : (iteratedDeriv 1 (fun t => z (t, (1 : ℝ))) 1) = (-((iteratedDeriv 1 (fun t => F (t, ((1 : ℝ), (1 : ℝ)))) 1) /. (iteratedDeriv 1 (fun t => F ((1 : ℝ), ((1 : ℝ), t))) 1))) := by
  sorry

theorem proof_gap_exercise_3388_1_2
  (F : (ℝ × (ℝ × ℝ) -> ℝ))
  (f : (ℝ × (ℝ × ℝ) -> ℝ))
  (z : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ) (z_1 : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z_1 ∈ (Set.univ : Set ℝ))) → ((F (x, (y, z_1))) = ((((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) + (z_1 ^ (2 : ℕ))) - (((3 * x) * y) * z_1))))))
  (h2 : (forall (x : ℝ) (y : ℝ) (z_1 : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z_1 ∈ (Set.univ : Set ℝ))) → ((f (x, (y, z_1))) = ((x * (y ^ (2 : ℕ))) * (z_1 ^ (3 : ℕ)))))))
  (h3 : (F ((1 : ℝ), ((1 : ℝ), (1 : ℝ)))) = 0)
  (h4 : (iteratedDeriv 1 (fun t => F ((1 : ℝ), ((1 : ℝ), t))) 1) ≠ 0)
  (h5 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((F (x, (y, (z (x, y))))) = 0))))
  (h6 : (iteratedDeriv 1 (fun t => z (t, (1 : ℝ))) 1) = (-((iteratedDeriv 1 (fun t => F (t, ((1 : ℝ), (1 : ℝ)))) 1) /. (iteratedDeriv 1 (fun t => F ((1 : ℝ), ((1 : ℝ), t))) 1))))
  : (iteratedDeriv 1 (fun t => z (t, (1 : ℝ))) 1) = (-((iteratedDeriv 1 (fun t => (F (t, ((1 : ℝ), (1 : ℝ))))) 1) /. (iteratedDeriv 1 (fun t => (F ((1 : ℝ), ((1 : ℝ), t)))) 1))) := by
  sorry

theorem proof_gap_exercise_3388_1_3
  (F : (ℝ × (ℝ × ℝ) -> ℝ))
  (f : (ℝ × (ℝ × ℝ) -> ℝ))
  (z : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ) (z_1 : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z_1 ∈ (Set.univ : Set ℝ))) → ((F (x, (y, z_1))) = ((((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) + (z_1 ^ (2 : ℕ))) - (((3 * x) * y) * z_1))))))
  (h2 : (forall (x : ℝ) (y : ℝ) (z_1 : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z_1 ∈ (Set.univ : Set ℝ))) → ((f (x, (y, z_1))) = ((x * (y ^ (2 : ℕ))) * (z_1 ^ (3 : ℕ)))))))
  (h3 : (F ((1 : ℝ), ((1 : ℝ), (1 : ℝ)))) = 0)
  (h4 : (iteratedDeriv 1 (fun t => F ((1 : ℝ), ((1 : ℝ), t))) 1) ≠ 0)
  (h5 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((F (x, (y, (z (x, y))))) = 0))))
  (h6 : (iteratedDeriv 1 (fun t => z (t, (1 : ℝ))) 1) = (-((iteratedDeriv 1 (fun t => F (t, ((1 : ℝ), (1 : ℝ)))) 1) /. (iteratedDeriv 1 (fun t => F ((1 : ℝ), ((1 : ℝ), t))) 1))))
  (h7 : (iteratedDeriv 1 (fun t => z (t, (1 : ℝ))) 1) = (-((iteratedDeriv 1 (fun t => (F (t, ((1 : ℝ), (1 : ℝ))))) 1) /. (iteratedDeriv 1 (fun t => (F ((1 : ℝ), ((1 : ℝ), t)))) 1))))
  : (iteratedDeriv 1 (fun t => z (t, (1 : ℝ))) 1) = (-((iteratedDeriv 1 (fun t => (((t ^ (2 : ℕ)) + 2) - (3 * t))) 1) /. (iteratedDeriv 1 (fun t => ((2 + (t ^ (2 : ℕ))) - (3 * t))) 1))) := by
  sorry

theorem proof_gap_exercise_3388_1_4
  (F : (ℝ × (ℝ × ℝ) -> ℝ))
  (f : (ℝ × (ℝ × ℝ) -> ℝ))
  (z : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ) (z_1 : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z_1 ∈ (Set.univ : Set ℝ))) → ((F (x, (y, z_1))) = ((((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) + (z_1 ^ (2 : ℕ))) - (((3 * x) * y) * z_1))))))
  (h2 : (forall (x : ℝ) (y : ℝ) (z_1 : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z_1 ∈ (Set.univ : Set ℝ))) → ((f (x, (y, z_1))) = ((x * (y ^ (2 : ℕ))) * (z_1 ^ (3 : ℕ)))))))
  (h3 : (F ((1 : ℝ), ((1 : ℝ), (1 : ℝ)))) = 0)
  (h4 : (iteratedDeriv 1 (fun t => F ((1 : ℝ), ((1 : ℝ), t))) 1) ≠ 0)
  (h5 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((F (x, (y, (z (x, y))))) = 0))))
  (h6 : (iteratedDeriv 1 (fun t => z (t, (1 : ℝ))) 1) = (-((iteratedDeriv 1 (fun t => F (t, ((1 : ℝ), (1 : ℝ)))) 1) /. (iteratedDeriv 1 (fun t => F ((1 : ℝ), ((1 : ℝ), t))) 1))))
  (h7 : (iteratedDeriv 1 (fun t => z (t, (1 : ℝ))) 1) = (-((iteratedDeriv 1 (fun t => (F (t, ((1 : ℝ), (1 : ℝ))))) 1) /. (iteratedDeriv 1 (fun t => (F ((1 : ℝ), ((1 : ℝ), t)))) 1))))
  (h8 : (iteratedDeriv 1 (fun t => z (t, (1 : ℝ))) 1) = (-((iteratedDeriv 1 (fun t => (((t ^ (2 : ℕ)) + 2) - (3 * t))) 1) /. (iteratedDeriv 1 (fun t => ((2 + (t ^ (2 : ℕ))) - (3 * t))) 1))))
  : (iteratedDeriv 1 (fun t => z (t, (1 : ℝ))) 1) = (-(1 : ℝ)) := by
  sorry

theorem proof_gap_exercise_3388_1_5
  (F : (ℝ × (ℝ × ℝ) -> ℝ))
  (f : (ℝ × (ℝ × ℝ) -> ℝ))
  (z : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ) (z_1 : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z_1 ∈ (Set.univ : Set ℝ))) → ((F (x, (y, z_1))) = ((((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) + (z_1 ^ (2 : ℕ))) - (((3 * x) * y) * z_1))))))
  (h2 : (forall (x : ℝ) (y : ℝ) (z_1 : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z_1 ∈ (Set.univ : Set ℝ))) → ((f (x, (y, z_1))) = ((x * (y ^ (2 : ℕ))) * (z_1 ^ (3 : ℕ)))))))
  (h3 : (F ((1 : ℝ), ((1 : ℝ), (1 : ℝ)))) = 0)
  (h4 : (iteratedDeriv 1 (fun t => F ((1 : ℝ), ((1 : ℝ), t))) 1) ≠ 0)
  (h5 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((F (x, (y, (z (x, y))))) = 0))))
  (h6 : (iteratedDeriv 1 (fun t => z (t, (1 : ℝ))) 1) = (-((iteratedDeriv 1 (fun t => F (t, ((1 : ℝ), (1 : ℝ)))) 1) /. (iteratedDeriv 1 (fun t => F ((1 : ℝ), ((1 : ℝ), t))) 1))))
  (h7 : (iteratedDeriv 1 (fun t => z (t, (1 : ℝ))) 1) = (-((iteratedDeriv 1 (fun t => (F (t, ((1 : ℝ), (1 : ℝ))))) 1) /. (iteratedDeriv 1 (fun t => (F ((1 : ℝ), ((1 : ℝ), t)))) 1))))
  (h8 : (iteratedDeriv 1 (fun t => z (t, (1 : ℝ))) 1) = (-((iteratedDeriv 1 (fun t => (((t ^ (2 : ℕ)) + 2) - (3 * t))) 1) /. (iteratedDeriv 1 (fun t => ((2 + (t ^ (2 : ℕ))) - (3 * t))) 1))))
  (h9 : (iteratedDeriv 1 (fun t => z (t, (1 : ℝ))) 1) = (-(1 : ℝ)))
  : (iteratedDeriv 1 (fun t => (f (t, ((1 : ℝ), (z (t, (1 : ℝ))))))) 1) = ((iteratedDeriv 1 (fun t => (f (t, ((1 : ℝ), (1 : ℝ))))) 1) + ((iteratedDeriv 1 (fun t => f ((1 : ℝ), ((1 : ℝ), t))) 1) * (iteratedDeriv 1 (fun t => z (t, (1 : ℝ))) 1))) := by
  sorry

theorem proof_gap_exercise_3388_1_6
  (F : (ℝ × (ℝ × ℝ) -> ℝ))
  (f : (ℝ × (ℝ × ℝ) -> ℝ))
  (z : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ) (z_1 : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z_1 ∈ (Set.univ : Set ℝ))) → ((F (x, (y, z_1))) = ((((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) + (z_1 ^ (2 : ℕ))) - (((3 * x) * y) * z_1))))))
  (h2 : (forall (x : ℝ) (y : ℝ) (z_1 : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z_1 ∈ (Set.univ : Set ℝ))) → ((f (x, (y, z_1))) = ((x * (y ^ (2 : ℕ))) * (z_1 ^ (3 : ℕ)))))))
  (h3 : (F ((1 : ℝ), ((1 : ℝ), (1 : ℝ)))) = 0)
  (h4 : (iteratedDeriv 1 (fun t => F ((1 : ℝ), ((1 : ℝ), t))) 1) ≠ 0)
  (h5 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((F (x, (y, (z (x, y))))) = 0))))
  (h6 : (iteratedDeriv 1 (fun t => z (t, (1 : ℝ))) 1) = (-((iteratedDeriv 1 (fun t => F (t, ((1 : ℝ), (1 : ℝ)))) 1) /. (iteratedDeriv 1 (fun t => F ((1 : ℝ), ((1 : ℝ), t))) 1))))
  (h7 : (iteratedDeriv 1 (fun t => z (t, (1 : ℝ))) 1) = (-((iteratedDeriv 1 (fun t => (F (t, ((1 : ℝ), (1 : ℝ))))) 1) /. (iteratedDeriv 1 (fun t => (F ((1 : ℝ), ((1 : ℝ), t)))) 1))))
  (h8 : (iteratedDeriv 1 (fun t => z (t, (1 : ℝ))) 1) = (-((iteratedDeriv 1 (fun t => (((t ^ (2 : ℕ)) + 2) - (3 * t))) 1) /. (iteratedDeriv 1 (fun t => ((2 + (t ^ (2 : ℕ))) - (3 * t))) 1))))
  (h9 : (iteratedDeriv 1 (fun t => z (t, (1 : ℝ))) 1) = (-(1 : ℝ)))
  (h10 : (iteratedDeriv 1 (fun t => (f (t, ((1 : ℝ), (z (t, (1 : ℝ))))))) 1) = ((iteratedDeriv 1 (fun t => (f (t, ((1 : ℝ), (1 : ℝ))))) 1) + ((iteratedDeriv 1 (fun t => f ((1 : ℝ), ((1 : ℝ), t))) 1) * (iteratedDeriv 1 (fun t => z (t, (1 : ℝ))) 1))))
  : (iteratedDeriv 1 (fun t => (f (t, ((1 : ℝ), (z (t, (1 : ℝ))))))) 1) = (1 + (3 * (-(1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_3388_1_7
  (F : (ℝ × (ℝ × ℝ) -> ℝ))
  (f : (ℝ × (ℝ × ℝ) -> ℝ))
  (z : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ) (z_1 : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z_1 ∈ (Set.univ : Set ℝ))) → ((F (x, (y, z_1))) = ((((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) + (z_1 ^ (2 : ℕ))) - (((3 * x) * y) * z_1))))))
  (h2 : (forall (x : ℝ) (y : ℝ) (z_1 : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z_1 ∈ (Set.univ : Set ℝ))) → ((f (x, (y, z_1))) = ((x * (y ^ (2 : ℕ))) * (z_1 ^ (3 : ℕ)))))))
  (h3 : (F ((1 : ℝ), ((1 : ℝ), (1 : ℝ)))) = 0)
  (h4 : (iteratedDeriv 1 (fun t => F ((1 : ℝ), ((1 : ℝ), t))) 1) ≠ 0)
  (h5 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((F (x, (y, (z (x, y))))) = 0))))
  (h6 : (iteratedDeriv 1 (fun t => z (t, (1 : ℝ))) 1) = (-((iteratedDeriv 1 (fun t => F (t, ((1 : ℝ), (1 : ℝ)))) 1) /. (iteratedDeriv 1 (fun t => F ((1 : ℝ), ((1 : ℝ), t))) 1))))
  (h7 : (iteratedDeriv 1 (fun t => z (t, (1 : ℝ))) 1) = (-((iteratedDeriv 1 (fun t => (F (t, ((1 : ℝ), (1 : ℝ))))) 1) /. (iteratedDeriv 1 (fun t => (F ((1 : ℝ), ((1 : ℝ), t)))) 1))))
  (h8 : (iteratedDeriv 1 (fun t => z (t, (1 : ℝ))) 1) = (-((iteratedDeriv 1 (fun t => (((t ^ (2 : ℕ)) + 2) - (3 * t))) 1) /. (iteratedDeriv 1 (fun t => ((2 + (t ^ (2 : ℕ))) - (3 * t))) 1))))
  (h9 : (iteratedDeriv 1 (fun t => z (t, (1 : ℝ))) 1) = (-(1 : ℝ)))
  (h10 : (iteratedDeriv 1 (fun t => (f (t, ((1 : ℝ), (z (t, (1 : ℝ))))))) 1) = ((iteratedDeriv 1 (fun t => (f (t, ((1 : ℝ), (1 : ℝ))))) 1) + ((iteratedDeriv 1 (fun t => f ((1 : ℝ), ((1 : ℝ), t))) 1) * (iteratedDeriv 1 (fun t => z (t, (1 : ℝ))) 1))))
  (h11 : (iteratedDeriv 1 (fun t => (f (t, ((1 : ℝ), (z (t, (1 : ℝ))))))) 1) = (1 + (3 * (-(1 : ℝ)))))
  : (iteratedDeriv 1 (fun t => (f (t, ((1 : ℝ), (z (t, (1 : ℝ))))))) 1) = (-(2 : ℝ)) := by
  sorry

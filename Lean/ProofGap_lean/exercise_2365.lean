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

-- exercise: exercise_2365

theorem proof_gap_exercise_2365_1
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : (1 < n) ∧ (n < 2))
  : (∫ x in Set.Ioi (0 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) = ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) + (∫ x in Set.Ioi (1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_2365_2
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : (∫ x in Set.Ioi (0 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) = ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) + (∫ x in Set.Ioi (1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ)))))
  : (n > 1) → (exists (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1))) := by
  sorry

theorem proof_gap_exercise_2365_3
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : (∫ x in Set.Ioi (0 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) = ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) + (∫ x in Set.Ioi (1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ)))))
  (h3 : (n > 1) → (exists (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1))))
  : (n > 1) → (forall (a : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → (((Real.rpow x (n - a)) * ((Real.log (1 + x)) /. (Real.rpow x n))) = ((Real.log (1 + x)) /. (Real.rpow x a))))))) := by
  sorry

theorem proof_gap_exercise_2365_4
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : (∫ x in Set.Ioi (0 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) = ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) + (∫ x in Set.Ioi (1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ)))))
  (h3 : (n > 1) → (exists (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1))))
  (h4 : (n > 1) → (forall (a : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → (((Real.rpow x (n - a)) * ((Real.log (1 + x)) /. (Real.rpow x n))) = ((Real.log (1 + x)) /. (Real.rpow x a))))))))
  (h5 : (1 < n) ∧ (n < 2))
  : (n > 1) → (forall (a : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1)) → (Tendsto (fun x : ℝ => ((Real.log (1 + x)) /. (Real.rpow x a))) atTop (𝓝 0)))) := by
  sorry

theorem proof_gap_exercise_2365_5
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : (∫ x in Set.Ioi (0 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) = ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) + (∫ x in Set.Ioi (1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ)))))
  (h3 : (n > 1) → (exists (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1))))
  (h4 : (n > 1) → (forall (a : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → (((Real.rpow x (n - a)) * ((Real.log (1 + x)) /. (Real.rpow x n))) = ((Real.log (1 + x)) /. (Real.rpow x a))))))))
  (h5 : (n > 1) → (forall (a : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1)) → (Tendsto (fun x : ℝ => ((Real.log (1 + x)) /. (Real.rpow x a))) atTop (𝓝 0)))))
  : (n > 1) → (forall (a : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1)) → (Tendsto (fun x : ℝ => ((Real.rpow x (n - a)) * ((Real.log (1 + x)) /. (Real.rpow x n)))) atTop (𝓝 0)))) := by
  sorry

theorem proof_gap_exercise_2365_6
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : (∫ x in Set.Ioi (0 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) = ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) + (∫ x in Set.Ioi (1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ)))))
  (h3 : (n > 1) → (exists (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1))))
  (h4 : (n > 1) → (forall (a : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → (((Real.rpow x (n - a)) * ((Real.log (1 + x)) /. (Real.rpow x n))) = ((Real.log (1 + x)) /. (Real.rpow x a))))))))
  (h5 : (n > 1) → (forall (a : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1)) → (Tendsto (fun x : ℝ => ((Real.log (1 + x)) /. (Real.rpow x a))) atTop (𝓝 0)))))
  (h6 : (n > 1) → (forall (a : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1)) → (Tendsto (fun x : ℝ => ((Real.rpow x (n - a)) * ((Real.log (1 + x)) /. (Real.rpow x n)))) atTop (𝓝 0)))))
  : (n > 1) → ((∫ x in Set.Ioi (1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)) := by
  sorry

theorem proof_gap_exercise_2365_7
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : (∫ x in Set.Ioi (0 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) = ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) + (∫ x in Set.Ioi (1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ)))))
  (h3 : (n > 1) → (exists (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1))))
  (h4 : (n > 1) → (forall (a : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → (((Real.rpow x (n - a)) * ((Real.log (1 + x)) /. (Real.rpow x n))) = ((Real.log (1 + x)) /. (Real.rpow x a))))))))
  (h5 : (n > 1) → (forall (a : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1)) → (Tendsto (fun x : ℝ => ((Real.log (1 + x)) /. (Real.rpow x a))) atTop (𝓝 0)))))
  (h6 : (n > 1) → (forall (a : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1)) → (Tendsto (fun x : ℝ => ((Real.rpow x (n - a)) * ((Real.log (1 + x)) /. (Real.rpow x n)))) atTop (𝓝 0)))))
  (h7 : (n > 1) → ((∫ x in Set.Ioi (1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)))
  : (n ≤ 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → (((Real.rpow x n) * ((Real.log (1 + x)) /. (Real.rpow x n))) = (Real.log (1 + x))))) := by
  sorry

theorem proof_gap_exercise_2365_8
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : (∫ x in Set.Ioi (0 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) = ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) + (∫ x in Set.Ioi (1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ)))))
  (h3 : (n > 1) → (exists (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1))))
  (h4 : (n > 1) → (forall (a : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → (((Real.rpow x (n - a)) * ((Real.log (1 + x)) /. (Real.rpow x n))) = ((Real.log (1 + x)) /. (Real.rpow x a))))))))
  (h5 : (n > 1) → (forall (a : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1)) → (Tendsto (fun x : ℝ => ((Real.log (1 + x)) /. (Real.rpow x a))) atTop (𝓝 0)))))
  (h6 : (n > 1) → (forall (a : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1)) → (Tendsto (fun x : ℝ => ((Real.rpow x (n - a)) * ((Real.log (1 + x)) /. (Real.rpow x n)))) atTop (𝓝 0)))))
  (h7 : (n > 1) → ((∫ x in Set.Ioi (1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)))
  (h8 : (n ≤ 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → (((Real.rpow x n) * ((Real.log (1 + x)) /. (Real.rpow x n))) = (Real.log (1 + x))))))
  : (n ≤ 1) → (Tendsto (fun x : ℝ => ((Real.log (1 + x)) : EReal)) atTop (𝓝 ⊤)) := by
  sorry

theorem proof_gap_exercise_2365_9
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : (∫ x in Set.Ioi (0 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) = ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) + (∫ x in Set.Ioi (1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ)))))
  (h3 : (n > 1) → (exists (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1))))
  (h4 : (n > 1) → (forall (a : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → (((Real.rpow x (n - a)) * ((Real.log (1 + x)) /. (Real.rpow x n))) = ((Real.log (1 + x)) /. (Real.rpow x a))))))))
  (h5 : (n > 1) → (forall (a : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1)) → (Tendsto (fun x : ℝ => ((Real.log (1 + x)) /. (Real.rpow x a))) atTop (𝓝 0)))))
  (h6 : (n > 1) → (forall (a : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1)) → (Tendsto (fun x : ℝ => ((Real.rpow x (n - a)) * ((Real.log (1 + x)) /. (Real.rpow x n)))) atTop (𝓝 0)))))
  (h7 : (n > 1) → ((∫ x in Set.Ioi (1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)))
  (h8 : (n ≤ 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → (((Real.rpow x n) * ((Real.log (1 + x)) /. (Real.rpow x n))) = (Real.log (1 + x))))))
  (h9 : (n ≤ 1) → (Tendsto (fun x : ℝ => ((Real.log (1 + x)) : EReal)) atTop (𝓝 ⊤)))
  : (n ≤ 1) → (Tendsto (fun x : ℝ => (((Real.rpow x n) * ((Real.log (1 + x)) /. (Real.rpow x n))) : EReal)) atTop (𝓝 ⊤)) := by
  sorry

theorem proof_gap_exercise_2365_10
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : (∫ x in Set.Ioi (0 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) = ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) + (∫ x in Set.Ioi (1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ)))))
  (h3 : (n > 1) → (exists (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1))))
  (h4 : (n > 1) → (forall (a : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → (((Real.rpow x (n - a)) * ((Real.log (1 + x)) /. (Real.rpow x n))) = ((Real.log (1 + x)) /. (Real.rpow x a))))))))
  (h5 : (n > 1) → (forall (a : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1)) → (Tendsto (fun x : ℝ => ((Real.log (1 + x)) /. (Real.rpow x a))) atTop (𝓝 0)))))
  (h6 : (n > 1) → (forall (a : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1)) → (Tendsto (fun x : ℝ => ((Real.rpow x (n - a)) * ((Real.log (1 + x)) /. (Real.rpow x n)))) atTop (𝓝 0)))))
  (h7 : (n > 1) → ((∫ x in Set.Ioi (1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)))
  (h8 : (n ≤ 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → (((Real.rpow x n) * ((Real.log (1 + x)) /. (Real.rpow x n))) = (Real.log (1 + x))))))
  (h9 : (n ≤ 1) → (Tendsto (fun x : ℝ => ((Real.log (1 + x)) : EReal)) atTop (𝓝 ⊤)))
  (h10 : (n ≤ 1) → (Tendsto (fun x : ℝ => (((Real.rpow x n) * ((Real.log (1 + x)) /. (Real.rpow x n))) : EReal)) atTop (𝓝 ⊤)))
  : (n ≤ 1) → (Not ((∫ x in Set.Ioi (1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) ∈ (Set.univ : Set ℝ))) := by
  sorry

theorem proof_gap_exercise_2365_11
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : (∫ x in Set.Ioi (0 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) = ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) + (∫ x in Set.Ioi (1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ)))))
  (h3 : (n > 1) → (exists (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1))))
  (h4 : (n > 1) → (forall (a : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → (((Real.rpow x (n - a)) * ((Real.log (1 + x)) /. (Real.rpow x n))) = ((Real.log (1 + x)) /. (Real.rpow x a))))))))
  (h5 : (n > 1) → (forall (a : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1)) → (Tendsto (fun x : ℝ => ((Real.log (1 + x)) /. (Real.rpow x a))) atTop (𝓝 0)))))
  (h6 : (n > 1) → (forall (a : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1)) → (Tendsto (fun x : ℝ => ((Real.rpow x (n - a)) * ((Real.log (1 + x)) /. (Real.rpow x n)))) atTop (𝓝 0)))))
  (h7 : (n > 1) → ((∫ x in Set.Ioi (1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)))
  (h8 : (n ≤ 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → (((Real.rpow x n) * ((Real.log (1 + x)) /. (Real.rpow x n))) = (Real.log (1 + x))))))
  (h9 : (n ≤ 1) → (Tendsto (fun x : ℝ => ((Real.log (1 + x)) : EReal)) atTop (𝓝 ⊤)))
  (h10 : (n ≤ 1) → (Tendsto (fun x : ℝ => (((Real.rpow x n) * ((Real.log (1 + x)) /. (Real.rpow x n))) : EReal)) atTop (𝓝 ⊤)))
  (h11 : (n ≤ 1) → (Not ((∫ x in Set.Ioi (1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) ∈ (Set.univ : Set ℝ))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (((Real.rpow x (n - 1)) * ((Real.log (1 + x)) /. (Real.rpow x n))) = ((Real.log (1 + x)) /. x)))) := by
  sorry

theorem proof_gap_exercise_2365_12
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : (∫ x in Set.Ioi (0 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) = ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) + (∫ x in Set.Ioi (1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ)))))
  (h3 : (n > 1) → (exists (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1))))
  (h4 : (n > 1) → (forall (a : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → (((Real.rpow x (n - a)) * ((Real.log (1 + x)) /. (Real.rpow x n))) = ((Real.log (1 + x)) /. (Real.rpow x a))))))))
  (h5 : (n > 1) → (forall (a : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1)) → (Tendsto (fun x : ℝ => ((Real.log (1 + x)) /. (Real.rpow x a))) atTop (𝓝 0)))))
  (h6 : (n > 1) → (forall (a : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1)) → (Tendsto (fun x : ℝ => ((Real.rpow x (n - a)) * ((Real.log (1 + x)) /. (Real.rpow x n)))) atTop (𝓝 0)))))
  (h7 : (n > 1) → ((∫ x in Set.Ioi (1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)))
  (h8 : (n ≤ 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → (((Real.rpow x n) * ((Real.log (1 + x)) /. (Real.rpow x n))) = (Real.log (1 + x))))))
  (h9 : (n ≤ 1) → (Tendsto (fun x : ℝ => ((Real.log (1 + x)) : EReal)) atTop (𝓝 ⊤)))
  (h10 : (n ≤ 1) → (Tendsto (fun x : ℝ => (((Real.rpow x n) * ((Real.log (1 + x)) /. (Real.rpow x n))) : EReal)) atTop (𝓝 ⊤)))
  (h11 : (n ≤ 1) → (Not ((∫ x in Set.Ioi (1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) ∈ (Set.univ : Set ℝ))))
  (h12 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (((Real.rpow x (n - 1)) * ((Real.log (1 + x)) /. (Real.rpow x n))) = ((Real.log (1 + x)) /. x)))))
  : Tendsto (fun x : ℝ => ((Real.log (1 + x)) /. x)) (𝓝[>] 0) (𝓝 1) := by
  sorry

theorem proof_gap_exercise_2365_13
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : (∫ x in Set.Ioi (0 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) = ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) + (∫ x in Set.Ioi (1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ)))))
  (h3 : (n > 1) → (exists (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1))))
  (h4 : (n > 1) → (forall (a : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → (((Real.rpow x (n - a)) * ((Real.log (1 + x)) /. (Real.rpow x n))) = ((Real.log (1 + x)) /. (Real.rpow x a))))))))
  (h5 : (n > 1) → (forall (a : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1)) → (Tendsto (fun x : ℝ => ((Real.log (1 + x)) /. (Real.rpow x a))) atTop (𝓝 0)))))
  (h6 : (n > 1) → (forall (a : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1)) → (Tendsto (fun x : ℝ => ((Real.rpow x (n - a)) * ((Real.log (1 + x)) /. (Real.rpow x n)))) atTop (𝓝 0)))))
  (h7 : (n > 1) → ((∫ x in Set.Ioi (1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)))
  (h8 : (n ≤ 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → (((Real.rpow x n) * ((Real.log (1 + x)) /. (Real.rpow x n))) = (Real.log (1 + x))))))
  (h9 : (n ≤ 1) → (Tendsto (fun x : ℝ => ((Real.log (1 + x)) : EReal)) atTop (𝓝 ⊤)))
  (h10 : (n ≤ 1) → (Tendsto (fun x : ℝ => (((Real.rpow x n) * ((Real.log (1 + x)) /. (Real.rpow x n))) : EReal)) atTop (𝓝 ⊤)))
  (h11 : (n ≤ 1) → (Not ((∫ x in Set.Ioi (1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) ∈ (Set.univ : Set ℝ))))
  (h12 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (((Real.rpow x (n - 1)) * ((Real.log (1 + x)) /. (Real.rpow x n))) = ((Real.log (1 + x)) /. x)))))
  (h13 : Tendsto (fun x : ℝ => ((Real.log (1 + x)) /. x)) (𝓝[>] 0) (𝓝 1))
  : Tendsto (fun x : ℝ => ((Real.rpow x (n - 1)) * ((Real.log (1 + x)) /. (Real.rpow x n)))) (𝓝[>] 0) (𝓝 1) := by
  sorry

theorem proof_gap_exercise_2365_14
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : (∫ x in Set.Ioi (0 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) = ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) + (∫ x in Set.Ioi (1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ)))))
  (h3 : (n > 1) → (exists (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1))))
  (h4 : (n > 1) → (forall (a : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → (((Real.rpow x (n - a)) * ((Real.log (1 + x)) /. (Real.rpow x n))) = ((Real.log (1 + x)) /. (Real.rpow x a))))))))
  (h5 : (n > 1) → (forall (a : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1)) → (Tendsto (fun x : ℝ => ((Real.log (1 + x)) /. (Real.rpow x a))) atTop (𝓝 0)))))
  (h6 : (n > 1) → (forall (a : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1)) → (Tendsto (fun x : ℝ => ((Real.rpow x (n - a)) * ((Real.log (1 + x)) /. (Real.rpow x n)))) atTop (𝓝 0)))))
  (h7 : (n > 1) → ((∫ x in Set.Ioi (1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)))
  (h8 : (n ≤ 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → (((Real.rpow x n) * ((Real.log (1 + x)) /. (Real.rpow x n))) = (Real.log (1 + x))))))
  (h9 : (n ≤ 1) → (Tendsto (fun x : ℝ => ((Real.log (1 + x)) : EReal)) atTop (𝓝 ⊤)))
  (h10 : (n ≤ 1) → (Tendsto (fun x : ℝ => (((Real.rpow x n) * ((Real.log (1 + x)) /. (Real.rpow x n))) : EReal)) atTop (𝓝 ⊤)))
  (h11 : (n ≤ 1) → (Not ((∫ x in Set.Ioi (1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) ∈ (Set.univ : Set ℝ))))
  (h12 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (((Real.rpow x (n - 1)) * ((Real.log (1 + x)) /. (Real.rpow x n))) = ((Real.log (1 + x)) /. x)))))
  (h13 : Tendsto (fun x : ℝ => ((Real.log (1 + x)) /. x)) (𝓝[>] 0) (𝓝 1))
  (h14 : Tendsto (fun x : ℝ => ((Real.rpow x (n - 1)) * ((Real.log (1 + x)) /. (Real.rpow x n)))) (𝓝[>] 0) (𝓝 1))
  : ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)) ↔ ((n - 1) < 1) := by
  sorry

theorem proof_gap_exercise_2365_15
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : (∫ x in Set.Ioi (0 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) = ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) + (∫ x in Set.Ioi (1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ)))))
  (h3 : (n > 1) → (exists (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1))))
  (h4 : (n > 1) → (forall (a : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → (((Real.rpow x (n - a)) * ((Real.log (1 + x)) /. (Real.rpow x n))) = ((Real.log (1 + x)) /. (Real.rpow x a))))))))
  (h5 : (n > 1) → (forall (a : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1)) → (Tendsto (fun x : ℝ => ((Real.log (1 + x)) /. (Real.rpow x a))) atTop (𝓝 0)))))
  (h6 : (n > 1) → (forall (a : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1)) → (Tendsto (fun x : ℝ => ((Real.rpow x (n - a)) * ((Real.log (1 + x)) /. (Real.rpow x n)))) atTop (𝓝 0)))))
  (h7 : (n > 1) → ((∫ x in Set.Ioi (1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)))
  (h8 : (n ≤ 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → (((Real.rpow x n) * ((Real.log (1 + x)) /. (Real.rpow x n))) = (Real.log (1 + x))))))
  (h9 : (n ≤ 1) → (Tendsto (fun x : ℝ => ((Real.log (1 + x)) : EReal)) atTop (𝓝 ⊤)))
  (h10 : (n ≤ 1) → (Tendsto (fun x : ℝ => (((Real.rpow x n) * ((Real.log (1 + x)) /. (Real.rpow x n))) : EReal)) atTop (𝓝 ⊤)))
  (h11 : (n ≤ 1) → (Not ((∫ x in Set.Ioi (1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) ∈ (Set.univ : Set ℝ))))
  (h12 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (((Real.rpow x (n - 1)) * ((Real.log (1 + x)) /. (Real.rpow x n))) = ((Real.log (1 + x)) /. x)))))
  (h13 : Tendsto (fun x : ℝ => ((Real.log (1 + x)) /. x)) (𝓝[>] 0) (𝓝 1))
  (h14 : Tendsto (fun x : ℝ => ((Real.rpow x (n - 1)) * ((Real.log (1 + x)) /. (Real.rpow x n)))) (𝓝[>] 0) (𝓝 1))
  (h15 : ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)) ↔ ((n - 1) < 1))
  : ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)) ↔ (n < 2) := by
  sorry

theorem proof_gap_exercise_2365_16
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : (∫ x in Set.Ioi (0 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) = ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) + (∫ x in Set.Ioi (1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ)))))
  (h3 : (n > 1) → (exists (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1))))
  (h4 : (n > 1) → (forall (a : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → (((Real.rpow x (n - a)) * ((Real.log (1 + x)) /. (Real.rpow x n))) = ((Real.log (1 + x)) /. (Real.rpow x a))))))))
  (h5 : (n > 1) → (forall (a : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1)) → (Tendsto (fun x : ℝ => ((Real.log (1 + x)) /. (Real.rpow x a))) atTop (𝓝 0)))))
  (h6 : (n > 1) → (forall (a : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ ((n - a) > 1)) → (Tendsto (fun x : ℝ => ((Real.rpow x (n - a)) * ((Real.log (1 + x)) /. (Real.rpow x n)))) atTop (𝓝 0)))))
  (h7 : (n > 1) → ((∫ x in Set.Ioi (1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)))
  (h8 : (n ≤ 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → (((Real.rpow x n) * ((Real.log (1 + x)) /. (Real.rpow x n))) = (Real.log (1 + x))))))
  (h9 : (n ≤ 1) → (Tendsto (fun x : ℝ => ((Real.log (1 + x)) : EReal)) atTop (𝓝 ⊤)))
  (h10 : (n ≤ 1) → (Tendsto (fun x : ℝ => (((Real.rpow x n) * ((Real.log (1 + x)) /. (Real.rpow x n))) : EReal)) atTop (𝓝 ⊤)))
  (h11 : (n ≤ 1) → (Not ((∫ x in Set.Ioi (1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) ∈ (Set.univ : Set ℝ))))
  (h12 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (((Real.rpow x (n - 1)) * ((Real.log (1 + x)) /. (Real.rpow x n))) = ((Real.log (1 + x)) /. x)))))
  (h13 : Tendsto (fun x : ℝ => ((Real.log (1 + x)) /. x)) (𝓝[>] 0) (𝓝 1))
  (h14 : Tendsto (fun x : ℝ => ((Real.rpow x (n - 1)) * ((Real.log (1 + x)) /. (Real.rpow x n)))) (𝓝[>] 0) (𝓝 1))
  (h15 : ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)) ↔ ((n - 1) < 1))
  (h16 : ((∫ x in (0 : ℝ)..(1 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)) ↔ (n < 2))
  : (n ∈ ({n_1 | (n_1 ∈ (Set.univ : Set ℝ)) ∧ (1 < n_1) ∧ (n_1 < 2)})) ↔ ((∫ x in Set.Ioi (0 : ℝ), (((Real.log (1 + x)) /. (Real.rpow x n)) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)) := by
  sorry

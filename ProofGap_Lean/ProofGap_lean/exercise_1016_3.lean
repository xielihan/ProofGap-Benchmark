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

-- exercise: exercise_1016_3

theorem proof_gap_exercise_1016_3_1
  (h1 : f_1 = (fun (x : ℝ) => ((2 * x) + |(x)|)))
  (h2 : g_1 = (fun (x : ℝ) => (((2 /. 3) * x) - ((1 /. 3) * |(x)|))))
  (h3 : F_1 = (fun (x : ℝ) => (f_1 (g_1 x))))
  : (g_1 0) = 0 := by
  sorry

theorem proof_gap_exercise_1016_3_2
  (h1 : f_1 = (fun (x : ℝ) => ((2 * x) + |(x)|)))
  (h2 : g_1 = (fun (x : ℝ) => (((2 /. 3) * x) - ((1 /. 3) * |(x)|))))
  (h3 : F_1 = (fun (x : ℝ) => (f_1 (g_1 x))))
  (h4 : (g_1 0) = 0)
  : Not (DifferentiableAt ℝ f_1 0) := by
  sorry

theorem proof_gap_exercise_1016_3_3
  (h1 : f_1 = (fun (x : ℝ) => ((2 * x) + |(x)|)))
  (h2 : g_1 = (fun (x : ℝ) => (((2 /. 3) * x) - ((1 /. 3) * |(x)|))))
  (h3 : F_1 = (fun (x : ℝ) => (f_1 (g_1 x))))
  (h4 : (g_1 0) = 0)
  (h5 : Not (DifferentiableAt ℝ f_1 0))
  : Not (DifferentiableAt ℝ g_1 0) := by
  sorry

theorem proof_gap_exercise_1016_3_4
  (h1 : f_1 = (fun (x : ℝ) => ((2 * x) + |(x)|)))
  (h2 : g_1 = (fun (x : ℝ) => (((2 /. 3) * x) - ((1 /. 3) * |(x)|))))
  (h3 : F_1 = (fun (x : ℝ) => (f_1 (g_1 x))))
  (h4 : (g_1 0) = 0)
  (h5 : Not (DifferentiableAt ℝ f_1 0))
  (h6 : Not (DifferentiableAt ℝ g_1 0))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((F_1 x) = (f_1 (g_1 x))) ∧ ((f_1 (g_1 x)) = ((2 * (((2 /. 3) * x) - ((1 /. 3) * |(x)|))) + |((((2 /. 3) * x) - ((1 /. 3) * |(x)|)))|))) ∧ (((2 * (((2 /. 3) * x) - ((1 /. 3) * |(x)|))) + |((((2 /. 3) * x) - ((1 /. 3) * |(x)|)))|) = x)))) := by
  sorry

theorem proof_gap_exercise_1016_3_5
  (h1 : f_1 = (fun (x : ℝ) => ((2 * x) + |(x)|)))
  (h2 : g_1 = (fun (x : ℝ) => (((2 /. 3) * x) - ((1 /. 3) * |(x)|))))
  (h3 : F_1 = (fun (x : ℝ) => (f_1 (g_1 x))))
  (h4 : (g_1 0) = 0)
  (h5 : Not (DifferentiableAt ℝ f_1 0))
  (h6 : Not (DifferentiableAt ℝ g_1 0))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((F_1 x) = (f_1 (g_1 x))) ∧ ((f_1 (g_1 x)) = ((2 * (((2 /. 3) * x) - ((1 /. 3) * |(x)|))) + |((((2 /. 3) * x) - ((1 /. 3) * |(x)|)))|))) ∧ (((2 * (((2 /. 3) * x) - ((1 /. 3) * |(x)|))) + |((((2 /. 3) * x) - ((1 /. 3) * |(x)|)))|) = x)))))
  : DifferentiableAt ℝ F_1 0 := by
  sorry

theorem proof_gap_exercise_1016_3_6
  (h1 : f_1 = (fun (x : ℝ) => ((2 * x) + |(x)|)))
  (h2 : g_1 = (fun (x : ℝ) => (((2 /. 3) * x) - ((1 /. 3) * |(x)|))))
  (h3 : F_1 = (fun (x : ℝ) => (f_1 (g_1 x))))
  (h4 : (g_1 0) = 0)
  (h5 : Not (DifferentiableAt ℝ f_1 0))
  (h6 : Not (DifferentiableAt ℝ g_1 0))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((F_1 x) = (f_1 (g_1 x))) ∧ ((f_1 (g_1 x)) = ((2 * (((2 /. 3) * x) - ((1 /. 3) * |(x)|))) + |((((2 /. 3) * x) - ((1 /. 3) * |(x)|)))|))) ∧ (((2 * (((2 /. 3) * x) - ((1 /. 3) * |(x)|))) + |((((2 /. 3) * x) - ((1 /. 3) * |(x)|)))|) = x)))))
  (h8 : DifferentiableAt ℝ F_1 0)
  : (iteratedDeriv 1 (fun t => F_1 t) 0) = 1 := by
  sorry

theorem proof_gap_exercise_1016_3_7
  (h1 : f_1 = (fun (x : ℝ) => ((2 * x) + |(x)|)))
  (h2 : g_1 = (fun (x : ℝ) => (((2 /. 3) * x) - ((1 /. 3) * |(x)|))))
  (h3 : F_1 = (fun (x : ℝ) => (f_1 (g_1 x))))
  (h4 : (g_1 0) = 0)
  (h5 : Not (DifferentiableAt ℝ f_1 0))
  (h6 : Not (DifferentiableAt ℝ g_1 0))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((F_1 x) = (f_1 (g_1 x))) ∧ ((f_1 (g_1 x)) = ((2 * (((2 /. 3) * x) - ((1 /. 3) * |(x)|))) + |((((2 /. 3) * x) - ((1 /. 3) * |(x)|)))|))) ∧ (((2 * (((2 /. 3) * x) - ((1 /. 3) * |(x)|))) + |((((2 /. 3) * x) - ((1 /. 3) * |(x)|)))|) = x)))))
  (h8 : DifferentiableAt ℝ F_1 0)
  (h9 : (iteratedDeriv 1 (fun t => F_1 t) 0) = 1)
  (h10 : f_2 = (fun (x : ℝ) => |(x)|))
  (h11 : g_2 = (fun (x : ℝ) => |(x)|))
  (h12 : F_2 = (fun (x : ℝ) => (f_2 (g_2 x))))
  : (g_2 0) = 0 := by
  sorry

theorem proof_gap_exercise_1016_3_8
  (h1 : f_1 = (fun (x : ℝ) => ((2 * x) + |(x)|)))
  (h2 : g_1 = (fun (x : ℝ) => (((2 /. 3) * x) - ((1 /. 3) * |(x)|))))
  (h3 : F_1 = (fun (x : ℝ) => (f_1 (g_1 x))))
  (h4 : (g_1 0) = 0)
  (h5 : Not (DifferentiableAt ℝ f_1 0))
  (h6 : Not (DifferentiableAt ℝ g_1 0))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((F_1 x) = (f_1 (g_1 x))) ∧ ((f_1 (g_1 x)) = ((2 * (((2 /. 3) * x) - ((1 /. 3) * |(x)|))) + |((((2 /. 3) * x) - ((1 /. 3) * |(x)|)))|))) ∧ (((2 * (((2 /. 3) * x) - ((1 /. 3) * |(x)|))) + |((((2 /. 3) * x) - ((1 /. 3) * |(x)|)))|) = x)))))
  (h8 : DifferentiableAt ℝ F_1 0)
  (h9 : (iteratedDeriv 1 (fun t => F_1 t) 0) = 1)
  (h10 : f_2 = (fun (x : ℝ) => |(x)|))
  (h11 : g_2 = (fun (x : ℝ) => |(x)|))
  (h12 : F_2 = (fun (x : ℝ) => (f_2 (g_2 x))))
  (h13 : (g_2 0) = 0)
  : Not (DifferentiableAt ℝ f_2 0) := by
  sorry

theorem proof_gap_exercise_1016_3_9
  (h1 : f_1 = (fun (x : ℝ) => ((2 * x) + |(x)|)))
  (h2 : g_1 = (fun (x : ℝ) => (((2 /. 3) * x) - ((1 /. 3) * |(x)|))))
  (h3 : F_1 = (fun (x : ℝ) => (f_1 (g_1 x))))
  (h4 : (g_1 0) = 0)
  (h5 : Not (DifferentiableAt ℝ f_1 0))
  (h6 : Not (DifferentiableAt ℝ g_1 0))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((F_1 x) = (f_1 (g_1 x))) ∧ ((f_1 (g_1 x)) = ((2 * (((2 /. 3) * x) - ((1 /. 3) * |(x)|))) + |((((2 /. 3) * x) - ((1 /. 3) * |(x)|)))|))) ∧ (((2 * (((2 /. 3) * x) - ((1 /. 3) * |(x)|))) + |((((2 /. 3) * x) - ((1 /. 3) * |(x)|)))|) = x)))))
  (h8 : DifferentiableAt ℝ F_1 0)
  (h9 : (iteratedDeriv 1 (fun t => F_1 t) 0) = 1)
  (h10 : f_2 = (fun (x : ℝ) => |(x)|))
  (h11 : g_2 = (fun (x : ℝ) => |(x)|))
  (h12 : F_2 = (fun (x : ℝ) => (f_2 (g_2 x))))
  (h13 : (g_2 0) = 0)
  (h14 : Not (DifferentiableAt ℝ f_2 0))
  : Not (DifferentiableAt ℝ g_2 0) := by
  sorry

theorem proof_gap_exercise_1016_3_10
  (h1 : f_1 = (fun (x : ℝ) => ((2 * x) + |(x)|)))
  (h2 : g_1 = (fun (x : ℝ) => (((2 /. 3) * x) - ((1 /. 3) * |(x)|))))
  (h3 : F_1 = (fun (x : ℝ) => (f_1 (g_1 x))))
  (h4 : (g_1 0) = 0)
  (h5 : Not (DifferentiableAt ℝ f_1 0))
  (h6 : Not (DifferentiableAt ℝ g_1 0))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((F_1 x) = (f_1 (g_1 x))) ∧ ((f_1 (g_1 x)) = ((2 * (((2 /. 3) * x) - ((1 /. 3) * |(x)|))) + |((((2 /. 3) * x) - ((1 /. 3) * |(x)|)))|))) ∧ (((2 * (((2 /. 3) * x) - ((1 /. 3) * |(x)|))) + |((((2 /. 3) * x) - ((1 /. 3) * |(x)|)))|) = x)))))
  (h8 : DifferentiableAt ℝ F_1 0)
  (h9 : (iteratedDeriv 1 (fun t => F_1 t) 0) = 1)
  (h10 : f_2 = (fun (x : ℝ) => |(x)|))
  (h11 : g_2 = (fun (x : ℝ) => |(x)|))
  (h12 : F_2 = (fun (x : ℝ) => (f_2 (g_2 x))))
  (h13 : (g_2 0) = 0)
  (h14 : Not (DifferentiableAt ℝ f_2 0))
  (h15 : Not (DifferentiableAt ℝ g_2 0))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((F_2 x) = (f_2 (g_2 x))) ∧ ((f_2 (g_2 x)) = |(x)|)))) := by
  sorry

theorem proof_gap_exercise_1016_3_11
  (h1 : f_1 = (fun (x : ℝ) => ((2 * x) + |(x)|)))
  (h2 : g_1 = (fun (x : ℝ) => (((2 /. 3) * x) - ((1 /. 3) * |(x)|))))
  (h3 : F_1 = (fun (x : ℝ) => (f_1 (g_1 x))))
  (h4 : (g_1 0) = 0)
  (h5 : Not (DifferentiableAt ℝ f_1 0))
  (h6 : Not (DifferentiableAt ℝ g_1 0))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((F_1 x) = (f_1 (g_1 x))) ∧ ((f_1 (g_1 x)) = ((2 * (((2 /. 3) * x) - ((1 /. 3) * |(x)|))) + |((((2 /. 3) * x) - ((1 /. 3) * |(x)|)))|))) ∧ (((2 * (((2 /. 3) * x) - ((1 /. 3) * |(x)|))) + |((((2 /. 3) * x) - ((1 /. 3) * |(x)|)))|) = x)))))
  (h8 : DifferentiableAt ℝ F_1 0)
  (h9 : (iteratedDeriv 1 (fun t => F_1 t) 0) = 1)
  (h10 : f_2 = (fun (x : ℝ) => |(x)|))
  (h11 : g_2 = (fun (x : ℝ) => |(x)|))
  (h12 : F_2 = (fun (x : ℝ) => (f_2 (g_2 x))))
  (h13 : (g_2 0) = 0)
  (h14 : Not (DifferentiableAt ℝ f_2 0))
  (h15 : Not (DifferentiableAt ℝ g_2 0))
  (h16 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((F_2 x) = (f_2 (g_2 x))) ∧ ((f_2 (g_2 x)) = |(x)|)))))
  : Not (DifferentiableAt ℝ F_2 0) := by
  sorry

theorem proof_gap_exercise_1016_3_12
  (h1 : f_1 = (fun (x : ℝ) => ((2 * x) + |(x)|)))
  (h2 : g_1 = (fun (x : ℝ) => (((2 /. 3) * x) - ((1 /. 3) * |(x)|))))
  (h3 : F_1 = (fun (x : ℝ) => (f_1 (g_1 x))))
  (h4 : (g_1 0) = 0)
  (h5 : Not (DifferentiableAt ℝ f_1 0))
  (h6 : Not (DifferentiableAt ℝ g_1 0))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((F_1 x) = (f_1 (g_1 x))) ∧ ((f_1 (g_1 x)) = ((2 * (((2 /. 3) * x) - ((1 /. 3) * |(x)|))) + |((((2 /. 3) * x) - ((1 /. 3) * |(x)|)))|))) ∧ (((2 * (((2 /. 3) * x) - ((1 /. 3) * |(x)|))) + |((((2 /. 3) * x) - ((1 /. 3) * |(x)|)))|) = x)))))
  (h8 : DifferentiableAt ℝ F_1 0)
  (h9 : (iteratedDeriv 1 (fun t => F_1 t) 0) = 1)
  (h10 : f_2 = (fun (x : ℝ) => |(x)|))
  (h11 : g_2 = (fun (x : ℝ) => |(x)|))
  (h12 : F_2 = (fun (x : ℝ) => (f_2 (g_2 x))))
  (h13 : (g_2 0) = 0)
  (h14 : Not (DifferentiableAt ℝ f_2 0))
  (h15 : Not (DifferentiableAt ℝ g_2 0))
  (h16 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((F_2 x) = (f_2 (g_2 x))) ∧ ((f_2 (g_2 x)) = |(x)|)))))
  (h17 : Not (DifferentiableAt ℝ F_2 0))
  : (exists (f_1 : (ℝ -> ℝ)) (g_1 : (ℝ -> ℝ)) (F_1 : (ℝ -> ℝ)) (x_0 : ℝ), ((((True ∧ (x_0 ∈ (Set.univ : Set ℝ))) ∧ (Not (DifferentiableAt ℝ f_1 (g_1 x_0)))) ∧ (Not (DifferentiableAt ℝ g_1 x_0))) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((F_1 x) = (f_1 (g_1 x))) ∧ (DifferentiableAt ℝ F_1 x_0)))))) := by
  sorry

theorem proof_gap_exercise_1016_3_13
  (h1 : f_1 = (fun (x : ℝ) => ((2 * x) + |(x)|)))
  (h2 : g_1 = (fun (x : ℝ) => (((2 /. 3) * x) - ((1 /. 3) * |(x)|))))
  (h3 : F_1 = (fun (x : ℝ) => (f_1 (g_1 x))))
  (h4 : (g_1 0) = 0)
  (h5 : Not (DifferentiableAt ℝ f_1 0))
  (h6 : Not (DifferentiableAt ℝ g_1 0))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((F_1 x) = (f_1 (g_1 x))) ∧ ((f_1 (g_1 x)) = ((2 * (((2 /. 3) * x) - ((1 /. 3) * |(x)|))) + |((((2 /. 3) * x) - ((1 /. 3) * |(x)|)))|))) ∧ (((2 * (((2 /. 3) * x) - ((1 /. 3) * |(x)|))) + |((((2 /. 3) * x) - ((1 /. 3) * |(x)|)))|) = x)))))
  (h8 : DifferentiableAt ℝ F_1 0)
  (h9 : (iteratedDeriv 1 (fun t => F_1 t) 0) = 1)
  (h10 : f_2 = (fun (x : ℝ) => |(x)|))
  (h11 : g_2 = (fun (x : ℝ) => |(x)|))
  (h12 : F_2 = (fun (x : ℝ) => (f_2 (g_2 x))))
  (h13 : (g_2 0) = 0)
  (h14 : Not (DifferentiableAt ℝ f_2 0))
  (h15 : Not (DifferentiableAt ℝ g_2 0))
  (h16 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((F_2 x) = (f_2 (g_2 x))) ∧ ((f_2 (g_2 x)) = |(x)|)))))
  (h17 : Not (DifferentiableAt ℝ F_2 0))
  (h18 : (exists (f_1 : (ℝ -> ℝ)) (g_1 : (ℝ -> ℝ)) (F_1 : (ℝ -> ℝ)) (x_0 : ℝ), ((((True ∧ (x_0 ∈ (Set.univ : Set ℝ))) ∧ (Not (DifferentiableAt ℝ f_1 (g_1 x_0)))) ∧ (Not (DifferentiableAt ℝ g_1 x_0))) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((F_1 x) = (f_1 (g_1 x))) ∧ (DifferentiableAt ℝ F_1 x_0)))))))
  : (exists (f_2 : (ℝ -> ℝ)) (g_2 : (ℝ -> ℝ)) (F_2 : (ℝ -> ℝ)) (x_0 : ℝ), ((((True ∧ (x_0 ∈ (Set.univ : Set ℝ))) ∧ (Not (DifferentiableAt ℝ f_2 (g_2 x_0)))) ∧ (Not (DifferentiableAt ℝ g_2 x_0))) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((F_2 x) = (f_2 (g_2 x))) ∧ (Not (DifferentiableAt ℝ F_2 x_0))))))) := by
  sorry

theorem proof_gap_exercise_1016_3_14
  (h1 : f_1 = (fun (x : ℝ) => ((2 * x) + |(x)|)))
  (h2 : g_1 = (fun (x : ℝ) => (((2 /. 3) * x) - ((1 /. 3) * |(x)|))))
  (h3 : F_1 = (fun (x : ℝ) => (f_1 (g_1 x))))
  (h4 : (g_1 0) = 0)
  (h5 : Not (DifferentiableAt ℝ f_1 0))
  (h6 : Not (DifferentiableAt ℝ g_1 0))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((F_1 x) = (f_1 (g_1 x))) ∧ ((f_1 (g_1 x)) = ((2 * (((2 /. 3) * x) - ((1 /. 3) * |(x)|))) + |((((2 /. 3) * x) - ((1 /. 3) * |(x)|)))|))) ∧ (((2 * (((2 /. 3) * x) - ((1 /. 3) * |(x)|))) + |((((2 /. 3) * x) - ((1 /. 3) * |(x)|)))|) = x)))))
  (h8 : DifferentiableAt ℝ F_1 0)
  (h9 : (iteratedDeriv 1 (fun t => F_1 t) 0) = 1)
  (h10 : f_2 = (fun (x : ℝ) => |(x)|))
  (h11 : g_2 = (fun (x : ℝ) => |(x)|))
  (h12 : F_2 = (fun (x : ℝ) => (f_2 (g_2 x))))
  (h13 : (g_2 0) = 0)
  (h14 : Not (DifferentiableAt ℝ f_2 0))
  (h15 : Not (DifferentiableAt ℝ g_2 0))
  (h16 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((F_2 x) = (f_2 (g_2 x))) ∧ ((f_2 (g_2 x)) = |(x)|)))))
  (h17 : Not (DifferentiableAt ℝ F_2 0))
  (h18 : (exists (f_1 : (ℝ -> ℝ)) (g_1 : (ℝ -> ℝ)) (F_1 : (ℝ -> ℝ)) (x_0 : ℝ), ((((True ∧ (x_0 ∈ (Set.univ : Set ℝ))) ∧ (Not (DifferentiableAt ℝ f_1 (g_1 x_0)))) ∧ (Not (DifferentiableAt ℝ g_1 x_0))) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((F_1 x) = (f_1 (g_1 x))) ∧ (DifferentiableAt ℝ F_1 x_0)))))))
  (h19 : (exists (f_2 : (ℝ -> ℝ)) (g_2 : (ℝ -> ℝ)) (F_2 : (ℝ -> ℝ)) (x_0 : ℝ), ((((True ∧ (x_0 ∈ (Set.univ : Set ℝ))) ∧ (Not (DifferentiableAt ℝ f_2 (g_2 x_0)))) ∧ (Not (DifferentiableAt ℝ g_2 x_0))) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((F_2 x) = (f_2 (g_2 x))) ∧ (Not (DifferentiableAt ℝ F_2 x_0))))))))
  : (exists (f_1 : (ℝ -> ℝ)) (g_1 : (ℝ -> ℝ)) (F_1 : (ℝ -> ℝ)) (x_0 : ℝ), ((((True ∧ (x_0 ∈ (Set.univ : Set ℝ))) ∧ (Not (DifferentiableAt ℝ f_1 (g_1 x_0)))) ∧ (Not (DifferentiableAt ℝ g_1 x_0))) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((F_1 x) = (f_1 (g_1 x))) ∧ (DifferentiableAt ℝ F_1 x_0)))))) ∧ (exists (f_2 : (ℝ -> ℝ)) (g_2 : (ℝ -> ℝ)) (F_2 : (ℝ -> ℝ)) (x_0 : ℝ), ((((True ∧ (x_0 ∈ (Set.univ : Set ℝ))) ∧ (Not (DifferentiableAt ℝ f_2 (g_2 x_0)))) ∧ (Not (DifferentiableAt ℝ g_2 x_0))) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((F_2 x) = (f_2 (g_2 x))) ∧ (Not (DifferentiableAt ℝ F_2 x_0))))))) := by
  sorry

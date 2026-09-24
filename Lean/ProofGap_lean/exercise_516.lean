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

-- exercise: exercise_516

theorem proof_gap_exercise_516_1
  (a_1 : ℝ)
  (a_2 : ℝ)
  (b_1 : ℝ)
  (b_2 : ℝ)
  (h1 : a_1 ∈ (Set.univ : Set ℝ))
  (h2 : a_2 ∈ (Set.univ : Set ℝ))
  (h3 : b_1 ∈ (Set.univ : Set ℝ))
  (h4 : b_2 ∈ (Set.univ : Set ℝ))
  (h5 : a_1 > 0)
  (h6 : a_2 > 0)
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((Real.rpow (((a_1 * x) + b_1) /. ((a_2 * x) + b_2)) x) = ((Real.rpow (a_1 /. a_2) x) * (Real.rpow ((x + (b_1 /. a_1)) /. (x + (b_2 /. a_2))) x))))) := by
  sorry

theorem proof_gap_exercise_516_2
  (a_1 : ℝ)
  (a_2 : ℝ)
  (b_1 : ℝ)
  (b_2 : ℝ)
  (h1 : a_1 ∈ (Set.univ : Set ℝ))
  (h2 : a_2 ∈ (Set.univ : Set ℝ))
  (h3 : b_1 ∈ (Set.univ : Set ℝ))
  (h4 : b_2 ∈ (Set.univ : Set ℝ))
  (h5 : a_1 > 0)
  (h6 : a_2 > 0)
  (h7 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (((a_1 * x) + b_1) > 0)) ∧ (((a_2 * x) + b_2) > 0)) → ((Real.rpow (((a_1 * x) + b_1) /. ((a_2 * x) + b_2)) x) = ((Real.rpow (a_1 /. a_2) x) * (Real.rpow ((x + (b_1 /. a_1)) /. (x + (b_2 /. a_2))) x))))))
  : (a_1 = a_2) → (Tendsto (fun x : ℝ => (Real.rpow (((a_1 * x) + b_1) /. ((a_2 * x) + b_2)) x)) atTop (𝓝 (Real.exp ((b_1 - b_2) /. a_1)))) := by
  sorry

theorem proof_gap_exercise_516_3
  (a_1 : ℝ)
  (a_2 : ℝ)
  (b_1 : ℝ)
  (b_2 : ℝ)
  (h1 : a_1 ∈ (Set.univ : Set ℝ))
  (h2 : a_2 ∈ (Set.univ : Set ℝ))
  (h3 : b_1 ∈ (Set.univ : Set ℝ))
  (h4 : b_2 ∈ (Set.univ : Set ℝ))
  (h5 : a_1 > 0)
  (h6 : a_2 > 0)
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((Real.rpow (((a_1 * x) + b_1) /. ((a_2 * x) + b_2)) x) = ((Real.rpow (a_1 /. a_2) x) * (Real.rpow ((x + (b_1 /. a_1)) /. (x + (b_2 /. a_2))) x))))))
  (h8 : (a_1 = a_2) → (Tendsto (fun x : ℝ => (Real.rpow (((a_1 * x) + b_1) /. ((a_2 * x) + b_2)) x)) atTop (𝓝 (Real.exp ((b_1 - b_2) /. a_1)))))
  : (a_1 < a_2) → (0 < (a_1 /. a_2)) := by
  sorry

theorem proof_gap_exercise_516_4
  (a_1 : ℝ)
  (a_2 : ℝ)
  (b_1 : ℝ)
  (b_2 : ℝ)
  (h1 : a_1 ∈ (Set.univ : Set ℝ))
  (h2 : a_2 ∈ (Set.univ : Set ℝ))
  (h3 : b_1 ∈ (Set.univ : Set ℝ))
  (h4 : b_2 ∈ (Set.univ : Set ℝ))
  (h5 : a_1 > 0)
  (h6 : a_2 > 0)
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((Real.rpow (((a_1 * x) + b_1) /. ((a_2 * x) + b_2)) x) = ((Real.rpow (a_1 /. a_2) x) * (Real.rpow ((x + (b_1 /. a_1)) /. (x + (b_2 /. a_2))) x))))))
  (h8 : (a_1 = a_2) → (Tendsto (fun x : ℝ => (Real.rpow (((a_1 * x) + b_1) /. ((a_2 * x) + b_2)) x)) atTop (𝓝 (Real.exp ((b_1 - b_2) /. a_1)))))
  (h9 : (a_1 < a_2) → (0 < (a_1 /. a_2)))
  : (a_1 < a_2) → ((a_1 /. a_2) < 1) := by
  sorry

theorem proof_gap_exercise_516_5
  (a_1 : ℝ)
  (a_2 : ℝ)
  (b_1 : ℝ)
  (b_2 : ℝ)
  (h1 : a_1 ∈ (Set.univ : Set ℝ))
  (h2 : a_2 ∈ (Set.univ : Set ℝ))
  (h3 : b_1 ∈ (Set.univ : Set ℝ))
  (h4 : b_2 ∈ (Set.univ : Set ℝ))
  (h5 : a_1 > 0)
  (h6 : a_2 > 0)
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((Real.rpow (((a_1 * x) + b_1) /. ((a_2 * x) + b_2)) x) = ((Real.rpow (a_1 /. a_2) x) * (Real.rpow ((x + (b_1 /. a_1)) /. (x + (b_2 /. a_2))) x))))))
  (h8 : (a_1 = a_2) → (Tendsto (fun x : ℝ => (Real.rpow (((a_1 * x) + b_1) /. ((a_2 * x) + b_2)) x)) atTop (𝓝 (Real.exp ((b_1 - b_2) /. a_1)))))
  (h9 : (a_1 < a_2) → (0 < (a_1 /. a_2)))
  (h10 : (a_1 < a_2) → ((a_1 /. a_2) < 1))
  : (a_1 < a_2) → (0 < 1) := by
  sorry

theorem proof_gap_exercise_516_6
  (a_1 : ℝ)
  (a_2 : ℝ)
  (b_1 : ℝ)
  (b_2 : ℝ)
  (h1 : a_1 ∈ (Set.univ : Set ℝ))
  (h2 : a_2 ∈ (Set.univ : Set ℝ))
  (h3 : b_1 ∈ (Set.univ : Set ℝ))
  (h4 : b_2 ∈ (Set.univ : Set ℝ))
  (h5 : a_1 > 0)
  (h6 : a_2 > 0)
  (h7 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (((a_1 * x) + b_1) > 0)) ∧ (((a_2 * x) + b_2) > 0)) → ((Real.rpow (((a_1 * x) + b_1) /. ((a_2 * x) + b_2)) x) = ((Real.rpow (a_1 /. a_2) x) * (Real.rpow ((x + (b_1 /. a_1)) /. (x + (b_2 /. a_2))) x))))))
  (h8 : (a_1 = a_2) → (Tendsto (fun x : ℝ => (Real.rpow (((a_1 * x) + b_1) /. ((a_2 * x) + b_2)) x)) atTop (𝓝 (Real.exp ((b_1 - b_2) /. a_1)))))
  (h9 : (a_1 < a_2) → (0 < (a_1 /. a_2)))
  (h10 : (a_1 < a_2) → ((a_1 /. a_2) < 1))
  (h11 : (a_1 < a_2) → (0 < 1))
  : (a_1 < a_2) → (Tendsto (fun x : ℝ => (Real.rpow (a_1 /. a_2) x)) atTop (𝓝 0)) := by
  sorry

theorem proof_gap_exercise_516_7
  (a_1 : ℝ)
  (a_2 : ℝ)
  (b_1 : ℝ)
  (b_2 : ℝ)
  (h1 : a_1 ∈ (Set.univ : Set ℝ))
  (h2 : a_2 ∈ (Set.univ : Set ℝ))
  (h3 : b_1 ∈ (Set.univ : Set ℝ))
  (h4 : b_2 ∈ (Set.univ : Set ℝ))
  (h5 : a_1 > 0)
  (h6 : a_2 > 0)
  (h7 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (((a_1 * x) + b_1) > 0)) ∧ (((a_2 * x) + b_2) > 0)) → ((Real.rpow (((a_1 * x) + b_1) /. ((a_2 * x) + b_2)) x) = ((Real.rpow (a_1 /. a_2) x) * (Real.rpow ((x + (b_1 /. a_1)) /. (x + (b_2 /. a_2))) x))))))
  (h8 : (a_1 = a_2) → (Tendsto (fun x : ℝ => (Real.rpow (((a_1 * x) + b_1) /. ((a_2 * x) + b_2)) x)) atTop (𝓝 (Real.exp ((b_1 - b_2) /. a_1)))))
  (h9 : (a_1 < a_2) → (0 < (a_1 /. a_2)))
  (h10 : (a_1 < a_2) → ((a_1 /. a_2) < 1))
  (h11 : (a_1 < a_2) → (0 < 1))
  (h12 : (a_1 < a_2) → (Tendsto (fun x : ℝ => (Real.rpow (a_1 /. a_2) x)) atTop (𝓝 0)))
  : (a_1 < a_2) → (Tendsto (fun x : ℝ => (Real.rpow ((x + (b_1 /. a_1)) /. (x + (b_2 /. a_2))) x)) atTop (𝓝 (Real.exp ((b_1 /. a_1) - (b_2 /. a_2))))) := by
  sorry

theorem proof_gap_exercise_516_8
  (a_1 : ℝ)
  (a_2 : ℝ)
  (b_1 : ℝ)
  (b_2 : ℝ)
  (h1 : a_1 ∈ (Set.univ : Set ℝ))
  (h2 : a_2 ∈ (Set.univ : Set ℝ))
  (h3 : b_1 ∈ (Set.univ : Set ℝ))
  (h4 : b_2 ∈ (Set.univ : Set ℝ))
  (h5 : a_1 > 0)
  (h6 : a_2 > 0)
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((Real.rpow (((a_1 * x) + b_1) /. ((a_2 * x) + b_2)) x) = ((Real.rpow (a_1 /. a_2) x) * (Real.rpow ((x + (b_1 /. a_1)) /. (x + (b_2 /. a_2))) x))))))
  (h8 : (a_1 = a_2) → (Tendsto (fun x : ℝ => (Real.rpow (((a_1 * x) + b_1) /. ((a_2 * x) + b_2)) x)) atTop (𝓝 (Real.exp ((b_1 - b_2) /. a_1)))))
  (h9 : (a_1 < a_2) → (0 < (a_1 /. a_2)))
  (h10 : (a_1 < a_2) → ((a_1 /. a_2) < 1))
  (h11 : (a_1 < a_2) → (0 < 1))
  (h12 : (a_1 < a_2) → (Tendsto (fun x : ℝ => (Real.rpow (a_1 /. a_2) x)) atTop (𝓝 0)))
  (h13 : (a_1 < a_2) → (Tendsto (fun x : ℝ => (Real.rpow ((x + (b_1 /. a_1)) /. (x + (b_2 /. a_2))) x)) atTop (𝓝 (Real.exp ((b_1 /. a_1) - (b_2 /. a_2))))))
  : (a_1 < a_2) → (Tendsto (fun x : ℝ => (Real.rpow (((a_1 * x) + b_1) /. ((a_2 * x) + b_2)) x)) atTop (𝓝 0)) := by
  sorry

theorem proof_gap_exercise_516_9
  (a_1 : ℝ)
  (a_2 : ℝ)
  (b_1 : ℝ)
  (b_2 : ℝ)
  (h1 : a_1 ∈ (Set.univ : Set ℝ))
  (h2 : a_2 ∈ (Set.univ : Set ℝ))
  (h3 : b_1 ∈ (Set.univ : Set ℝ))
  (h4 : b_2 ∈ (Set.univ : Set ℝ))
  (h5 : a_1 > 0)
  (h6 : a_2 > 0)
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((Real.rpow (((a_1 * x) + b_1) /. ((a_2 * x) + b_2)) x) = ((Real.rpow (a_1 /. a_2) x) * (Real.rpow ((x + (b_1 /. a_1)) /. (x + (b_2 /. a_2))) x))))))
  (h8 : (a_1 = a_2) → (Tendsto (fun x : ℝ => (Real.rpow (((a_1 * x) + b_1) /. ((a_2 * x) + b_2)) x)) atTop (𝓝 (Real.exp ((b_1 - b_2) /. a_1)))))
  (h9 : (a_1 < a_2) → (0 < (a_1 /. a_2)))
  (h10 : (a_1 < a_2) → ((a_1 /. a_2) < 1))
  (h11 : (a_1 < a_2) → (0 < 1))
  (h12 : (a_1 < a_2) → (Tendsto (fun x : ℝ => (Real.rpow (a_1 /. a_2) x)) atTop (𝓝 0)))
  (h13 : (a_1 < a_2) → (Tendsto (fun x : ℝ => (Real.rpow ((x + (b_1 /. a_1)) /. (x + (b_2 /. a_2))) x)) atTop (𝓝 (Real.exp ((b_1 /. a_1) - (b_2 /. a_2))))))
  (h14 : (a_1 < a_2) → (Tendsto (fun x : ℝ => (Real.rpow (((a_1 * x) + b_1) /. ((a_2 * x) + b_2)) x)) atTop (𝓝 0)))
  : (a_1 > a_2) → ((a_1 /. a_2) > 1) := by
  sorry

theorem proof_gap_exercise_516_10
  (a_1 : ℝ)
  (a_2 : ℝ)
  (b_1 : ℝ)
  (b_2 : ℝ)
  (h1 : a_1 ∈ (Set.univ : Set ℝ))
  (h2 : a_2 ∈ (Set.univ : Set ℝ))
  (h3 : b_1 ∈ (Set.univ : Set ℝ))
  (h4 : b_2 ∈ (Set.univ : Set ℝ))
  (h5 : a_1 > 0)
  (h6 : a_2 > 0)
  (h7 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (((a_1 * x) + b_1) > 0)) ∧ (((a_2 * x) + b_2) > 0)) → ((Real.rpow (((a_1 * x) + b_1) /. ((a_2 * x) + b_2)) x) = ((Real.rpow (a_1 /. a_2) x) * (Real.rpow ((x + (b_1 /. a_1)) /. (x + (b_2 /. a_2))) x))))))
  (h8 : (a_1 = a_2) → (Tendsto (fun x : ℝ => (Real.rpow (((a_1 * x) + b_1) /. ((a_2 * x) + b_2)) x)) atTop (𝓝 (Real.exp ((b_1 - b_2) /. a_1)))))
  (h9 : (a_1 < a_2) → (0 < (a_1 /. a_2)))
  (h10 : (a_1 < a_2) → ((a_1 /. a_2) < 1))
  (h11 : (a_1 < a_2) → (0 < 1))
  (h12 : (a_1 < a_2) → (Tendsto (fun x : ℝ => (Real.rpow (a_1 /. a_2) x)) atTop (𝓝 0)))
  (h13 : (a_1 < a_2) → (Tendsto (fun x : ℝ => (Real.rpow ((x + (b_1 /. a_1)) /. (x + (b_2 /. a_2))) x)) atTop (𝓝 (Real.exp ((b_1 /. a_1) - (b_2 /. a_2))))))
  (h14 : (a_1 < a_2) → (Tendsto (fun x : ℝ => (Real.rpow (((a_1 * x) + b_1) /. ((a_2 * x) + b_2)) x)) atTop (𝓝 0)))
  (h15 : (a_1 > a_2) → ((a_1 /. a_2) > 1))
  : (a_1 > a_2) → (Tendsto (fun x : ℝ => ((Real.rpow (a_1 /. a_2) x) : EReal)) atTop (𝓝 ⊤)) := by
  sorry

theorem proof_gap_exercise_516_11
  (a_1 : ℝ)
  (a_2 : ℝ)
  (b_1 : ℝ)
  (b_2 : ℝ)
  (h1 : a_1 ∈ (Set.univ : Set ℝ))
  (h2 : a_2 ∈ (Set.univ : Set ℝ))
  (h3 : b_1 ∈ (Set.univ : Set ℝ))
  (h4 : b_2 ∈ (Set.univ : Set ℝ))
  (h5 : a_1 > 0)
  (h6 : a_2 > 0)
  (h7 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (((a_1 * x) + b_1) > 0)) ∧ (((a_2 * x) + b_2) > 0)) → ((Real.rpow (((a_1 * x) + b_1) /. ((a_2 * x) + b_2)) x) = ((Real.rpow (a_1 /. a_2) x) * (Real.rpow ((x + (b_1 /. a_1)) /. (x + (b_2 /. a_2))) x))))))
  (h8 : (a_1 = a_2) → (Tendsto (fun x : ℝ => (Real.rpow (((a_1 * x) + b_1) /. ((a_2 * x) + b_2)) x)) atTop (𝓝 (Real.exp ((b_1 - b_2) /. a_1)))))
  (h9 : (a_1 < a_2) → (0 < (a_1 /. a_2)))
  (h10 : (a_1 < a_2) → ((a_1 /. a_2) < 1))
  (h11 : (a_1 < a_2) → (0 < 1))
  (h12 : (a_1 < a_2) → (Tendsto (fun x : ℝ => (Real.rpow (a_1 /. a_2) x)) atTop (𝓝 0)))
  (h13 : (a_1 < a_2) → (Tendsto (fun x : ℝ => (Real.rpow ((x + (b_1 /. a_1)) /. (x + (b_2 /. a_2))) x)) atTop (𝓝 (Real.exp ((b_1 /. a_1) - (b_2 /. a_2))))))
  (h14 : (a_1 < a_2) → (Tendsto (fun x : ℝ => (Real.rpow (((a_1 * x) + b_1) /. ((a_2 * x) + b_2)) x)) atTop (𝓝 0)))
  (h15 : (a_1 > a_2) → ((a_1 /. a_2) > 1))
  (h16 : (a_1 > a_2) → (Tendsto (fun x : ℝ => ((Real.rpow (a_1 /. a_2) x) : EReal)) atTop (𝓝 ⊤)))
  : (a_1 > a_2) → (Tendsto (fun x : ℝ => ((Real.rpow (((a_1 * x) + b_1) /. ((a_2 * x) + b_2)) x) : EReal)) atTop (𝓝 ⊤)) := by
  sorry

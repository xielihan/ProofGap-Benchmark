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

-- exercise: exercise_2475

theorem proof_gap_exercise_2475_1
  (f : (ℝ -> ℝ))
  (g : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (V_x : ℝ)
  (V_y : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : V_x ∈ (Set.univ : Set ℝ))
  (h4 : V_y ∈ (Set.univ : Set ℝ))
  (h5 : a > 0)
  (h6 : b > 0)
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (b * ((x /. a) ^ (2 : ℕ)))))))
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((g x) = (b * |((x /. a))|)))))
  : (f a) = (g a) := by
  sorry

theorem proof_gap_exercise_2475_2
  (f : (ℝ -> ℝ))
  (g : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (V_x : ℝ)
  (V_y : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : V_x ∈ (Set.univ : Set ℝ))
  (h4 : V_y ∈ (Set.univ : Set ℝ))
  (h5 : a > 0)
  (h6 : b > 0)
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (b * ((x /. a) ^ (2 : ℕ)))))))
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((g x) = (b * |((x /. a))|)))))
  (h9 : (f a) = (g a))
  : (f (-a)) = (g (-a)) := by
  sorry

theorem proof_gap_exercise_2475_3
  (f : (ℝ -> ℝ))
  (g : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (V_x : ℝ)
  (V_y : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : V_x ∈ (Set.univ : Set ℝ))
  (h4 : V_y ∈ (Set.univ : Set ℝ))
  (h5 : a > 0)
  (h6 : b > 0)
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (b * ((x /. a) ^ (2 : ℕ)))))))
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((g x) = (b * |((x /. a))|)))))
  (h9 : (f a) = (g a))
  (h10 : (f (-a)) = (g (-a)))
  (h11 : V_x = ((((4 * Real.pi) /. 15) * a) * (b ^ (2 : ℕ))))
  : V_x = ((2 * Real.pi) * (∫ x in (0 : ℝ)..a, ((((b ^ (2 : ℕ)) * ((x ^ (2 : ℕ)) /. (a ^ (2 : ℕ)))) - ((b ^ (2 : ℕ)) * ((x ^ (4 : ℕ)) /. (a ^ (4 : ℕ))))) * (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_2475_4
  (f : (ℝ -> ℝ))
  (g : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (V_x : ℝ)
  (V_y : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : V_x ∈ (Set.univ : Set ℝ))
  (h4 : V_y ∈ (Set.univ : Set ℝ))
  (h5 : a > 0)
  (h6 : b > 0)
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (b * ((x /. a) ^ (2 : ℕ)))))))
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((g x) = (b * |((x /. a))|)))))
  (h9 : (f a) = (g a))
  (h10 : (f (-a)) = (g (-a)))
  (h11 : V_x = ((2 * Real.pi) * (∫ x in (0 : ℝ)..a, ((((b ^ (2 : ℕ)) * ((x ^ (2 : ℕ)) /. (a ^ (2 : ℕ)))) - ((b ^ (2 : ℕ)) * ((x ^ (4 : ℕ)) /. (a ^ (4 : ℕ))))) * (1 : ℝ)))))
  : V_x = ((((4 * Real.pi) /. 15) * a) * (b ^ (2 : ℕ))) := by
  sorry

theorem proof_gap_exercise_2475_5
  (f : (ℝ -> ℝ))
  (g : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (V_x : ℝ)
  (V_y : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : V_x ∈ (Set.univ : Set ℝ))
  (h4 : V_y ∈ (Set.univ : Set ℝ))
  (h5 : a > 0)
  (h6 : b > 0)
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (b * ((x /. a) ^ (2 : ℕ)))))))
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((g x) = (b * |((x /. a))|)))))
  (h9 : (f a) = (g a))
  (h10 : (f (-a)) = (g (-a)))
  (h11 : V_x = ((2 * Real.pi) * (∫ x in (0 : ℝ)..a, ((((b ^ (2 : ℕ)) * ((x ^ (2 : ℕ)) /. (a ^ (2 : ℕ)))) - ((b ^ (2 : ℕ)) * ((x ^ (4 : ℕ)) /. (a ^ (4 : ℕ))))) * (1 : ℝ)))))
  (h12 : V_x = ((((4 * Real.pi) /. 15) * a) * (b ^ (2 : ℕ))))
  (h13 : V_y = (((Real.pi * (a ^ (2 : ℕ))) * b) /. 6))
  : V_y = (Real.pi * (∫ y in (0 : ℝ)..b, (((((a ^ (2 : ℕ)) * y) /. b) - (((a ^ (2 : ℕ)) * (y ^ (2 : ℕ))) /. (b ^ (2 : ℕ)))) * (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_2475_6
  (f : (ℝ -> ℝ))
  (g : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (V_x : ℝ)
  (V_y : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : V_x ∈ (Set.univ : Set ℝ))
  (h4 : V_y ∈ (Set.univ : Set ℝ))
  (h5 : a > 0)
  (h6 : b > 0)
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (b * ((x /. a) ^ (2 : ℕ)))))))
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((g x) = (b * |((x /. a))|)))))
  (h9 : (f a) = (g a))
  (h10 : (f (-a)) = (g (-a)))
  (h11 : V_x = ((2 * Real.pi) * (∫ x in (0 : ℝ)..a, ((((b ^ (2 : ℕ)) * ((x ^ (2 : ℕ)) /. (a ^ (2 : ℕ)))) - ((b ^ (2 : ℕ)) * ((x ^ (4 : ℕ)) /. (a ^ (4 : ℕ))))) * (1 : ℝ)))))
  (h12 : V_x = ((((4 * Real.pi) /. 15) * a) * (b ^ (2 : ℕ))))
  (h13 : V_y = (Real.pi * (∫ y in (0 : ℝ)..b, (((((a ^ (2 : ℕ)) * y) /. b) - (((a ^ (2 : ℕ)) * (y ^ (2 : ℕ))) /. (b ^ (2 : ℕ)))) * (1 : ℝ)))))
  : V_y = (((Real.pi * (a ^ (2 : ℕ))) * b) /. 6) := by
  sorry

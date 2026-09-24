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

-- exercise: exercise_479

theorem proof_gap_exercise_479_1
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (Real.cos (2 * x)) ≠ 0)
  (h3 : (Real.cos ((Real.pi /. 4) - x)) ≠ 0)
  : (∃ L : ℝ, Tendsto (fun x_1 : ℝ => (((Real.sin (2 * x_1)) * (Real.sin ((Real.pi /. 4) - x_1))) /. ((Real.cos (2 * x_1)) * (Real.cos ((Real.pi /. 4) - x_1))))) (𝓝[≠] (Real.pi /. 4)) (𝓝 L) ∧ (Tendsto (fun x_1 : ℝ => ((Real.tan (2 * x_1)) * (Real.tan ((Real.pi /. 4) - x_1)))) (𝓝[≠] (Real.pi /. 4)) (𝓝 ((𝓝[≠] (Real.pi /. 4)).limUnder (fun x_1 : ℝ => (((Real.sin (2 * x_1)) * (Real.sin ((Real.pi /. 4) - x_1))) /. ((Real.cos (2 * x_1)) * (Real.cos ((Real.pi /. 4) - x_1))))))))) := by
  sorry

theorem proof_gap_exercise_479_2
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (Real.cos (2 * x)) ≠ 0)
  (h3 : (Real.cos ((Real.pi /. 4) - x)) ≠ 0)
  (h4 : Tendsto (fun x_1 : ℝ => ((Real.tan (2 * x_1)) * (Real.tan ((Real.pi /. 4) - x_1)))) (𝓝[≠] (Real.pi /. 4)) (𝓝 ((𝓝[≠] (Real.pi /. 4)).limUnder (fun x_1 : ℝ => (((Real.sin (2 * x_1)) * (Real.sin ((Real.pi /. 4) - x_1))) /. ((Real.cos (2 * x_1)) * (Real.cos ((Real.pi /. 4) - x_1))))))))
  (h5 : x = ((Real.pi /. 4) + y))
  (h6 : ∃ L : ℝ, Tendsto (fun x_1 : ℝ => (((Real.sin (2 * x_1)) * (Real.sin ((Real.pi /. 4) - x_1))) /. ((Real.cos (2 * x_1)) * (Real.cos ((Real.pi /. 4) - x_1))))) (𝓝[≠] (Real.pi /. 4)) (𝓝 L))
  : y ∈ (Set.univ : Set ℝ) := by
  sorry

theorem proof_gap_exercise_479_3
  (x : ℝ)
  (y : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (Real.cos (2 * x)) ≠ 0)
  (h3 : (Real.cos ((Real.pi /. 4) - x)) ≠ 0)
  (h4 : Tendsto (fun x_1 : ℝ => ((Real.tan (2 * x_1)) * (Real.tan ((Real.pi /. 4) - x_1)))) (𝓝[≠] (Real.pi /. 4)) (𝓝 ((𝓝[≠] (Real.pi /. 4)).limUnder (fun x_1 : ℝ => (((Real.sin (2 * x_1)) * (Real.sin ((Real.pi /. 4) - x_1))) /. ((Real.cos (2 * x_1)) * (Real.cos ((Real.pi /. 4) - x_1))))))))
  (h5 : x = ((Real.pi /. 4) + y))
  (h6 : y ∈ (Set.univ : Set ℝ))
  (h7 : ∃ L : ℝ, Tendsto (fun x_1 : ℝ => (((Real.sin (2 * x_1)) * (Real.sin ((Real.pi /. 4) - x_1))) /. ((Real.cos (2 * x_1)) * (Real.cos ((Real.pi /. 4) - x_1))))) (𝓝[≠] (Real.pi /. 4)) (𝓝 L))
  : y ≠ 0 := by
  sorry

theorem proof_gap_exercise_479_4
  (x : ℝ)
  (y : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (Real.cos (2 * x)) ≠ 0)
  (h3 : (Real.cos ((Real.pi /. 4) - x)) ≠ 0)
  (h4 : Tendsto (fun x_1 : ℝ => ((Real.tan (2 * x_1)) * (Real.tan ((Real.pi /. 4) - x_1)))) (𝓝[≠] (Real.pi /. 4)) (𝓝 ((𝓝[≠] (Real.pi /. 4)).limUnder (fun x_1 : ℝ => (((Real.sin (2 * x_1)) * (Real.sin ((Real.pi /. 4) - x_1))) /. ((Real.cos (2 * x_1)) * (Real.cos ((Real.pi /. 4) - x_1))))))))
  (h5 : x = ((Real.pi /. 4) + y))
  (h6 : y ∈ (Set.univ : Set ℝ))
  (h7 : y ≠ 0)
  (h8 : ∃ L : ℝ, Tendsto (fun x_1 : ℝ => (((Real.sin (2 * x_1)) * (Real.sin ((Real.pi /. 4) - x_1))) /. ((Real.cos (2 * x_1)) * (Real.cos ((Real.pi /. 4) - x_1))))) (𝓝[≠] (Real.pi /. 4)) (𝓝 L))
  : (Real.sin (2 * y)) ≠ 0 := by
  sorry

theorem proof_gap_exercise_479_5
  (x : ℝ)
  (y : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (Real.cos (2 * x)) ≠ 0)
  (h3 : (Real.cos ((Real.pi /. 4) - x)) ≠ 0)
  (h4 : Tendsto (fun x_1 : ℝ => ((Real.tan (2 * x_1)) * (Real.tan ((Real.pi /. 4) - x_1)))) (𝓝[≠] (Real.pi /. 4)) (𝓝 ((𝓝[≠] (Real.pi /. 4)).limUnder (fun x_1 : ℝ => (((Real.sin (2 * x_1)) * (Real.sin ((Real.pi /. 4) - x_1))) /. ((Real.cos (2 * x_1)) * (Real.cos ((Real.pi /. 4) - x_1))))))))
  (h5 : x = ((Real.pi /. 4) + y))
  (h6 : y ∈ (Set.univ : Set ℝ))
  (h7 : y ≠ 0)
  (h8 : (Real.sin (2 * y)) ≠ 0)
  (h9 : ∃ L : ℝ, Tendsto (fun x_1 : ℝ => (((Real.sin (2 * x_1)) * (Real.sin ((Real.pi /. 4) - x_1))) /. ((Real.cos (2 * x_1)) * (Real.cos ((Real.pi /. 4) - x_1))))) (𝓝[≠] (Real.pi /. 4)) (𝓝 L))
  : (Real.cos y) ≠ 0 := by
  sorry

theorem proof_gap_exercise_479_6
  (x : ℝ)
  (y : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (Real.cos (2 * x)) ≠ 0)
  (h3 : (Real.cos ((Real.pi /. 4) - x)) ≠ 0)
  (h4 : Tendsto (fun x_1 : ℝ => ((Real.tan (2 * x_1)) * (Real.tan ((Real.pi /. 4) - x_1)))) (𝓝[≠] (Real.pi /. 4)) (𝓝 ((𝓝[≠] (Real.pi /. 4)).limUnder (fun x_1 : ℝ => (((Real.sin (2 * x_1)) * (Real.sin ((Real.pi /. 4) - x_1))) /. ((Real.cos (2 * x_1)) * (Real.cos ((Real.pi /. 4) - x_1))))))))
  (h5 : x = ((Real.pi /. 4) + y))
  (h6 : y ∈ (Set.univ : Set ℝ))
  (h7 : y ≠ 0)
  (h8 : (Real.sin (2 * y)) ≠ 0)
  (h9 : (Real.cos y) ≠ 0)
  (h10 : ∃ L : ℝ, Tendsto (fun x_1 : ℝ => (((Real.sin (2 * x_1)) * (Real.sin ((Real.pi /. 4) - x_1))) /. ((Real.cos (2 * x_1)) * (Real.cos ((Real.pi /. 4) - x_1))))) (𝓝[≠] (Real.pi /. 4)) (𝓝 L))
  : (∃ L : ℝ, Tendsto (fun y_1 : ℝ => (((Real.cos (2 * y_1)) * (Real.sin y_1)) /. ((Real.sin (2 * y_1)) * (Real.cos y_1)))) (𝓝[≠] 0) (𝓝 L) ∧ (Tendsto (fun x_1 : ℝ => (((Real.sin (2 * x_1)) * (Real.sin ((Real.pi /. 4) - x_1))) /. ((Real.cos (2 * x_1)) * (Real.cos ((Real.pi /. 4) - x_1))))) (𝓝[≠] (Real.pi /. 4)) (𝓝 ((𝓝[≠] 0).limUnder (fun y_1 : ℝ => (((Real.cos (2 * y_1)) * (Real.sin y_1)) /. ((Real.sin (2 * y_1)) * (Real.cos y_1)))))))) := by
  sorry

theorem proof_gap_exercise_479_7
  (x : ℝ)
  (y : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (Real.cos (2 * x)) ≠ 0)
  (h3 : (Real.cos ((Real.pi /. 4) - x)) ≠ 0)
  (h4 : Tendsto (fun x_1 : ℝ => ((Real.tan (2 * x_1)) * (Real.tan ((Real.pi /. 4) - x_1)))) (𝓝[≠] (Real.pi /. 4)) (𝓝 ((𝓝[≠] (Real.pi /. 4)).limUnder (fun x_1 : ℝ => (((Real.sin (2 * x_1)) * (Real.sin ((Real.pi /. 4) - x_1))) /. ((Real.cos (2 * x_1)) * (Real.cos ((Real.pi /. 4) - x_1))))))))
  (h5 : x = ((Real.pi /. 4) + y))
  (h6 : y ∈ (Set.univ : Set ℝ))
  (h7 : y ≠ 0)
  (h8 : (Real.sin (2 * y)) ≠ 0)
  (h9 : (Real.cos y) ≠ 0)
  (h10 : Tendsto (fun x_1 : ℝ => (((Real.sin (2 * x_1)) * (Real.sin ((Real.pi /. 4) - x_1))) /. ((Real.cos (2 * x_1)) * (Real.cos ((Real.pi /. 4) - x_1))))) (𝓝[≠] (Real.pi /. 4)) (𝓝 ((𝓝[≠] 0).limUnder (fun y_1 : ℝ => (((Real.cos (2 * y_1)) * (Real.sin y_1)) /. ((Real.sin (2 * y_1)) * (Real.cos y_1)))))))
  (h11 : ∃ L : ℝ, Tendsto (fun x_1 : ℝ => (((Real.sin (2 * x_1)) * (Real.sin ((Real.pi /. 4) - x_1))) /. ((Real.cos (2 * x_1)) * (Real.cos ((Real.pi /. 4) - x_1))))) (𝓝[≠] (Real.pi /. 4)) (𝓝 L))
  (h12 : ∃ L : ℝ, Tendsto (fun y_1 : ℝ => (((Real.cos (2 * y_1)) * (Real.sin y_1)) /. ((Real.sin (2 * y_1)) * (Real.cos y_1)))) (𝓝[≠] 0) (𝓝 L))
  : (∃ L : ℝ, Tendsto (fun y_1 : ℝ => ((Real.cos (2 * y_1)) /. (2 * ((Real.cos y_1) ^ (2 : ℕ))))) (𝓝[≠] 0) (𝓝 L) ∧ (Tendsto (fun y_1 : ℝ => (((Real.cos (2 * y_1)) * (Real.sin y_1)) /. ((Real.sin (2 * y_1)) * (Real.cos y_1)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun y_1 : ℝ => ((Real.cos (2 * y_1)) /. (2 * ((Real.cos y_1) ^ (2 : ℕ))))))))) := by
  sorry

theorem proof_gap_exercise_479_8
  (x : ℝ)
  (y : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (Real.cos (2 * x)) ≠ 0)
  (h3 : (Real.cos ((Real.pi /. 4) - x)) ≠ 0)
  (h4 : Tendsto (fun x_1 : ℝ => ((Real.tan (2 * x_1)) * (Real.tan ((Real.pi /. 4) - x_1)))) (𝓝[≠] (Real.pi /. 4)) (𝓝 ((𝓝[≠] (Real.pi /. 4)).limUnder (fun x_1 : ℝ => (((Real.sin (2 * x_1)) * (Real.sin ((Real.pi /. 4) - x_1))) /. ((Real.cos (2 * x_1)) * (Real.cos ((Real.pi /. 4) - x_1))))))))
  (h5 : x = ((Real.pi /. 4) + y))
  (h6 : y ∈ (Set.univ : Set ℝ))
  (h7 : y ≠ 0)
  (h8 : (Real.sin (2 * y)) ≠ 0)
  (h9 : (Real.cos y) ≠ 0)
  (h10 : Tendsto (fun x_1 : ℝ => (((Real.sin (2 * x_1)) * (Real.sin ((Real.pi /. 4) - x_1))) /. ((Real.cos (2 * x_1)) * (Real.cos ((Real.pi /. 4) - x_1))))) (𝓝[≠] (Real.pi /. 4)) (𝓝 ((𝓝[≠] 0).limUnder (fun y_1 : ℝ => (((Real.cos (2 * y_1)) * (Real.sin y_1)) /. ((Real.sin (2 * y_1)) * (Real.cos y_1)))))))
  (h11 : Tendsto (fun y_1 : ℝ => (((Real.cos (2 * y_1)) * (Real.sin y_1)) /. ((Real.sin (2 * y_1)) * (Real.cos y_1)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun y_1 : ℝ => ((Real.cos (2 * y_1)) /. (2 * ((Real.cos y_1) ^ (2 : ℕ))))))))
  (h12 : ∃ L : ℝ, Tendsto (fun x_1 : ℝ => (((Real.sin (2 * x_1)) * (Real.sin ((Real.pi /. 4) - x_1))) /. ((Real.cos (2 * x_1)) * (Real.cos ((Real.pi /. 4) - x_1))))) (𝓝[≠] (Real.pi /. 4)) (𝓝 L))
  (h13 : ∃ L : ℝ, Tendsto (fun y_1 : ℝ => (((Real.cos (2 * y_1)) * (Real.sin y_1)) /. ((Real.sin (2 * y_1)) * (Real.cos y_1)))) (𝓝[≠] 0) (𝓝 L))
  (h14 : ∃ L : ℝ, Tendsto (fun y_1 : ℝ => ((Real.cos (2 * y_1)) /. (2 * ((Real.cos y_1) ^ (2 : ℕ))))) (𝓝[≠] 0) (𝓝 L))
  : Tendsto (fun y_1 : ℝ => ((Real.cos (2 * y_1)) /. (2 * ((Real.cos y_1) ^ (2 : ℕ))))) (𝓝[≠] 0) (𝓝 (1 /. 2)) := by
  sorry

theorem proof_gap_exercise_479_9
  (x : ℝ)
  (y : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (Real.cos (2 * x)) ≠ 0)
  (h3 : (Real.cos ((Real.pi /. 4) - x)) ≠ 0)
  (h4 : Tendsto (fun x_1 : ℝ => ((Real.tan (2 * x_1)) * (Real.tan ((Real.pi /. 4) - x_1)))) (𝓝[≠] (Real.pi /. 4)) (𝓝 ((𝓝[≠] (Real.pi /. 4)).limUnder (fun x_1 : ℝ => (((Real.sin (2 * x_1)) * (Real.sin ((Real.pi /. 4) - x_1))) /. ((Real.cos (2 * x_1)) * (Real.cos ((Real.pi /. 4) - x_1))))))))
  (h5 : x = ((Real.pi /. 4) + y))
  (h6 : y ∈ (Set.univ : Set ℝ))
  (h7 : y ≠ 0)
  (h8 : (Real.sin (2 * y)) ≠ 0)
  (h9 : (Real.cos y) ≠ 0)
  (h10 : Tendsto (fun x_1 : ℝ => (((Real.sin (2 * x_1)) * (Real.sin ((Real.pi /. 4) - x_1))) /. ((Real.cos (2 * x_1)) * (Real.cos ((Real.pi /. 4) - x_1))))) (𝓝[≠] (Real.pi /. 4)) (𝓝 ((𝓝[≠] 0).limUnder (fun y_1 : ℝ => (((Real.cos (2 * y_1)) * (Real.sin y_1)) /. ((Real.sin (2 * y_1)) * (Real.cos y_1)))))))
  (h11 : Tendsto (fun y_1 : ℝ => (((Real.cos (2 * y_1)) * (Real.sin y_1)) /. ((Real.sin (2 * y_1)) * (Real.cos y_1)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun y_1 : ℝ => ((Real.cos (2 * y_1)) /. (2 * ((Real.cos y_1) ^ (2 : ℕ))))))))
  (h12 : Tendsto (fun y_1 : ℝ => ((Real.cos (2 * y_1)) /. (2 * ((Real.cos y_1) ^ (2 : ℕ))))) (𝓝[≠] 0) (𝓝 (1 /. 2)))
  (h13 : ∃ L : ℝ, Tendsto (fun x_1 : ℝ => (((Real.sin (2 * x_1)) * (Real.sin ((Real.pi /. 4) - x_1))) /. ((Real.cos (2 * x_1)) * (Real.cos ((Real.pi /. 4) - x_1))))) (𝓝[≠] (Real.pi /. 4)) (𝓝 L))
  (h14 : ∃ L : ℝ, Tendsto (fun y_1 : ℝ => (((Real.cos (2 * y_1)) * (Real.sin y_1)) /. ((Real.sin (2 * y_1)) * (Real.cos y_1)))) (𝓝[≠] 0) (𝓝 L))
  (h15 : ∃ L : ℝ, Tendsto (fun y_1 : ℝ => ((Real.cos (2 * y_1)) /. (2 * ((Real.cos y_1) ^ (2 : ℕ))))) (𝓝[≠] 0) (𝓝 L))
  : Tendsto (fun x_1 : ℝ => ((Real.tan (2 * x_1)) * (Real.tan ((Real.pi /. 4) - x_1)))) (𝓝[≠] (Real.pi /. 4)) (𝓝 (1 /. 2)) := by
  sorry

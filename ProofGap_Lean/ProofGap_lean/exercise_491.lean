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

-- exercise: exercise_491

theorem proof_gap_exercise_491_1
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : (forall (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) → (a ≠ (k * Real.pi)))))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => ((((-(Real.sin x)) * (Real.sin (a + x))) * ((Real.sin a) - (Real.sin (a + (2 * x))))) /. ((((x ^ (2 : ℕ)) * (Real.sin a)) * ((Real.sin (a + x)) ^ (2 : ℕ))) * (Real.sin (a + (2 * x)))))) (𝓝[≠] 0) (𝓝 L) ∧ (Tendsto (fun x : ℝ => (((((1 : ℝ) /. (Real.tan (a + (2 * x)))) - (2 * ((1 : ℝ) /. (Real.tan (a + x))))) + ((1 : ℝ) /. (Real.tan a))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((-(Real.sin x)) * (Real.sin (a + x))) * ((Real.sin a) - (Real.sin (a + (2 * x))))) /. ((((x ^ (2 : ℕ)) * (Real.sin a)) * ((Real.sin (a + x)) ^ (2 : ℕ))) * (Real.sin (a + (2 * x)))))))))) := by
  sorry

theorem proof_gap_exercise_491_2
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : (forall (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) → (a ≠ (k * Real.pi)))))
  (h3 : Tendsto (fun x : ℝ => (((((1 : ℝ) /. (Real.tan (a + (2 * x)))) - (2 * ((1 : ℝ) /. (Real.tan (a + x))))) + ((1 : ℝ) /. (Real.tan a))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((-(Real.sin x)) * (Real.sin (a + x))) * ((Real.sin a) - (Real.sin (a + (2 * x))))) /. ((((x ^ (2 : ℕ)) * (Real.sin a)) * ((Real.sin (a + x)) ^ (2 : ℕ))) * (Real.sin (a + (2 * x)))))))))
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((((-(Real.sin x)) * (Real.sin (a + x))) * ((Real.sin a) - (Real.sin (a + (2 * x))))) /. ((((x ^ (2 : ℕ)) * (Real.sin a)) * ((Real.sin (a + x)) ^ (2 : ℕ))) * (Real.sin (a + (2 * x)))))) (𝓝[≠] 0) (𝓝 L))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => ((((Real.sin x) /. x) ^ (2 : ℕ)) * ((2 * (Real.cos (a + x))) /. (((Real.sin a) * (Real.sin (a + x))) * (Real.sin (a + (2 * x))))))) (𝓝[≠] 0) (𝓝 L) ∧ (Tendsto (fun x : ℝ => ((((-(Real.sin x)) * (Real.sin (a + x))) * ((Real.sin a) - (Real.sin (a + (2 * x))))) /. ((((x ^ (2 : ℕ)) * (Real.sin a)) * ((Real.sin (a + x)) ^ (2 : ℕ))) * (Real.sin (a + (2 * x)))))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((Real.sin x) /. x) ^ (2 : ℕ)) * ((2 * (Real.cos (a + x))) /. (((Real.sin a) * (Real.sin (a + x))) * (Real.sin (a + (2 * x))))))))))) := by
  sorry

theorem proof_gap_exercise_491_3
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : (forall (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) → (a ≠ (k * Real.pi)))))
  (h3 : Tendsto (fun x : ℝ => (((((1 : ℝ) /. (Real.tan (a + (2 * x)))) - (2 * ((1 : ℝ) /. (Real.tan (a + x))))) + ((1 : ℝ) /. (Real.tan a))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((-(Real.sin x)) * (Real.sin (a + x))) * ((Real.sin a) - (Real.sin (a + (2 * x))))) /. ((((x ^ (2 : ℕ)) * (Real.sin a)) * ((Real.sin (a + x)) ^ (2 : ℕ))) * (Real.sin (a + (2 * x)))))))))
  (h4 : Tendsto (fun x : ℝ => ((((-(Real.sin x)) * (Real.sin (a + x))) * ((Real.sin a) - (Real.sin (a + (2 * x))))) /. ((((x ^ (2 : ℕ)) * (Real.sin a)) * ((Real.sin (a + x)) ^ (2 : ℕ))) * (Real.sin (a + (2 * x)))))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((Real.sin x) /. x) ^ (2 : ℕ)) * ((2 * (Real.cos (a + x))) /. (((Real.sin a) * (Real.sin (a + x))) * (Real.sin (a + (2 * x))))))))))
  (h5 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((((-(Real.sin x)) * (Real.sin (a + x))) * ((Real.sin a) - (Real.sin (a + (2 * x))))) /. ((((x ^ (2 : ℕ)) * (Real.sin a)) * ((Real.sin (a + x)) ^ (2 : ℕ))) * (Real.sin (a + (2 * x)))))) (𝓝[≠] 0) (𝓝 L))
  (h6 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((((Real.sin x) /. x) ^ (2 : ℕ)) * ((2 * (Real.cos (a + x))) /. (((Real.sin a) * (Real.sin (a + x))) * (Real.sin (a + (2 * x))))))) (𝓝[≠] 0) (𝓝 L))
  : Tendsto (fun x : ℝ => ((((Real.sin x) /. x) ^ (2 : ℕ)) * ((2 * (Real.cos (a + x))) /. (((Real.sin a) * (Real.sin (a + x))) * (Real.sin (a + (2 * x))))))) (𝓝[≠] 0) (𝓝 ((2 * (Real.cos a)) /. ((Real.sin a) ^ (3 : ℕ)))) := by
  sorry

theorem proof_gap_exercise_491_4
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : (forall (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) → (a ≠ (k * Real.pi)))))
  (h3 : Tendsto (fun x : ℝ => (((((1 : ℝ) /. (Real.tan (a + (2 * x)))) - (2 * ((1 : ℝ) /. (Real.tan (a + x))))) + ((1 : ℝ) /. (Real.tan a))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((-(Real.sin x)) * (Real.sin (a + x))) * ((Real.sin a) - (Real.sin (a + (2 * x))))) /. ((((x ^ (2 : ℕ)) * (Real.sin a)) * ((Real.sin (a + x)) ^ (2 : ℕ))) * (Real.sin (a + (2 * x)))))))))
  (h4 : Tendsto (fun x : ℝ => ((((-(Real.sin x)) * (Real.sin (a + x))) * ((Real.sin a) - (Real.sin (a + (2 * x))))) /. ((((x ^ (2 : ℕ)) * (Real.sin a)) * ((Real.sin (a + x)) ^ (2 : ℕ))) * (Real.sin (a + (2 * x)))))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((Real.sin x) /. x) ^ (2 : ℕ)) * ((2 * (Real.cos (a + x))) /. (((Real.sin a) * (Real.sin (a + x))) * (Real.sin (a + (2 * x))))))))))
  (h5 : Tendsto (fun x : ℝ => ((((Real.sin x) /. x) ^ (2 : ℕ)) * ((2 * (Real.cos (a + x))) /. (((Real.sin a) * (Real.sin (a + x))) * (Real.sin (a + (2 * x))))))) (𝓝[≠] 0) (𝓝 ((2 * (Real.cos a)) /. ((Real.sin a) ^ (3 : ℕ)))))
  (h6 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((((-(Real.sin x)) * (Real.sin (a + x))) * ((Real.sin a) - (Real.sin (a + (2 * x))))) /. ((((x ^ (2 : ℕ)) * (Real.sin a)) * ((Real.sin (a + x)) ^ (2 : ℕ))) * (Real.sin (a + (2 * x)))))) (𝓝[≠] 0) (𝓝 L))
  (h7 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((((Real.sin x) /. x) ^ (2 : ℕ)) * ((2 * (Real.cos (a + x))) /. (((Real.sin a) * (Real.sin (a + x))) * (Real.sin (a + (2 * x))))))) (𝓝[≠] 0) (𝓝 L))
  : Tendsto (fun x : ℝ => (((((1 : ℝ) /. (Real.tan (a + (2 * x)))) - (2 * ((1 : ℝ) /. (Real.tan (a + x))))) + ((1 : ℝ) /. (Real.tan a))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 ((2 * (Real.cos a)) /. ((Real.sin a) ^ (3 : ℕ)))) := by
  sorry

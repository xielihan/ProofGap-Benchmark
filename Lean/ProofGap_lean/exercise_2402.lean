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

-- exercise: exercise_2402

theorem proof_gap_exercise_2402_1
  (a : ℝ)
  (S : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : S ∈ (Set.univ : Set ℝ))
  : S = (∫ x, (((a ^ (3 : ℕ)) /. ((a ^ (2 : ℕ)) + (x ^ (2 : ℕ)))) * (1 : ℝ))) := by
  sorry

theorem proof_gap_exercise_2402_2
  (a : ℝ)
  (S : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : S ∈ (Set.univ : Set ℝ))
  (h3 : S = (∫ x, (((a ^ (3 : ℕ)) /. ((a ^ (2 : ℕ)) + (x ^ (2 : ℕ)))) * (1 : ℝ))))
  : (∃ L : ℝ, Tendsto (fun b : ℝ => (∫ x in (0 : ℝ)..b, (((1 : ℝ) /. ((a ^ (2 : ℕ)) + (x ^ (2 : ℕ)))) * (1 : ℝ)))) atTop (𝓝 L) ∧ (S = ((2 * (a ^ (3 : ℕ))) * atTop.limUnder (fun b : ℝ => (∫ x in (0 : ℝ)..b, (((1 : ℝ) /. ((a ^ (2 : ℕ)) + (x ^ (2 : ℕ)))) * (1 : ℝ))))))) := by
  sorry

theorem proof_gap_exercise_2402_3
  (a : ℝ)
  (S : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : S ∈ (Set.univ : Set ℝ))
  (h3 : S = (∫ x, (((a ^ (3 : ℕ)) /. ((a ^ (2 : ℕ)) + (x ^ (2 : ℕ)))) * (1 : ℝ))))
  (h4 : S = ((2 * (a ^ (3 : ℕ))) * atTop.limUnder (fun b : ℝ => (∫ x in (0 : ℝ)..b, (((1 : ℝ) /. ((a ^ (2 : ℕ)) + (x ^ (2 : ℕ)))) * (1 : ℝ))))))
  (h5 : ∃ L : ℝ, Tendsto (fun b : ℝ => (∫ x in (0 : ℝ)..b, (((1 : ℝ) /. ((a ^ (2 : ℕ)) + (x ^ (2 : ℕ)))) * (1 : ℝ)))) atTop (𝓝 L))
  : (forall (b : ℝ), ((b ∈ (Set.univ : Set ℝ)) → ((∫ x in (0 : ℝ)..b, (((1 : ℝ) /. ((a ^ (2 : ℕ)) + (x ^ (2 : ℕ)))) * (1 : ℝ))) = ((1 /. a) * (Real.arctan (b /. a)))))) := by
  sorry

theorem proof_gap_exercise_2402_4
  (a : ℝ)
  (S : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : S ∈ (Set.univ : Set ℝ))
  (h3 : S = (∫ x, (((a ^ (3 : ℕ)) /. ((a ^ (2 : ℕ)) + (x ^ (2 : ℕ)))) * (1 : ℝ))))
  (h4 : S = ((2 * (a ^ (3 : ℕ))) * atTop.limUnder (fun b : ℝ => (∫ x in (0 : ℝ)..b, (((1 : ℝ) /. ((a ^ (2 : ℕ)) + (x ^ (2 : ℕ)))) * (1 : ℝ))))))
  (h5 : (forall (b : ℝ), ((b ∈ (Set.univ : Set ℝ)) → ((∫ x in (0 : ℝ)..b, (((1 : ℝ) /. ((a ^ (2 : ℕ)) + (x ^ (2 : ℕ)))) * (1 : ℝ))) = ((1 /. a) * (Real.arctan (b /. a)))))))
  (h6 : ∃ L : ℝ, Tendsto (fun b : ℝ => (∫ x in (0 : ℝ)..b, (((1 : ℝ) /. ((a ^ (2 : ℕ)) + (x ^ (2 : ℕ)))) * (1 : ℝ)))) atTop (𝓝 L))
  : (∃ L : ℝ, Tendsto (fun b : ℝ => ((1 /. a) * (Real.arctan (b /. a)))) atTop (𝓝 L) ∧ (S = ((2 * (a ^ (3 : ℕ))) * atTop.limUnder (fun b : ℝ => ((1 /. a) * (Real.arctan (b /. a))))))) := by
  sorry

theorem proof_gap_exercise_2402_5
  (a : ℝ)
  (S : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : S ∈ (Set.univ : Set ℝ))
  (h3 : S = (∫ x, (((a ^ (3 : ℕ)) /. ((a ^ (2 : ℕ)) + (x ^ (2 : ℕ)))) * (1 : ℝ))))
  (h4 : S = ((2 * (a ^ (3 : ℕ))) * atTop.limUnder (fun b : ℝ => (∫ x in (0 : ℝ)..b, (((1 : ℝ) /. ((a ^ (2 : ℕ)) + (x ^ (2 : ℕ)))) * (1 : ℝ))))))
  (h5 : (forall (b : ℝ), ((b ∈ (Set.univ : Set ℝ)) → ((∫ x in (0 : ℝ)..b, (((1 : ℝ) /. ((a ^ (2 : ℕ)) + (x ^ (2 : ℕ)))) * (1 : ℝ))) = ((1 /. a) * (Real.arctan (b /. a)))))))
  (h6 : S = ((2 * (a ^ (3 : ℕ))) * atTop.limUnder (fun b : ℝ => ((1 /. a) * (Real.arctan (b /. a))))))
  (h7 : ∃ L : ℝ, Tendsto (fun b : ℝ => (∫ x in (0 : ℝ)..b, (((1 : ℝ) /. ((a ^ (2 : ℕ)) + (x ^ (2 : ℕ)))) * (1 : ℝ)))) atTop (𝓝 L))
  (h8 : ∃ L : ℝ, Tendsto (fun b : ℝ => ((1 /. a) * (Real.arctan (b /. a)))) atTop (𝓝 L))
  : Tendsto (fun b : ℝ => (Real.arctan (b /. a))) atTop (𝓝 (Real.pi /. 2)) := by
  sorry

theorem proof_gap_exercise_2402_6
  (a : ℝ)
  (S : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : S ∈ (Set.univ : Set ℝ))
  (h3 : S = (∫ x, (((a ^ (3 : ℕ)) /. ((a ^ (2 : ℕ)) + (x ^ (2 : ℕ)))) * (1 : ℝ))))
  (h4 : S = ((2 * (a ^ (3 : ℕ))) * atTop.limUnder (fun b : ℝ => (∫ x in (0 : ℝ)..b, (((1 : ℝ) /. ((a ^ (2 : ℕ)) + (x ^ (2 : ℕ)))) * (1 : ℝ))))))
  (h5 : (forall (b : ℝ), ((b ∈ (Set.univ : Set ℝ)) → ((∫ x in (0 : ℝ)..b, (((1 : ℝ) /. ((a ^ (2 : ℕ)) + (x ^ (2 : ℕ)))) * (1 : ℝ))) = ((1 /. a) * (Real.arctan (b /. a)))))))
  (h6 : S = ((2 * (a ^ (3 : ℕ))) * atTop.limUnder (fun b : ℝ => ((1 /. a) * (Real.arctan (b /. a))))))
  (h7 : Tendsto (fun b : ℝ => (Real.arctan (b /. a))) atTop (𝓝 (Real.pi /. 2)))
  (h8 : ∃ L : ℝ, Tendsto (fun b : ℝ => (∫ x in (0 : ℝ)..b, (((1 : ℝ) /. ((a ^ (2 : ℕ)) + (x ^ (2 : ℕ)))) * (1 : ℝ)))) atTop (𝓝 L))
  (h9 : ∃ L : ℝ, Tendsto (fun b : ℝ => ((1 /. a) * (Real.arctan (b /. a)))) atTop (𝓝 L))
  : S = (Real.pi * (a ^ (2 : ℕ))) := by
  sorry

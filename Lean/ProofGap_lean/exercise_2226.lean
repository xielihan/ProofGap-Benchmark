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

-- exercise: exercise_2226

theorem proof_gap_exercise_2226_1
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : a ≠ b)
  (h4 : ContinuousOn f (Set.Icc (min a b) (max a b)))
  : Tendsto (fun n : ℕ => ((1 /. n) * (∑ k ∈ Finset.Icc (1 : ℕ) n, (f (a + (k * ((b - a) /. n))))))) atTop (𝓝 (∫ x in (0 : ℝ)..(1 : ℝ), ((f (a + ((b - a) * x))) * (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_2226_2
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : a ≠ b)
  (h4 : ContinuousOn f (Set.Icc (min a b) (max a b)))
  (h5 : Tendsto (fun n : ℕ => ((1 /. n) * (∑ k ∈ Finset.Icc (1 : ℕ) n, (f (a + (k * ((b - a) /. n))))))) atTop (𝓝 (∫ x in (0 : ℝ)..(1 : ℝ), ((f (a + ((b - a) * x))) * (1 : ℝ)))))
  : (∫ x in (0 : ℝ)..(1 : ℝ), ((f (a + ((b - a) * x))) * (1 : ℝ))) = ((1 /. (b - a)) * (∫ x in a..b, ((f x) * (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_2226_3
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : a ≠ b)
  (h4 : ContinuousOn f (Set.Icc (min a b) (max a b)))
  (h5 : Tendsto (fun n : ℕ => ((1 /. n) * (∑ k ∈ Finset.Icc (1 : ℕ) n, (f (a + (k * ((b - a) /. n))))))) atTop (𝓝 (∫ x in (0 : ℝ)..(1 : ℝ), ((f (a + ((b - a) * x))) * (1 : ℝ)))))
  (h6 : (∫ x in (0 : ℝ)..(1 : ℝ), ((f (a + ((b - a) * x))) * (1 : ℝ))) = ((1 /. (b - a)) * (∫ x in a..b, ((f x) * (1 : ℝ)))))
  : Tendsto (fun n : ℕ => ((1 /. n) * (∑ k ∈ Finset.Icc (1 : ℕ) n, (f (a + (k * ((b - a) /. n))))))) atTop (𝓝 ((1 /. (b - a)) * (∫ x in a..b, ((f x) * (1 : ℝ))))) := by
  sorry

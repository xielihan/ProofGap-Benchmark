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

-- exercise: exercise_2277

theorem proof_gap_exercise_2277_1
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((Real.sin x) * (Real.sin (2 * x))) * (Real.sin (3 * x))) = (((1 /. 2) * ((Real.cos (2 * x)) - (Real.cos (4 * x)))) * (Real.sin (2 * x)))))) := by
  sorry

theorem proof_gap_exercise_2277_2
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((Real.sin x) * (Real.sin (2 * x))) * (Real.sin (3 * x))) = (((1 /. 2) * ((Real.cos (2 * x)) - (Real.cos (4 * x)))) * (Real.sin (2 * x)))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((1 /. 2) * ((Real.cos (2 * x)) - (Real.cos (4 * x)))) * (Real.sin (2 * x))) = (((1 /. 4) * (Real.sin (4 * x))) - ((1 /. 4) * ((Real.sin (6 * x)) - (Real.sin (2 * x)))))))) := by
  sorry

theorem proof_gap_exercise_2277_3
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((Real.sin x) * (Real.sin (2 * x))) * (Real.sin (3 * x))) = (((1 /. 2) * ((Real.cos (2 * x)) - (Real.cos (4 * x)))) * (Real.sin (2 * x)))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((1 /. 2) * ((Real.cos (2 * x)) - (Real.cos (4 * x)))) * (Real.sin (2 * x))) = (((1 /. 4) * (Real.sin (4 * x))) - ((1 /. 4) * ((Real.sin (6 * x)) - (Real.sin (2 * x)))))))))
  : (∫ x in (0 : ℝ)..(Real.pi /. 2), ((((Real.sin x) * (Real.sin (2 * x))) * (Real.sin (3 * x))) * (1 : ℝ))) = (((((-(1 /. 16)) * (Real.cos (4 * (Real.pi /. 2)))) + ((1 /. 24) * (Real.cos (6 * (Real.pi /. 2))))) - ((1 /. 8) * (Real.cos (2 * (Real.pi /. 2))))) - ((((-(1 /. 16)) * (Real.cos (4 * 0))) + ((1 /. 24) * (Real.cos (6 * 0)))) - ((1 /. 8) * (Real.cos (2 * 0))))) := by
  sorry

theorem proof_gap_exercise_2277_4
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((Real.sin x) * (Real.sin (2 * x))) * (Real.sin (3 * x))) = (((1 /. 2) * ((Real.cos (2 * x)) - (Real.cos (4 * x)))) * (Real.sin (2 * x)))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((1 /. 2) * ((Real.cos (2 * x)) - (Real.cos (4 * x)))) * (Real.sin (2 * x))) = (((1 /. 4) * (Real.sin (4 * x))) - ((1 /. 4) * ((Real.sin (6 * x)) - (Real.sin (2 * x)))))))))
  (h3 : (∫ x in (0 : ℝ)..(Real.pi /. 2), ((((Real.sin x) * (Real.sin (2 * x))) * (Real.sin (3 * x))) * (1 : ℝ))) = (((((-(1 /. 16)) * (Real.cos (4 * (Real.pi /. 2)))) + ((1 /. 24) * (Real.cos (6 * (Real.pi /. 2))))) - ((1 /. 8) * (Real.cos (2 * (Real.pi /. 2))))) - ((((-(1 /. 16)) * (Real.cos (4 * 0))) + ((1 /. 24) * (Real.cos (6 * 0)))) - ((1 /. 8) * (Real.cos (2 * 0))))))
  : (((((-(1 /. 16)) * (Real.cos (4 * (Real.pi /. 2)))) + ((1 /. 24) * (Real.cos (6 * (Real.pi /. 2))))) - ((1 /. 8) * (Real.cos (2 * (Real.pi /. 2))))) - ((((-(1 /. 16)) * (Real.cos (4 * 0))) + ((1 /. 24) * (Real.cos (6 * 0)))) - ((1 /. 8) * (Real.cos (2 * 0))))) = (1 /. 6) := by
  sorry

theorem proof_gap_exercise_2277_5
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((Real.sin x) * (Real.sin (2 * x))) * (Real.sin (3 * x))) = (((1 /. 2) * ((Real.cos (2 * x)) - (Real.cos (4 * x)))) * (Real.sin (2 * x)))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((1 /. 2) * ((Real.cos (2 * x)) - (Real.cos (4 * x)))) * (Real.sin (2 * x))) = (((1 /. 4) * (Real.sin (4 * x))) - ((1 /. 4) * ((Real.sin (6 * x)) - (Real.sin (2 * x)))))))))
  (h3 : (∫ x in (0 : ℝ)..(Real.pi /. 2), ((((Real.sin x) * (Real.sin (2 * x))) * (Real.sin (3 * x))) * (1 : ℝ))) = (((((-(1 /. 16)) * (Real.cos (4 * (Real.pi /. 2)))) + ((1 /. 24) * (Real.cos (6 * (Real.pi /. 2))))) - ((1 /. 8) * (Real.cos (2 * (Real.pi /. 2))))) - ((((-(1 /. 16)) * (Real.cos (4 * 0))) + ((1 /. 24) * (Real.cos (6 * 0)))) - ((1 /. 8) * (Real.cos (2 * 0))))))
  (h4 : (((((-(1 /. 16)) * (Real.cos (4 * (Real.pi /. 2)))) + ((1 /. 24) * (Real.cos (6 * (Real.pi /. 2))))) - ((1 /. 8) * (Real.cos (2 * (Real.pi /. 2))))) - ((((-(1 /. 16)) * (Real.cos (4 * 0))) + ((1 /. 24) * (Real.cos (6 * 0)))) - ((1 /. 8) * (Real.cos (2 * 0))))) = (1 /. 6))
  : (∫ x in (0 : ℝ)..(Real.pi /. 2), ((((Real.sin x) * (Real.sin (2 * x))) * (Real.sin (3 * x))) * (1 : ℝ))) = (1 /. 6) := by
  sorry

theorem proof_gap_exercise_2277_6
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((Real.sin x) * (Real.sin (2 * x))) * (Real.sin (3 * x))) = (((1 /. 2) * ((Real.cos (2 * x)) - (Real.cos (4 * x)))) * (Real.sin (2 * x)))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((1 /. 2) * ((Real.cos (2 * x)) - (Real.cos (4 * x)))) * (Real.sin (2 * x))) = (((1 /. 4) * (Real.sin (4 * x))) - ((1 /. 4) * ((Real.sin (6 * x)) - (Real.sin (2 * x)))))))))
  (h3 : (∫ x in (0 : ℝ)..(Real.pi /. 2), ((((Real.sin x) * (Real.sin (2 * x))) * (Real.sin (3 * x))) * (1 : ℝ))) = (((((-(1 /. 16)) * (Real.cos (4 * (Real.pi /. 2)))) + ((1 /. 24) * (Real.cos (6 * (Real.pi /. 2))))) - ((1 /. 8) * (Real.cos (2 * (Real.pi /. 2))))) - ((((-(1 /. 16)) * (Real.cos (4 * 0))) + ((1 /. 24) * (Real.cos (6 * 0)))) - ((1 /. 8) * (Real.cos (2 * 0))))))
  (h4 : (((((-(1 /. 16)) * (Real.cos (4 * (Real.pi /. 2)))) + ((1 /. 24) * (Real.cos (6 * (Real.pi /. 2))))) - ((1 /. 8) * (Real.cos (2 * (Real.pi /. 2))))) - ((((-(1 /. 16)) * (Real.cos (4 * 0))) + ((1 /. 24) * (Real.cos (6 * 0)))) - ((1 /. 8) * (Real.cos (2 * 0))))) = (1 /. 6))
  (h5 : (∫ x in (0 : ℝ)..(Real.pi /. 2), ((((Real.sin x) * (Real.sin (2 * x))) * (Real.sin (3 * x))) * (1 : ℝ))) = (1 /. 6))
  : (∫ x in (0 : ℝ)..(Real.pi /. 2), ((((Real.sin x) * (Real.sin (2 * x))) * (Real.sin (3 * x))) * (1 : ℝ))) = (1 /. 6) := by
  sorry

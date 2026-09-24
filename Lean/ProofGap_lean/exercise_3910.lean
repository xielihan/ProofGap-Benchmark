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

-- exercise: exercise_3910

theorem proof_gap_exercise_3910_1
  (f : (ℝ × ℝ -> ℝ))
  (F : (ℝ × ℝ -> ℝ))
  (a : ℝ)
  (A : ℝ)
  (b : ℝ)
  (B : ℝ)
  (I : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : A ∈ (Set.univ : Set ℝ))
  (h3 : b ∈ (Set.univ : Set ℝ))
  (h4 : B ∈ (Set.univ : Set ℝ))
  (h5 : I ∈ (Set.univ : Set ℝ))
  (h6 : a ≤ A)
  (h7 : b ≤ B)
  (h8 : ContDiffOn ℝ (2 : ℕ∞) F ((Set.Icc a A) ×ˢ (Set.Icc b B)))
  (h9 : (forall (x : ℝ) (y : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Icc a A))) ∧ (y ∈ (Set.Icc b B))) → ((f (x, y)) = (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => F (t, p.2)) p.1)) (x, t)) y)))))
  (h10 : I = (∫ x in a..A, ((∫ y in b..B, ((f (x, y)) * (1 : ℝ))) * (1 : ℝ))))
  : I = (∫ x in a..A, (((iteratedDeriv 1 (fun t => F (t, B)) x) - (iteratedDeriv 1 (fun t => F (t, b)) x)) * (1 : ℝ))) := by
  sorry

theorem proof_gap_exercise_3910_2
  (f : (ℝ × ℝ -> ℝ))
  (F : (ℝ × ℝ -> ℝ))
  (a : ℝ)
  (A : ℝ)
  (b : ℝ)
  (B : ℝ)
  (I : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : A ∈ (Set.univ : Set ℝ))
  (h3 : b ∈ (Set.univ : Set ℝ))
  (h4 : B ∈ (Set.univ : Set ℝ))
  (h5 : I ∈ (Set.univ : Set ℝ))
  (h6 : a ≤ A)
  (h7 : b ≤ B)
  (h8 : ContDiffOn ℝ (2 : ℕ∞) F ((Set.Icc a A) ×ˢ (Set.Icc b B)))
  (h9 : (forall (x : ℝ) (y : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Icc a A))) ∧ (y ∈ (Set.Icc b B))) → ((f (x, y)) = (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => F (t, p.2)) p.1)) (x, t)) y)))))
  (h10 : I = (∫ x in a..A, ((∫ y in b..B, ((f (x, y)) * (1 : ℝ))) * (1 : ℝ))))
  (h11 : I = (∫ x in a..A, (((iteratedDeriv 1 (fun t => F (t, B)) x) - (iteratedDeriv 1 (fun t => F (t, b)) x)) * (1 : ℝ))))
  : I = (((F (A, B)) - (F (a, B))) - ((F (A, b)) - (F (a, b)))) := by
  sorry

theorem proof_gap_exercise_3910_3
  (f : (ℝ × ℝ -> ℝ))
  (F : (ℝ × ℝ -> ℝ))
  (a : ℝ)
  (A : ℝ)
  (b : ℝ)
  (B : ℝ)
  (I : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : A ∈ (Set.univ : Set ℝ))
  (h3 : b ∈ (Set.univ : Set ℝ))
  (h4 : B ∈ (Set.univ : Set ℝ))
  (h5 : I ∈ (Set.univ : Set ℝ))
  (h6 : a ≤ A)
  (h7 : b ≤ B)
  (h8 : ContDiffOn ℝ (2 : ℕ∞) F ((Set.Icc a A) ×ˢ (Set.Icc b B)))
  (h9 : (forall (x : ℝ) (y : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Icc a A))) ∧ (y ∈ (Set.Icc b B))) → ((f (x, y)) = (iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => F (t, p.2)) p.1)) (x, t)) y)))))
  (h10 : I = (∫ x in a..A, ((∫ y in b..B, ((f (x, y)) * (1 : ℝ))) * (1 : ℝ))))
  (h11 : I = (∫ x in a..A, (((iteratedDeriv 1 (fun t => F (t, B)) x) - (iteratedDeriv 1 (fun t => F (t, b)) x)) * (1 : ℝ))))
  (h12 : I = (((F (A, B)) - (F (a, B))) - ((F (A, b)) - (F (a, b)))))
  : I = ((((F (A, B)) - (F (a, B))) - (F (A, b))) + (F (a, b))) := by
  sorry

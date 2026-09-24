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

-- exercise: exercise_2254

theorem proof_gap_exercise_2254_1
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : a < b)
  (h4 : ContinuousOn f (Set.Icc a b))
  (h5 : x = (fun (t : ℝ) => (a + ((b - a) * t))))
  : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = 0)) → ((x t) = a))) := by
  sorry

theorem proof_gap_exercise_2254_2
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : a < b)
  (h4 : ContinuousOn f (Set.Icc a b))
  (h5 : x = (fun (t : ℝ) => (a + ((b - a) * t))))
  (h6 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = 0)) → ((x t) = a))))
  : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = 1)) → ((x t) = b))) := by
  sorry

theorem proof_gap_exercise_2254_3
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : a < b)
  (h4 : ContinuousOn f (Set.Icc a b))
  (h5 : x = (fun (t : ℝ) => (a + ((b - a) * t))))
  (h6 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = 0)) → ((x t) = a))))
  (h7 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = 1)) → ((x t) = b))))
  : (fderiv ℝ x) = ((fun (t : ℝ) => (b - a)) • (fderiv ℝ (fun (t : ℝ) => t))) := by
  sorry

theorem proof_gap_exercise_2254_4
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : a < b)
  (h4 : ContinuousOn f (Set.Icc a b))
  (h5 : x = (fun (t : ℝ) => (a + ((b - a) * t))))
  (h6 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = 0)) → ((x t) = a))))
  (h7 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = 1)) → ((x t) = b))))
  (h8 : (fderiv ℝ x) = ((fun (t : ℝ) => (b - a)) • (fderiv ℝ (fun (t : ℝ) => t))))
  : (∫ x in a..b, ((f x) * (1 : ℝ))) = ((b - a) * (∫ t in (0 : ℝ)..(1 : ℝ), ((f (a + ((b - a) * t))) * (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_2254_5
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : a < b)
  (h4 : ContinuousOn f (Set.Icc a b))
  (h5 : x = (fun (t : ℝ) => (a + ((b - a) * t))))
  (h6 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = 0)) → ((x t) = a))))
  (h7 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = 1)) → ((x t) = b))))
  (h8 : (fderiv ℝ x) = ((fun (t : ℝ) => (b - a)) • (fderiv ℝ (fun (t : ℝ) => t))))
  (h9 : (∫ x in a..b, ((f x) * (1 : ℝ))) = ((b - a) * (∫ t in (0 : ℝ)..(1 : ℝ), ((f (a + ((b - a) * t))) * (1 : ℝ)))))
  : ((b - a) * (∫ t in (0 : ℝ)..(1 : ℝ), ((f (a + ((b - a) * t))) * (1 : ℝ)))) = ((b - a) * (∫ x in (0 : ℝ)..(1 : ℝ), ((f (a + ((b - a) * x))) * (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_2254_6
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : a < b)
  (h4 : ContinuousOn f (Set.Icc a b))
  (h5 : x = (fun (t : ℝ) => (a + ((b - a) * t))))
  (h6 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = 0)) → ((x t) = a))))
  (h7 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = 1)) → ((x t) = b))))
  (h8 : (fderiv ℝ x) = ((fun (t : ℝ) => (b - a)) • (fderiv ℝ (fun (t : ℝ) => t))))
  (h9 : (∫ x in a..b, ((f x) * (1 : ℝ))) = ((b - a) * (∫ t in (0 : ℝ)..(1 : ℝ), ((f (a + ((b - a) * t))) * (1 : ℝ)))))
  (h10 : ((b - a) * (∫ t in (0 : ℝ)..(1 : ℝ), ((f (a + ((b - a) * t))) * (1 : ℝ)))) = ((b - a) * (∫ x in (0 : ℝ)..(1 : ℝ), ((f (a + ((b - a) * x))) * (1 : ℝ)))))
  : (∫ x in a..b, ((f x) * (1 : ℝ))) = ((b - a) * (∫ x in (0 : ℝ)..(1 : ℝ), ((f (a + ((b - a) * x))) * (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_2254_7
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : a < b)
  (h4 : ContinuousOn f (Set.Icc a b))
  (h5 : x = (fun (t : ℝ) => (a + ((b - a) * t))))
  (h6 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = 0)) → ((x t) = a))))
  (h7 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = 1)) → ((x t) = b))))
  (h8 : (fderiv ℝ x) = ((fun (t : ℝ) => (b - a)) • (fderiv ℝ (fun (t : ℝ) => t))))
  (h9 : (∫ x in a..b, ((f x) * (1 : ℝ))) = ((b - a) * (∫ t in (0 : ℝ)..(1 : ℝ), ((f (a + ((b - a) * t))) * (1 : ℝ)))))
  (h10 : ((b - a) * (∫ t in (0 : ℝ)..(1 : ℝ), ((f (a + ((b - a) * t))) * (1 : ℝ)))) = ((b - a) * (∫ x in (0 : ℝ)..(1 : ℝ), ((f (a + ((b - a) * x))) * (1 : ℝ)))))
  (h11 : (∫ x in a..b, ((f x) * (1 : ℝ))) = ((b - a) * (∫ x in (0 : ℝ)..(1 : ℝ), ((f (a + ((b - a) * x))) * (1 : ℝ)))))
  : (∫ x in a..b, ((f x) * (1 : ℝ))) = ((b - a) * (∫ x in (0 : ℝ)..(1 : ℝ), ((f (a + ((b - a) * x))) * (1 : ℝ)))) := by
  sorry

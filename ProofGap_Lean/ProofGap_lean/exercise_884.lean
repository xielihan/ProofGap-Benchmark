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

-- exercise: exercise_884

theorem proof_gap_exercise_884_1
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (b ∈ (Set.univ : Set ℝ)) ∧ (b > 0))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((y x) = (((Real.rpow (a /. b) x) * (Real.rpow (b /. x) a)) * (Real.rpow (x /. a) b))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((Real.log (y x)) = (((x * (Real.log (a /. b))) + (a * ((Real.log b) - (Real.log x)))) + (b * ((Real.log x) - (Real.log a))))))) := by
  sorry

theorem proof_gap_exercise_884_2
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (b ∈ (Set.univ : Set ℝ)) ∧ (b > 0))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((y x) = (((Real.rpow (a /. b) x) * (Real.rpow (b /. x) a)) * (Real.rpow (x /. a) b))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((Real.log (y x)) = (((x * (Real.log (a /. b))) + (a * ((Real.log b) - (Real.log x)))) + (b * ((Real.log x) - (Real.log a))))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (((iteratedDeriv 1 (fun t => y t) x) /. (y x)) = (((Real.log (a /. b)) - (a /. x)) + (b /. x))))) := by
  sorry

theorem proof_gap_exercise_884_3
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (b ∈ (Set.univ : Set ℝ)) ∧ (b > 0))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((y x) = (((Real.rpow (a /. b) x) * (Real.rpow (b /. x) a)) * (Real.rpow (x /. a) b))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((Real.log (y x)) = (((x * (Real.log (a /. b))) + (a * ((Real.log b) - (Real.log x)))) + (b * ((Real.log x) - (Real.log a))))))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (((iteratedDeriv 1 (fun t => y t) x) /. (y x)) = (((Real.log (a /. b)) - (a /. x)) + (b /. x))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 1 (fun t => y t) x) = ((y x) * (((Real.log (a /. b)) - (a /. x)) + (b /. x)))))) := by
  sorry

theorem proof_gap_exercise_884_4
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (b ∈ (Set.univ : Set ℝ)) ∧ (b > 0))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((y x) = (((Real.rpow (a /. b) x) * (Real.rpow (b /. x) a)) * (Real.rpow (x /. a) b))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((Real.log (y x)) = (((x * (Real.log (a /. b))) + (a * ((Real.log b) - (Real.log x)))) + (b * ((Real.log x) - (Real.log a))))))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (((iteratedDeriv 1 (fun t => y t) x) /. (y x)) = (((Real.log (a /. b)) - (a /. x)) + (b /. x))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 1 (fun t => y t) x) = ((y x) * (((Real.log (a /. b)) - (a /. x)) + (b /. x)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 1 (fun t => y t) x) = ((((Real.rpow (a /. b) x) * (Real.rpow (b /. x) a)) * (Real.rpow (x /. a) b)) * (((Real.log (a /. b)) - (a /. x)) + (b /. x)))))) := by
  sorry

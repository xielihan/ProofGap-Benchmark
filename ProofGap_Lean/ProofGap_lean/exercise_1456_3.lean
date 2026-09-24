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

-- exercise: exercise_1456_3

theorem proof_gap_exercise_1456_3_1
  (a : ℝ)
  (m : ℝ)
  (n : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : m ∈ (Set.univ : Set ℝ))
  (h3 : n ∈ (Set.univ : Set ℝ))
  (h4 : m > 0)
  (h5 : n > 0)
  (h6 : a ≥ 0)
  (h7 : f = (fun (x : ℝ) => ((Real.rpow x m) * (Real.rpow (a - x) n))))
  : ContinuousOn f (Set.Icc 0 a) := by
  sorry

theorem proof_gap_exercise_1456_3_2
  (a : ℝ)
  (m : ℝ)
  (n : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : m ∈ (Set.univ : Set ℝ))
  (h3 : n ∈ (Set.univ : Set ℝ))
  (h4 : m > 0)
  (h5 : n > 0)
  (h6 : a ≥ 0)
  (h7 : f = (fun (x : ℝ) => ((Real.rpow x m) * (Real.rpow (a - x) n))))
  (h8 : ContinuousOn f (Set.Icc 0 a))
  : (lpMaximumPointsOn f (Set.Icc 0 a)) = ({x | x = ((m * a) /. (m + n))}) := by
  sorry

theorem proof_gap_exercise_1456_3_3
  (a : ℝ)
  (m : ℝ)
  (n : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : m ∈ (Set.univ : Set ℝ))
  (h3 : n ∈ (Set.univ : Set ℝ))
  (h4 : m > 0)
  (h5 : n > 0)
  (h6 : a ≥ 0)
  (h7 : f = (fun (x : ℝ) => ((Real.rpow x m) * (Real.rpow (a - x) n))))
  (h8 : ContinuousOn f (Set.Icc 0 a))
  (h9 : (lpMaximumPointsOn f (Set.Icc 0 a)) = ({x | x = ((m * a) /. (m + n))}))
  : (f ((m * a) /. (m + n))) = ((Real.rpow ((m * a) /. (m + n)) m) * (Real.rpow (a - ((m * a) /. (m + n))) n)) := by
  sorry

theorem proof_gap_exercise_1456_3_4
  (a : ℝ)
  (m : ℝ)
  (n : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : m ∈ (Set.univ : Set ℝ))
  (h3 : n ∈ (Set.univ : Set ℝ))
  (h4 : m > 0)
  (h5 : n > 0)
  (h6 : a ≥ 0)
  (h7 : f = (fun (x : ℝ) => ((Real.rpow x m) * (Real.rpow (a - x) n))))
  (h8 : ContinuousOn f (Set.Icc 0 a))
  (h9 : (lpMaximumPointsOn f (Set.Icc 0 a)) = ({x | x = ((m * a) /. (m + n))}))
  (h10 : (f ((m * a) /. (m + n))) = ((Real.rpow ((m * a) /. (m + n)) m) * (Real.rpow (a - ((m * a) /. (m + n))) n)))
  : ((Real.rpow ((m * a) /. (m + n)) m) * (Real.rpow (a - ((m * a) /. (m + n))) n)) = ((((Real.rpow m m) * (Real.rpow n n)) /. (Real.rpow (m + n) (m + n))) * (Real.rpow a (m + n))) := by
  sorry

theorem proof_gap_exercise_1456_3_5
  (a : ℝ)
  (m : ℝ)
  (n : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : m ∈ (Set.univ : Set ℝ))
  (h3 : n ∈ (Set.univ : Set ℝ))
  (h4 : m > 0)
  (h5 : n > 0)
  (h6 : a ≥ 0)
  (h7 : f = (fun (x : ℝ) => ((Real.rpow x m) * (Real.rpow (a - x) n))))
  (h8 : ContinuousOn f (Set.Icc 0 a))
  (h9 : (lpMaximumPointsOn f (Set.Icc 0 a)) = ({x | x = ((m * a) /. (m + n))}))
  (h10 : (f ((m * a) /. (m + n))) = ((Real.rpow ((m * a) /. (m + n)) m) * (Real.rpow (a - ((m * a) /. (m + n))) n)))
  (h11 : ((Real.rpow ((m * a) /. (m + n)) m) * (Real.rpow (a - ((m * a) /. (m + n))) n)) = ((((Real.rpow m m) * (Real.rpow n n)) /. (Real.rpow (m + n) (m + n))) * (Real.rpow a (m + n))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ a)) → ((f x) ≤ (f ((m * a) /. (m + n)))))) := by
  sorry

theorem proof_gap_exercise_1456_3_6
  (a : ℝ)
  (m : ℝ)
  (n : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : m ∈ (Set.univ : Set ℝ))
  (h3 : n ∈ (Set.univ : Set ℝ))
  (h4 : m > 0)
  (h5 : n > 0)
  (h6 : a ≥ 0)
  (h7 : f = (fun (x : ℝ) => ((Real.rpow x m) * (Real.rpow (a - x) n))))
  (h8 : ContinuousOn f (Set.Icc 0 a))
  (h9 : (lpMaximumPointsOn f (Set.Icc 0 a)) = ({x | x = ((m * a) /. (m + n))}))
  (h10 : (f ((m * a) /. (m + n))) = ((Real.rpow ((m * a) /. (m + n)) m) * (Real.rpow (a - ((m * a) /. (m + n))) n)))
  (h11 : ((Real.rpow ((m * a) /. (m + n)) m) * (Real.rpow (a - ((m * a) /. (m + n))) n)) = ((((Real.rpow m m) * (Real.rpow n n)) /. (Real.rpow (m + n) (m + n))) * (Real.rpow a (m + n))))
  (h12 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ a)) → ((f x) ≤ (f ((m * a) /. (m + n)))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ a)) → (((Real.rpow x m) * (Real.rpow (a - x) n)) ≤ ((((Real.rpow m m) * (Real.rpow n n)) /. (Real.rpow (m + n) (m + n))) * (Real.rpow a (m + n)))))) := by
  sorry

theorem proof_gap_exercise_1456_3_7
  (a : ℝ)
  (m : ℝ)
  (n : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : m ∈ (Set.univ : Set ℝ))
  (h3 : n ∈ (Set.univ : Set ℝ))
  (h4 : m > 0)
  (h5 : n > 0)
  (h6 : a ≥ 0)
  (h7 : f = (fun (x : ℝ) => ((Real.rpow x m) * (Real.rpow (a - x) n))))
  (h8 : ContinuousOn f (Set.Icc 0 a))
  (h9 : (lpMaximumPointsOn f (Set.Icc 0 a)) = ({x | x = ((m * a) /. (m + n))}))
  (h10 : (f ((m * a) /. (m + n))) = ((Real.rpow ((m * a) /. (m + n)) m) * (Real.rpow (a - ((m * a) /. (m + n))) n)))
  (h11 : ((Real.rpow ((m * a) /. (m + n)) m) * (Real.rpow (a - ((m * a) /. (m + n))) n)) = ((((Real.rpow m m) * (Real.rpow n n)) /. (Real.rpow (m + n) (m + n))) * (Real.rpow a (m + n))))
  (h12 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ a)) → ((f x) ≤ (f ((m * a) /. (m + n)))))))
  (h13 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ a)) → (((Real.rpow x m) * (Real.rpow (a - x) n)) ≤ ((((Real.rpow m m) * (Real.rpow n n)) /. (Real.rpow (m + n) (m + n))) * (Real.rpow a (m + n)))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ a)) → (((Real.rpow x m) * (Real.rpow (a - x) n)) ≤ ((((Real.rpow m m) * (Real.rpow n n)) /. (Real.rpow (m + n) (m + n))) * (Real.rpow a (m + n)))))) := by
  sorry

theorem proof_gap_exercise_1456_3_8
  (a : ℝ)
  (m : ℝ)
  (n : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : m ∈ (Set.univ : Set ℝ))
  (h3 : n ∈ (Set.univ : Set ℝ))
  (h4 : m > 0)
  (h5 : n > 0)
  (h6 : a ≥ 0)
  (h7 : f = (fun (x : ℝ) => ((Real.rpow x m) * (Real.rpow (a - x) n))))
  (h8 : ContinuousOn f (Set.Icc 0 a))
  (h9 : (lpMaximumPointsOn f (Set.Icc 0 a)) = ({x | x = ((m * a) /. (m + n))}))
  (h10 : (f ((m * a) /. (m + n))) = ((Real.rpow ((m * a) /. (m + n)) m) * (Real.rpow (a - ((m * a) /. (m + n))) n)))
  (h11 : ((Real.rpow ((m * a) /. (m + n)) m) * (Real.rpow (a - ((m * a) /. (m + n))) n)) = ((((Real.rpow m m) * (Real.rpow n n)) /. (Real.rpow (m + n) (m + n))) * (Real.rpow a (m + n))))
  (h12 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ a)) → ((f x) ≤ (f ((m * a) /. (m + n)))))))
  (h13 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ a)) → (((Real.rpow x m) * (Real.rpow (a - x) n)) ≤ ((((Real.rpow m m) * (Real.rpow n n)) /. (Real.rpow (m + n) (m + n))) * (Real.rpow a (m + n)))))))
  (h14 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ a)) → (((Real.rpow x m) * (Real.rpow (a - x) n)) ≤ ((((Real.rpow m m) * (Real.rpow n n)) /. (Real.rpow (m + n) (m + n))) * (Real.rpow a (m + n)))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ a)) → (((Real.rpow x m) * (Real.rpow (a - x) n)) ≤ ((((Real.rpow m m) * (Real.rpow n n)) /. (Real.rpow (m + n) (m + n))) * (Real.rpow a (m + n)))))) := by
  sorry

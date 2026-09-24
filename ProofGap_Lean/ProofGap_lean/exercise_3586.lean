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

-- exercise: exercise_3586

theorem proof_gap_exercise_3586_1
  (f : (ℝ × ℝ -> ℝ))
  (x : ℝ)
  (y : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (y ∈ (Set.univ : Set ℝ)) ∧ (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) < 1))
  (h3 : (forall (x_1 : ℝ) (y_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (y_1 ∈ (Set.univ : Set ℝ))) ∧ (((x_1 ^ (2 : ℕ)) + (y_1 ^ (2 : ℕ))) < 1)) → ((f (x_1, y_1)) = (Real.rpow ((1 - (x_1 ^ (2 : ℕ))) - (y_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))
  : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) < t)) ∧ (t < 1)) → (|((Real.rpow (1 + t) (1 /. 2)) - (((1 + ((1 /. 2) * t)) - ((1 /. 8) * (t ^ (2 : ℕ)))) + ((1 /. 16) * (t ^ (3 : ℕ)))))| ≤ (t ^ (4 : ℕ))))) := by
  sorry

theorem proof_gap_exercise_3586_2
  (f : (ℝ × ℝ -> ℝ))
  (x : ℝ)
  (y : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (y ∈ (Set.univ : Set ℝ)) ∧ (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) < 1))
  (h3 : (forall (x_1 : ℝ) (y_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (y_1 ∈ (Set.univ : Set ℝ))) ∧ (((x_1 ^ (2 : ℕ)) + (y_1 ^ (2 : ℕ))) < 1)) → ((f (x_1, y_1)) = (Real.rpow ((1 - (x_1 ^ (2 : ℕ))) - (y_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))
  (h4 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) < t)) ∧ (t < 1)) → (|((Real.rpow (1 + t) (1 /. 2)) - (((1 + ((1 /. 2) * t)) - ((1 /. 8) * (t ^ (2 : ℕ)))) + ((1 /. 16) * (t ^ (3 : ℕ)))))| ≤ (t ^ (4 : ℕ))))))
  : (forall (x_1 : ℝ) (y_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (y_1 ∈ (Set.univ : Set ℝ))) ∧ (((x_1 ^ (2 : ℕ)) + (y_1 ^ (2 : ℕ))) < 1)) → ((f (x_1, y_1)) = (Real.rpow ((1 - (x_1 ^ (2 : ℕ))) - (y_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))) := by
  sorry

theorem proof_gap_exercise_3586_3
  (f : (ℝ × ℝ -> ℝ))
  (x : ℝ)
  (y : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (y ∈ (Set.univ : Set ℝ)) ∧ (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) < 1))
  (h3 : (forall (x_1 : ℝ) (y_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (y_1 ∈ (Set.univ : Set ℝ))) ∧ (((x_1 ^ (2 : ℕ)) + (y_1 ^ (2 : ℕ))) < 1)) → ((f (x_1, y_1)) = (Real.rpow ((1 - (x_1 ^ (2 : ℕ))) - (y_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))
  (h4 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) < t)) ∧ (t < 1)) → (|((Real.rpow (1 + t) (1 /. 2)) - (((1 + ((1 /. 2) * t)) - ((1 /. 8) * (t ^ (2 : ℕ)))) + ((1 /. 16) * (t ^ (3 : ℕ)))))| ≤ (t ^ (4 : ℕ))))))
  (h5 : (forall (x_1 : ℝ) (y_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (y_1 ∈ (Set.univ : Set ℝ))) ∧ (((x_1 ^ (2 : ℕ)) + (y_1 ^ (2 : ℕ))) < 1)) → ((f (x_1, y_1)) = (Real.rpow ((1 - (x_1 ^ (2 : ℕ))) - (y_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))
  : (forall (x_1 : ℝ) (y_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (y_1 ∈ (Set.univ : Set ℝ))) ∧ (((x_1 ^ (2 : ℕ)) + (y_1 ^ (2 : ℕ))) < 1)) → ((Real.rpow ((1 - (x_1 ^ (2 : ℕ))) - (y_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) = (Real.rpow ((1 + (-(x_1 ^ (2 : ℕ)))) - (y_1 ^ (2 : ℕ))) (1 /. 2))))) := by
  sorry

theorem proof_gap_exercise_3586_4
  (f : (ℝ × ℝ -> ℝ))
  (x : ℝ)
  (y : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (y ∈ (Set.univ : Set ℝ)) ∧ (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) < 1))
  (h3 : (forall (x_1 : ℝ) (y_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (y_1 ∈ (Set.univ : Set ℝ))) ∧ (((x_1 ^ (2 : ℕ)) + (y_1 ^ (2 : ℕ))) < 1)) → ((f (x_1, y_1)) = (Real.rpow ((1 - (x_1 ^ (2 : ℕ))) - (y_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))
  (h4 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) < t)) ∧ (t < 1)) → (|((Real.rpow (1 + t) (1 /. 2)) - (((1 + ((1 /. 2) * t)) - ((1 /. 8) * (t ^ (2 : ℕ)))) + ((1 /. 16) * (t ^ (3 : ℕ)))))| ≤ (t ^ (4 : ℕ))))))
  (h5 : (forall (x_1 : ℝ) (y_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (y_1 ∈ (Set.univ : Set ℝ))) ∧ (((x_1 ^ (2 : ℕ)) + (y_1 ^ (2 : ℕ))) < 1)) → ((f (x_1, y_1)) = (Real.rpow ((1 - (x_1 ^ (2 : ℕ))) - (y_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))
  (h6 : (forall (x_1 : ℝ) (y_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (y_1 ∈ (Set.univ : Set ℝ))) ∧ (((x_1 ^ (2 : ℕ)) + (y_1 ^ (2 : ℕ))) < 1)) → ((Real.rpow ((1 - (x_1 ^ (2 : ℕ))) - (y_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) = (Real.rpow ((1 + (-(x_1 ^ (2 : ℕ)))) - (y_1 ^ (2 : ℕ))) (1 /. 2))))))
  : (forall (x_1 : ℝ) (y_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (y_1 ∈ (Set.univ : Set ℝ))) ∧ (((x_1 ^ (2 : ℕ)) + (y_1 ^ (2 : ℕ))) < 1)) → ((f (x_1, y_1)) = (Real.rpow ((1 + (-(x_1 ^ (2 : ℕ)))) - (y_1 ^ (2 : ℕ))) (1 /. 2))))) := by
  sorry

theorem proof_gap_exercise_3586_5
  (f : (ℝ × ℝ -> ℝ))
  (x : ℝ)
  (y : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (y ∈ (Set.univ : Set ℝ)) ∧ (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) < 1))
  (h3 : (forall (x_1 : ℝ) (y_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (y_1 ∈ (Set.univ : Set ℝ))) ∧ (((x_1 ^ (2 : ℕ)) + (y_1 ^ (2 : ℕ))) < 1)) → ((f (x_1, y_1)) = (Real.rpow ((1 - (x_1 ^ (2 : ℕ))) - (y_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))
  (h4 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) < t)) ∧ (t < 1)) → (|((Real.rpow (1 + t) (1 /. 2)) - (((1 + ((1 /. 2) * t)) - ((1 /. 8) * (t ^ (2 : ℕ)))) + ((1 /. 16) * (t ^ (3 : ℕ)))))| ≤ (t ^ (4 : ℕ))))))
  (h5 : (forall (x_1 : ℝ) (y_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (y_1 ∈ (Set.univ : Set ℝ))) ∧ (((x_1 ^ (2 : ℕ)) + (y_1 ^ (2 : ℕ))) < 1)) → ((f (x_1, y_1)) = (Real.rpow ((1 - (x_1 ^ (2 : ℕ))) - (y_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))
  (h6 : (forall (x_1 : ℝ) (y_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (y_1 ∈ (Set.univ : Set ℝ))) ∧ (((x_1 ^ (2 : ℕ)) + (y_1 ^ (2 : ℕ))) < 1)) → ((Real.rpow ((1 - (x_1 ^ (2 : ℕ))) - (y_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) = (Real.rpow ((1 + (-(x_1 ^ (2 : ℕ)))) - (y_1 ^ (2 : ℕ))) (1 /. 2))))))
  (h7 : (forall (x_1 : ℝ) (y_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (y_1 ∈ (Set.univ : Set ℝ))) ∧ (((x_1 ^ (2 : ℕ)) + (y_1 ^ (2 : ℕ))) < 1)) → ((f (x_1, y_1)) = (Real.rpow ((1 + (-(x_1 ^ (2 : ℕ)))) - (y_1 ^ (2 : ℕ))) (1 /. 2))))))
  : (forall (x_1 : ℝ) (y_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (y_1 ∈ (Set.univ : Set ℝ))) ∧ (((x_1 ^ (2 : ℕ)) + (y_1 ^ (2 : ℕ))) < 1)) → (|((f (x_1, y_1)) - ((1 - ((1 /. 2) * ((x_1 ^ (2 : ℕ)) + (y_1 ^ (2 : ℕ))))) - ((1 /. 8) * (((x_1 ^ (2 : ℕ)) + (y_1 ^ (2 : ℕ))) ^ (2 : ℕ)))))| ≤ (((x_1 ^ (2 : ℕ)) + (y_1 ^ (2 : ℕ))) ^ (3 : ℕ))))) := by
  sorry

theorem proof_gap_exercise_3586_6
  (f : (ℝ × ℝ -> ℝ))
  (x : ℝ)
  (y : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (y ∈ (Set.univ : Set ℝ)) ∧ (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) < 1))
  (h3 : (forall (x_1 : ℝ) (y_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (y_1 ∈ (Set.univ : Set ℝ))) ∧ (((x_1 ^ (2 : ℕ)) + (y_1 ^ (2 : ℕ))) < 1)) → ((f (x_1, y_1)) = (Real.rpow ((1 - (x_1 ^ (2 : ℕ))) - (y_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))
  (h4 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) < t)) ∧ (t < 1)) → (|((Real.rpow (1 + t) (1 /. 2)) - (((1 + ((1 /. 2) * t)) - ((1 /. 8) * (t ^ (2 : ℕ)))) + ((1 /. 16) * (t ^ (3 : ℕ)))))| ≤ (t ^ (4 : ℕ))))))
  (h5 : (forall (x_1 : ℝ) (y_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (y_1 ∈ (Set.univ : Set ℝ))) ∧ (((x_1 ^ (2 : ℕ)) + (y_1 ^ (2 : ℕ))) < 1)) → ((f (x_1, y_1)) = (Real.rpow ((1 - (x_1 ^ (2 : ℕ))) - (y_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))
  (h6 : (forall (x_1 : ℝ) (y_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (y_1 ∈ (Set.univ : Set ℝ))) ∧ (((x_1 ^ (2 : ℕ)) + (y_1 ^ (2 : ℕ))) < 1)) → ((Real.rpow ((1 - (x_1 ^ (2 : ℕ))) - (y_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) = (Real.rpow ((1 + (-(x_1 ^ (2 : ℕ)))) - (y_1 ^ (2 : ℕ))) (1 /. 2))))))
  (h7 : (forall (x_1 : ℝ) (y_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (y_1 ∈ (Set.univ : Set ℝ))) ∧ (((x_1 ^ (2 : ℕ)) + (y_1 ^ (2 : ℕ))) < 1)) → ((f (x_1, y_1)) = (Real.rpow ((1 + (-(x_1 ^ (2 : ℕ)))) - (y_1 ^ (2 : ℕ))) (1 /. 2))))))
  (h8 : (forall (x_1 : ℝ) (y_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (y_1 ∈ (Set.univ : Set ℝ))) ∧ (((x_1 ^ (2 : ℕ)) + (y_1 ^ (2 : ℕ))) < 1)) → (|((f (x_1, y_1)) - ((1 - ((1 /. 2) * ((x_1 ^ (2 : ℕ)) + (y_1 ^ (2 : ℕ))))) - ((1 /. 8) * (((x_1 ^ (2 : ℕ)) + (y_1 ^ (2 : ℕ))) ^ (2 : ℕ)))))| ≤ (((x_1 ^ (2 : ℕ)) + (y_1 ^ (2 : ℕ))) ^ (3 : ℕ))))))
  : (forall (x_1 : ℝ) (y_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (y_1 ∈ (Set.univ : Set ℝ))) ∧ (((x_1 ^ (2 : ℕ)) + (y_1 ^ (2 : ℕ))) < 1)) → (|((f (x_1, y_1)) - ((1 - ((1 /. 2) * ((x_1 ^ (2 : ℕ)) + (y_1 ^ (2 : ℕ))))) - ((1 /. 8) * (((x_1 ^ (2 : ℕ)) + (y_1 ^ (2 : ℕ))) ^ (2 : ℕ)))))| ≤ (((x_1 ^ (2 : ℕ)) + (y_1 ^ (2 : ℕ))) ^ (3 : ℕ))))) := by
  sorry

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

-- exercise: exercise_2943

theorem proof_gap_exercise_2943_1
  (f : (ℝ -> ℝ))
  (A : (ℕ -> ℝ))
  (B : (ℕ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-Real.pi) < x)) ∧ (x < Real.pi)) → ((f x) = (if (((-Real.pi) < x) ∧ (x < 0)) then (a * x) else (if ((0 < x) ∧ (x < Real.pi)) then (b * x) else (b * x)))))))
  : (A (0 : ℕ)) = (((1 /. Real.pi) * (∫ x in (-Real.pi)..(0 : ℝ), ((a * x) * (1 : ℝ)))) + ((1 /. Real.pi) * (∫ x in (0 : ℝ)..Real.pi, ((b * x) * (1 : ℝ))))) := by
  sorry

theorem proof_gap_exercise_2943_2
  (f : (ℝ -> ℝ))
  (A : (ℕ -> ℝ))
  (B : (ℕ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-Real.pi) < x)) ∧ (x < Real.pi)) → ((f x) = (if (((-Real.pi) < x) ∧ (x < 0)) then (a * x) else (if ((0 < x) ∧ (x < Real.pi)) then (b * x) else (b * x)))))))
  (h4 : (A (0 : ℕ)) = (((1 /. Real.pi) * (∫ x in (-Real.pi)..(0 : ℝ), ((a * x) * (1 : ℝ)))) + ((1 /. Real.pi) * (∫ x in (0 : ℝ)..Real.pi, ((b * x) * (1 : ℝ))))))
  : (((1 /. Real.pi) * (∫ x in (-Real.pi)..(0 : ℝ), ((a * x) * (1 : ℝ)))) + ((1 /. Real.pi) * (∫ x in (0 : ℝ)..Real.pi, ((b * x) * (1 : ℝ))))) = (((b - a) /. 2) * Real.pi) := by
  sorry

theorem proof_gap_exercise_2943_3
  (f : (ℝ -> ℝ))
  (A : (ℕ -> ℝ))
  (B : (ℕ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-Real.pi) < x)) ∧ (x < Real.pi)) → ((f x) = (if (((-Real.pi) < x) ∧ (x < 0)) then (a * x) else (if ((0 < x) ∧ (x < Real.pi)) then (b * x) else (b * x)))))))
  (h4 : (A (0 : ℕ)) = (((1 /. Real.pi) * (∫ x in (-Real.pi)..(0 : ℝ), ((a * x) * (1 : ℝ)))) + ((1 /. Real.pi) * (∫ x in (0 : ℝ)..Real.pi, ((b * x) * (1 : ℝ))))))
  (h5 : (((1 /. Real.pi) * (∫ x in (-Real.pi)..(0 : ℝ), ((a * x) * (1 : ℝ)))) + ((1 /. Real.pi) * (∫ x in (0 : ℝ)..Real.pi, ((b * x) * (1 : ℝ))))) = (((b - a) /. 2) * Real.pi))
  : (A (0 : ℕ)) = (((b - a) /. 2) * Real.pi) := by
  sorry

theorem proof_gap_exercise_2943_4
  (f : (ℝ -> ℝ))
  (A : (ℕ -> ℝ))
  (B : (ℕ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-Real.pi) < x)) ∧ (x < Real.pi)) → ((f x) = (if (((-Real.pi) < x) ∧ (x < 0)) then (a * x) else (if ((0 < x) ∧ (x < Real.pi)) then (b * x) else (b * x)))))))
  (h4 : (A (0 : ℕ)) = (((1 /. Real.pi) * (∫ x in (-Real.pi)..(0 : ℝ), ((a * x) * (1 : ℝ)))) + ((1 /. Real.pi) * (∫ x in (0 : ℝ)..Real.pi, ((b * x) * (1 : ℝ))))))
  (h5 : (((1 /. Real.pi) * (∫ x in (-Real.pi)..(0 : ℝ), ((a * x) * (1 : ℝ)))) + ((1 /. Real.pi) * (∫ x in (0 : ℝ)..Real.pi, ((b * x) * (1 : ℝ))))) = (((b - a) /. 2) * Real.pi))
  (h6 : (A (0 : ℕ)) = (((b - a) /. 2) * Real.pi))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((A n) = (((1 /. Real.pi) * (∫ x in (-Real.pi)..(0 : ℝ), (((a * x) * (Real.cos (n * x))) * (1 : ℝ)))) + ((1 /. Real.pi) * (∫ x in (0 : ℝ)..Real.pi, (((b * x) * (Real.cos (n * x))) * (1 : ℝ)))))) ∧ ((((1 /. Real.pi) * (∫ x in (-Real.pi)..(0 : ℝ), (((a * x) * (Real.cos (n * x))) * (1 : ℝ)))) + ((1 /. Real.pi) * (∫ x in (0 : ℝ)..Real.pi, (((b * x) * (Real.cos (n * x))) * (1 : ℝ))))) = (((a - b) /. ((n ^ (2 : ℕ)) * Real.pi)) * (1 - ((-(1 : ℤ)) ^ n))))))) := by
  sorry

theorem proof_gap_exercise_2943_5
  (f : (ℝ -> ℝ))
  (A : (ℕ -> ℝ))
  (B : (ℕ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-Real.pi) < x)) ∧ (x < Real.pi)) → ((f x) = (if (((-Real.pi) < x) ∧ (x < 0)) then (a * x) else (if ((0 < x) ∧ (x < Real.pi)) then (b * x) else (b * x)))))))
  (h4 : (A (0 : ℕ)) = (((1 /. Real.pi) * (∫ x in (-Real.pi)..(0 : ℝ), ((a * x) * (1 : ℝ)))) + ((1 /. Real.pi) * (∫ x in (0 : ℝ)..Real.pi, ((b * x) * (1 : ℝ))))))
  (h5 : (((1 /. Real.pi) * (∫ x in (-Real.pi)..(0 : ℝ), ((a * x) * (1 : ℝ)))) + ((1 /. Real.pi) * (∫ x in (0 : ℝ)..Real.pi, ((b * x) * (1 : ℝ))))) = (((b - a) /. 2) * Real.pi))
  (h6 : (A (0 : ℕ)) = (((b - a) /. 2) * Real.pi))
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((A n) = (((1 /. Real.pi) * (∫ x in (-Real.pi)..(0 : ℝ), (((a * x) * (Real.cos (n * x))) * (1 : ℝ)))) + ((1 /. Real.pi) * (∫ x in (0 : ℝ)..Real.pi, (((b * x) * (Real.cos (n * x))) * (1 : ℝ)))))) ∧ ((((1 /. Real.pi) * (∫ x in (-Real.pi)..(0 : ℝ), (((a * x) * (Real.cos (n * x))) * (1 : ℝ)))) + ((1 /. Real.pi) * (∫ x in (0 : ℝ)..Real.pi, (((b * x) * (Real.cos (n * x))) * (1 : ℝ))))) = (((a - b) /. ((n ^ (2 : ℕ)) * Real.pi)) * (1 - ((-(1 : ℤ)) ^ n))))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((B n) = (((1 /. Real.pi) * (∫ x in (-Real.pi)..(0 : ℝ), (((a * x) * (Real.sin (n * x))) * (1 : ℝ)))) + ((1 /. Real.pi) * (∫ x in (0 : ℝ)..Real.pi, (((b * x) * (Real.sin (n * x))) * (1 : ℝ)))))) ∧ ((((1 /. Real.pi) * (∫ x in (-Real.pi)..(0 : ℝ), (((a * x) * (Real.sin (n * x))) * (1 : ℝ)))) + ((1 /. Real.pi) * (∫ x in (0 : ℝ)..Real.pi, (((b * x) * (Real.sin (n * x))) * (1 : ℝ))))) = (((a + b) /. n) * ((-(1 : ℤ)) ^ (n + 1))))))) := by
  sorry

theorem proof_gap_exercise_2943_6
  (f : (ℝ -> ℝ))
  (A : (ℕ -> ℝ))
  (B : (ℕ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-Real.pi) < x)) ∧ (x < Real.pi)) → ((f x) = (if (((-Real.pi) < x) ∧ (x < 0)) then (a * x) else (if ((0 < x) ∧ (x < Real.pi)) then (b * x) else (b * x)))))))
  (h4 : (A (0 : ℕ)) = (((1 /. Real.pi) * (∫ x in (-Real.pi)..(0 : ℝ), ((a * x) * (1 : ℝ)))) + ((1 /. Real.pi) * (∫ x in (0 : ℝ)..Real.pi, ((b * x) * (1 : ℝ))))))
  (h5 : (((1 /. Real.pi) * (∫ x in (-Real.pi)..(0 : ℝ), ((a * x) * (1 : ℝ)))) + ((1 /. Real.pi) * (∫ x in (0 : ℝ)..Real.pi, ((b * x) * (1 : ℝ))))) = (((b - a) /. 2) * Real.pi))
  (h6 : (A (0 : ℕ)) = (((b - a) /. 2) * Real.pi))
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((A n) = (((1 /. Real.pi) * (∫ x in (-Real.pi)..(0 : ℝ), (((a * x) * (Real.cos (n * x))) * (1 : ℝ)))) + ((1 /. Real.pi) * (∫ x in (0 : ℝ)..Real.pi, (((b * x) * (Real.cos (n * x))) * (1 : ℝ)))))) ∧ ((((1 /. Real.pi) * (∫ x in (-Real.pi)..(0 : ℝ), (((a * x) * (Real.cos (n * x))) * (1 : ℝ)))) + ((1 /. Real.pi) * (∫ x in (0 : ℝ)..Real.pi, (((b * x) * (Real.cos (n * x))) * (1 : ℝ))))) = (((a - b) /. ((n ^ (2 : ℕ)) * Real.pi)) * (1 - ((-(1 : ℤ)) ^ n))))))))
  (h8 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((B n) = (((1 /. Real.pi) * (∫ x in (-Real.pi)..(0 : ℝ), (((a * x) * (Real.sin (n * x))) * (1 : ℝ)))) + ((1 /. Real.pi) * (∫ x in (0 : ℝ)..Real.pi, (((b * x) * (Real.sin (n * x))) * (1 : ℝ)))))) ∧ ((((1 /. Real.pi) * (∫ x in (-Real.pi)..(0 : ℝ), (((a * x) * (Real.sin (n * x))) * (1 : ℝ)))) + ((1 /. Real.pi) * (∫ x in (0 : ℝ)..Real.pi, (((b * x) * (Real.sin (n * x))) * (1 : ℝ))))) = (((a + b) /. n) * ((-(1 : ℤ)) ^ (n + 1))))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-Real.pi) < x)) ∧ (x < Real.pi)) → ((((((b - a) /. 4) * Real.pi) + (((2 * (a - b)) /. Real.pi) * (∑' k, if (0 : ℕ) ≤ k then ((Real.cos (((2 * k) + 1) * x)) /. (((2 * k) + 1) ^ (2 : ℕ))) else 0))) + ((a + b) * (∑' n, if (1 : ℕ) ≤ n then ((((-(1 : ℤ)) ^ (n + 1)) /. n) * (Real.sin (n * x))) else 0))) = (if (((-Real.pi) < x) ∧ (x < 0)) then (a * x) else (if (x = 0) then 0 else (if ((0 < x) ∧ (x < Real.pi)) then (b * x) else (b * x))))))) := by
  sorry

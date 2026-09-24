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

-- exercise: exercise_2463

theorem proof_gap_exercise_2463_1
  (S : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (V : ℝ)
  (y : ℝ)
  (z : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : V ∈ (Set.univ : Set ℝ))
  (h5 : y ∈ (Set.univ : Set ℝ))
  (h6 : z ∈ (Set.univ : Set ℝ))
  (h7 : a > 0)
  (h8 : b > 0)
  (h9 : c > 0)
  (h10 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-a) ≤ x)) ∧ (x ≤ a)) → ((S x) = (((Real.pi * b) * c) * (1 - ((x ^ (2 : ℕ)) /. (a ^ (2 : ℕ)))))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-a) < x)) ∧ (x < a)) → ((((y ^ (2 : ℕ)) /. ((b ^ (2 : ℕ)) * (1 - ((x ^ (2 : ℕ)) /. (a ^ (2 : ℕ)))))) + ((z ^ (2 : ℕ)) /. ((c ^ (2 : ℕ)) * (1 - ((x ^ (2 : ℕ)) /. (a ^ (2 : ℕ))))))) = 1))) := by
  sorry

theorem proof_gap_exercise_2463_2
  (S : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (z : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (V : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : V ∈ (Set.univ : Set ℝ))
  (h5 : a > 0)
  (h6 : b > 0)
  (h7 : c > 0)
  (h8 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-a) < x)) ∧ (x < a)) → (((((y x) ^ (2 : ℕ)) /. ((b ^ (2 : ℕ)) * (1 - ((x ^ (2 : ℕ)) /. (a ^ (2 : ℕ)))))) + (((z x) ^ (2 : ℕ)) /. ((c ^ (2 : ℕ)) * (1 - ((x ^ (2 : ℕ)) /. (a ^ (2 : ℕ))))))) = 1))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-a) ≤ x)) ∧ (x ≤ a)) → ((S x) = (((Real.pi * b) * c) * (1 - ((x ^ (2 : ℕ)) /. (a ^ (2 : ℕ)))))))) := by
  sorry

theorem proof_gap_exercise_2463_3
  (S : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (z : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (V : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : V ∈ (Set.univ : Set ℝ))
  (h5 : a > 0)
  (h6 : b > 0)
  (h7 : c > 0)
  (h8 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-a) < x)) ∧ (x < a)) → (((((y x) ^ (2 : ℕ)) /. ((b ^ (2 : ℕ)) * (1 - ((x ^ (2 : ℕ)) /. (a ^ (2 : ℕ)))))) + (((z x) ^ (2 : ℕ)) /. ((c ^ (2 : ℕ)) * (1 - ((x ^ (2 : ℕ)) /. (a ^ (2 : ℕ))))))) = 1))))
  (h9 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-a) ≤ x)) ∧ (x ≤ a)) → ((S x) = (((Real.pi * b) * c) * (1 - ((x ^ (2 : ℕ)) /. (a ^ (2 : ℕ)))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (V = (∫ x_1 in (-a)..a, ((S x_1) * (1 : ℝ)))))) := by
  sorry

theorem proof_gap_exercise_2463_4
  (S : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (z : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (V : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : V ∈ (Set.univ : Set ℝ))
  (h5 : a > 0)
  (h6 : b > 0)
  (h7 : c > 0)
  (h8 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-a) < x)) ∧ (x < a)) → (((((y x) ^ (2 : ℕ)) /. ((b ^ (2 : ℕ)) * (1 - ((x ^ (2 : ℕ)) /. (a ^ (2 : ℕ)))))) + (((z x) ^ (2 : ℕ)) /. ((c ^ (2 : ℕ)) * (1 - ((x ^ (2 : ℕ)) /. (a ^ (2 : ℕ))))))) = 1))))
  (h9 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-a) ≤ x)) ∧ (x ≤ a)) → ((S x) = (((Real.pi * b) * c) * (1 - ((x ^ (2 : ℕ)) /. (a ^ (2 : ℕ)))))))))
  (h10 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (V = (∫ x_1 in (-a)..a, ((S x_1) * (1 : ℝ)))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (V = (∫ x_1 in (-a)..a, ((((((1 : ℝ) - ((x_1 ^ (2 : ℕ)) /. (a ^ (2 : ℕ)))) * Real.pi) * b) * c) * (1 : ℝ)))))) := by
  sorry

theorem proof_gap_exercise_2463_5
  (S : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (z : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (V : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : V ∈ (Set.univ : Set ℝ))
  (h5 : a > 0)
  (h6 : b > 0)
  (h7 : c > 0)
  (h8 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-a) < x)) ∧ (x < a)) → (((((y x) ^ (2 : ℕ)) /. ((b ^ (2 : ℕ)) * (1 - ((x ^ (2 : ℕ)) /. (a ^ (2 : ℕ)))))) + (((z x) ^ (2 : ℕ)) /. ((c ^ (2 : ℕ)) * (1 - ((x ^ (2 : ℕ)) /. (a ^ (2 : ℕ))))))) = 1))))
  (h9 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-a) ≤ x)) ∧ (x ≤ a)) → ((S x) = (((Real.pi * b) * c) * (1 - ((x ^ (2 : ℕ)) /. (a ^ (2 : ℕ)))))))))
  (h10 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (V = (∫ x_1 in (-a)..a, ((S x_1) * (1 : ℝ)))))))
  (h11 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (V = (∫ x_1 in (-a)..a, ((((((1 : ℝ) - ((x_1 ^ (2 : ℕ)) /. (a ^ (2 : ℕ)))) * Real.pi) * b) * c) * (1 : ℝ)))))))
  : V = (((((4 /. 3) * Real.pi) * a) * b) * c) := by
  sorry

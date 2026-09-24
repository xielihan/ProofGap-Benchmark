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

-- exercise: exercise_2460

theorem proof_gap_exercise_2460_1
  (S : (ℝ -> ℝ))
  (V : ℝ)
  (H : ℝ)
  (A : ℝ)
  (B : ℝ)
  (C : ℝ)
  (a : ℝ)
  (b : ℝ)
  (h1 : V ∈ (Set.univ : Set ℝ))
  (h2 : H ∈ (Set.univ : Set ℝ))
  (h3 : A ∈ (Set.univ : Set ℝ))
  (h4 : B ∈ (Set.univ : Set ℝ))
  (h5 : C ∈ (Set.univ : Set ℝ))
  (h6 : a ∈ (Set.univ : Set ℝ))
  (h7 : b ∈ (Set.univ : Set ℝ))
  (h8 : a < b)
  (h9 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ (x ≤ b)) → ((S x) = (((A * (x ^ (2 : ℕ))) + (B * x)) + C)))))
  (h10 : H = (b - a))
  (h11 : V = ((((A /. 3) * ((b ^ (3 : ℕ)) - (a ^ (3 : ℕ)))) + ((B /. 2) * ((b ^ (2 : ℕ)) - (a ^ (2 : ℕ))))) + (C * (b - a))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (V = (∫ x_1 in a..b, ((((A * (x_1 ^ (2 : ℕ))) + (B * x_1)) + C) * (1 : ℝ)))))) := by
  sorry

theorem proof_gap_exercise_2460_2
  (S : (ℝ -> ℝ))
  (V : ℝ)
  (H : ℝ)
  (A : ℝ)
  (B : ℝ)
  (C : ℝ)
  (a : ℝ)
  (b : ℝ)
  (h1 : V ∈ (Set.univ : Set ℝ))
  (h2 : H ∈ (Set.univ : Set ℝ))
  (h3 : A ∈ (Set.univ : Set ℝ))
  (h4 : B ∈ (Set.univ : Set ℝ))
  (h5 : C ∈ (Set.univ : Set ℝ))
  (h6 : a ∈ (Set.univ : Set ℝ))
  (h7 : b ∈ (Set.univ : Set ℝ))
  (h8 : a < b)
  (h9 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ (x ≤ b)) → ((S x) = (((A * (x ^ (2 : ℕ))) + (B * x)) + C)))))
  (h10 : H = (b - a))
  (h11 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (V = (∫ x_1 in a..b, ((((A * (x_1 ^ (2 : ℕ))) + (B * x_1)) + C) * (1 : ℝ)))))))
  : V = ((((A /. 3) * ((b ^ (3 : ℕ)) - (a ^ (3 : ℕ)))) + ((B /. 2) * ((b ^ (2 : ℕ)) - (a ^ (2 : ℕ))))) + (C * (b - a))) := by
  sorry

theorem proof_gap_exercise_2460_3
  (S : (ℝ -> ℝ))
  (V : ℝ)
  (H : ℝ)
  (A : ℝ)
  (B : ℝ)
  (C : ℝ)
  (a : ℝ)
  (b : ℝ)
  (h1 : V ∈ (Set.univ : Set ℝ))
  (h2 : H ∈ (Set.univ : Set ℝ))
  (h3 : A ∈ (Set.univ : Set ℝ))
  (h4 : B ∈ (Set.univ : Set ℝ))
  (h5 : C ∈ (Set.univ : Set ℝ))
  (h6 : a ∈ (Set.univ : Set ℝ))
  (h7 : b ∈ (Set.univ : Set ℝ))
  (h8 : a < b)
  (h9 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ (x ≤ b)) → ((S x) = (((A * (x ^ (2 : ℕ))) + (B * x)) + C)))))
  (h10 : H = (b - a))
  (h11 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (V = (∫ x_1 in a..b, ((((A * (x_1 ^ (2 : ℕ))) + (B * x_1)) + C) * (1 : ℝ)))))))
  (h12 : V = ((((A /. 3) * ((b ^ (3 : ℕ)) - (a ^ (3 : ℕ)))) + ((B /. 2) * ((b ^ (2 : ℕ)) - (a ^ (2 : ℕ))))) + (C * (b - a))))
  : V = (((b - a) /. 6) * ((((2 * A) * (((b ^ (2 : ℕ)) + (a * b)) + (a ^ (2 : ℕ)))) + ((3 * B) * (a + b))) + (6 * C))) := by
  sorry

theorem proof_gap_exercise_2460_4
  (S : (ℝ -> ℝ))
  (V : ℝ)
  (H : ℝ)
  (A : ℝ)
  (B : ℝ)
  (C : ℝ)
  (a : ℝ)
  (b : ℝ)
  (h1 : V ∈ (Set.univ : Set ℝ))
  (h2 : H ∈ (Set.univ : Set ℝ))
  (h3 : A ∈ (Set.univ : Set ℝ))
  (h4 : B ∈ (Set.univ : Set ℝ))
  (h5 : C ∈ (Set.univ : Set ℝ))
  (h6 : a ∈ (Set.univ : Set ℝ))
  (h7 : b ∈ (Set.univ : Set ℝ))
  (h8 : a < b)
  (h9 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ (x ≤ b)) → ((S x) = (((A * (x ^ (2 : ℕ))) + (B * x)) + C)))))
  (h10 : H = (b - a))
  (h11 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (V = (∫ x_1 in a..b, ((((A * (x_1 ^ (2 : ℕ))) + (B * x_1)) + C) * (1 : ℝ)))))))
  (h12 : V = ((((A /. 3) * ((b ^ (3 : ℕ)) - (a ^ (3 : ℕ)))) + ((B /. 2) * ((b ^ (2 : ℕ)) - (a ^ (2 : ℕ))))) + (C * (b - a))))
  (h13 : V = (((b - a) /. 6) * ((((2 * A) * (((b ^ (2 : ℕ)) + (a * b)) + (a ^ (2 : ℕ)))) + ((3 * B) * (a + b))) + (6 * C))))
  : V = ((H /. 6) * (((((((((A * (a ^ (2 : ℕ))) + (B * a)) + C) + (A * (b ^ (2 : ℕ)))) + (B * b)) + C) + (A * (((a ^ (2 : ℕ)) + ((2 * a) * b)) + (b ^ (2 : ℕ))))) + ((2 * B) * (a + b))) + (4 * C))) := by
  sorry

theorem proof_gap_exercise_2460_5
  (S : (ℝ -> ℝ))
  (V : ℝ)
  (H : ℝ)
  (A : ℝ)
  (B : ℝ)
  (C : ℝ)
  (a : ℝ)
  (b : ℝ)
  (h1 : V ∈ (Set.univ : Set ℝ))
  (h2 : H ∈ (Set.univ : Set ℝ))
  (h3 : A ∈ (Set.univ : Set ℝ))
  (h4 : B ∈ (Set.univ : Set ℝ))
  (h5 : C ∈ (Set.univ : Set ℝ))
  (h6 : a ∈ (Set.univ : Set ℝ))
  (h7 : b ∈ (Set.univ : Set ℝ))
  (h8 : a < b)
  (h9 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ (x ≤ b)) → ((S x) = (((A * (x ^ (2 : ℕ))) + (B * x)) + C)))))
  (h10 : H = (b - a))
  (h11 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (V = (∫ x_1 in a..b, ((((A * (x_1 ^ (2 : ℕ))) + (B * x_1)) + C) * (1 : ℝ)))))))
  (h12 : V = ((((A /. 3) * ((b ^ (3 : ℕ)) - (a ^ (3 : ℕ)))) + ((B /. 2) * ((b ^ (2 : ℕ)) - (a ^ (2 : ℕ))))) + (C * (b - a))))
  (h13 : V = (((b - a) /. 6) * ((((2 * A) * (((b ^ (2 : ℕ)) + (a * b)) + (a ^ (2 : ℕ)))) + ((3 * B) * (a + b))) + (6 * C))))
  (h14 : V = ((H /. 6) * (((((((((A * (a ^ (2 : ℕ))) + (B * a)) + C) + (A * (b ^ (2 : ℕ)))) + (B * b)) + C) + (A * (((a ^ (2 : ℕ)) + ((2 * a) * b)) + (b ^ (2 : ℕ))))) + ((2 * B) * (a + b))) + (4 * C))))
  : V = ((H /. 6) * (((S a) + (S b)) + (4 * (S ((a + b) /. 2))))) := by
  sorry

theorem proof_gap_exercise_2460_6
  (S : (ℝ -> ℝ))
  (V : ℝ)
  (H : ℝ)
  (A : ℝ)
  (B : ℝ)
  (C : ℝ)
  (a : ℝ)
  (b : ℝ)
  (h1 : V ∈ (Set.univ : Set ℝ))
  (h2 : H ∈ (Set.univ : Set ℝ))
  (h3 : A ∈ (Set.univ : Set ℝ))
  (h4 : B ∈ (Set.univ : Set ℝ))
  (h5 : C ∈ (Set.univ : Set ℝ))
  (h6 : a ∈ (Set.univ : Set ℝ))
  (h7 : b ∈ (Set.univ : Set ℝ))
  (h8 : a < b)
  (h9 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ (x ≤ b)) → ((S x) = (((A * (x ^ (2 : ℕ))) + (B * x)) + C)))))
  (h10 : H = (b - a))
  (h11 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (V = (∫ x_1 in a..b, ((((A * (x_1 ^ (2 : ℕ))) + (B * x_1)) + C) * (1 : ℝ)))))))
  (h12 : V = ((((A /. 3) * ((b ^ (3 : ℕ)) - (a ^ (3 : ℕ)))) + ((B /. 2) * ((b ^ (2 : ℕ)) - (a ^ (2 : ℕ))))) + (C * (b - a))))
  (h13 : V = (((b - a) /. 6) * ((((2 * A) * (((b ^ (2 : ℕ)) + (a * b)) + (a ^ (2 : ℕ)))) + ((3 * B) * (a + b))) + (6 * C))))
  (h14 : V = ((H /. 6) * (((((((((A * (a ^ (2 : ℕ))) + (B * a)) + C) + (A * (b ^ (2 : ℕ)))) + (B * b)) + C) + (A * (((a ^ (2 : ℕ)) + ((2 * a) * b)) + (b ^ (2 : ℕ))))) + ((2 * B) * (a + b))) + (4 * C))))
  (h15 : V = ((H /. 6) * (((S a) + (S b)) + (4 * (S ((a + b) /. 2))))))
  : V = ((H /. 6) * (((S a) + (4 * (S ((a + b) /. 2)))) + (S b))) := by
  sorry

theorem proof_gap_exercise_2460_7
  (S : (ℝ -> ℝ))
  (V : ℝ)
  (H : ℝ)
  (A : ℝ)
  (B : ℝ)
  (C : ℝ)
  (a : ℝ)
  (b : ℝ)
  (h1 : V ∈ (Set.univ : Set ℝ))
  (h2 : H ∈ (Set.univ : Set ℝ))
  (h3 : A ∈ (Set.univ : Set ℝ))
  (h4 : B ∈ (Set.univ : Set ℝ))
  (h5 : C ∈ (Set.univ : Set ℝ))
  (h6 : a ∈ (Set.univ : Set ℝ))
  (h7 : b ∈ (Set.univ : Set ℝ))
  (h8 : a < b)
  (h9 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ (x ≤ b)) → ((S x) = (((A * (x ^ (2 : ℕ))) + (B * x)) + C)))))
  (h10 : H = (b - a))
  (h11 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (V = (∫ x_1 in a..b, ((((A * (x_1 ^ (2 : ℕ))) + (B * x_1)) + C) * (1 : ℝ)))))))
  (h12 : V = ((((A /. 3) * ((b ^ (3 : ℕ)) - (a ^ (3 : ℕ)))) + ((B /. 2) * ((b ^ (2 : ℕ)) - (a ^ (2 : ℕ))))) + (C * (b - a))))
  (h13 : V = (((b - a) /. 6) * ((((2 * A) * (((b ^ (2 : ℕ)) + (a * b)) + (a ^ (2 : ℕ)))) + ((3 * B) * (a + b))) + (6 * C))))
  (h14 : V = ((H /. 6) * (((((((((A * (a ^ (2 : ℕ))) + (B * a)) + C) + (A * (b ^ (2 : ℕ)))) + (B * b)) + C) + (A * (((a ^ (2 : ℕ)) + ((2 * a) * b)) + (b ^ (2 : ℕ))))) + ((2 * B) * (a + b))) + (4 * C))))
  (h15 : V = ((H /. 6) * (((S a) + (S b)) + (4 * (S ((a + b) /. 2))))))
  (h16 : V = ((H /. 6) * (((S a) + (4 * (S ((a + b) /. 2)))) + (S b))))
  : V = ((H /. 6) * (((S a) + (4 * (S ((a + b) /. 2)))) + (S b))) := by
  sorry

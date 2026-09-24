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

-- exercise: exercise_3131

theorem proof_gap_exercise_3131_1
  (f : (ℝ -> ℝ))
  (B : (ℕ × ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (k : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : k ∈ (Set.univ : Set ℝ))
  (h4 : a < b)
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ (x ≤ b)) → ((f x) = (Real.exp (k * x))))))
  : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Icc a b))) → ((B (n, x)) = (∑ j ∈ Finset.Icc (0 : ℕ) n, (((f (a + ((b - a) * (j /. n)))) * (Nat.choose n j)) * ((((x - a) ^ j) * ((b - x) ^ (n - j))) /. ((b - a) ^ n))))))) := by
  sorry

theorem proof_gap_exercise_3131_2
  (f : (ℝ -> ℝ))
  (B : (ℕ × ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (k : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : k ∈ (Set.univ : Set ℝ))
  (h4 : a < b)
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ (x ≤ b)) → ((f x) = (Real.exp (k * x))))))
  (h6 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Icc a b))) → ((B (n, x)) = (∑ j ∈ Finset.Icc (0 : ℕ) n, (((f (a + ((b - a) * (j /. n)))) * (Nat.choose n j)) * ((((x - a) ^ j) * ((b - x) ^ (n - j))) /. ((b - a) ^ n))))))))
  : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Icc a b))) → ((B (n, x)) = (∑ j ∈ Finset.Icc (0 : ℕ) n, (((Real.exp (k * (a + ((b - a) * (j /. n))))) * (Nat.choose n j)) * ((((x - a) ^ j) * ((b - x) ^ (n - j))) /. ((b - a) ^ n))))))) := by
  sorry

theorem proof_gap_exercise_3131_3
  (f : (ℝ -> ℝ))
  (B : (ℕ × ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (k : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : k ∈ (Set.univ : Set ℝ))
  (h4 : a < b)
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ (x ≤ b)) → ((f x) = (Real.exp (k * x))))))
  (h6 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Icc a b))) → ((B (n, x)) = (∑ j ∈ Finset.Icc (0 : ℕ) n, (((f (a + ((b - a) * (j /. n)))) * (Nat.choose n j)) * ((((x - a) ^ j) * ((b - x) ^ (n - j))) /. ((b - a) ^ n))))))))
  (h7 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Icc a b))) → ((B (n, x)) = (∑ j ∈ Finset.Icc (0 : ℕ) n, (((Real.exp (k * (a + ((b - a) * (j /. n))))) * (Nat.choose n j)) * ((((x - a) ^ j) * ((b - x) ^ (n - j))) /. ((b - a) ^ n))))))))
  : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Icc a b))) → ((B (n, x)) = (((Real.exp (k * a)) /. ((b - a) ^ n)) * (∑ j ∈ Finset.Icc (0 : ℕ) n, ((((Real.exp ((k * (b - a)) * (j /. n))) * (Nat.choose n j)) * ((x - a) ^ j)) * ((b - x) ^ (n - j)))))))) := by
  sorry

theorem proof_gap_exercise_3131_4
  (f : (ℝ -> ℝ))
  (B : (ℕ × ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (k : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : k ∈ (Set.univ : Set ℝ))
  (h4 : a < b)
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ (x ≤ b)) → ((f x) = (Real.exp (k * x))))))
  (h6 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Icc a b))) → ((B (n, x)) = (∑ j ∈ Finset.Icc (0 : ℕ) n, (((f (a + ((b - a) * (j /. n)))) * (Nat.choose n j)) * ((((x - a) ^ j) * ((b - x) ^ (n - j))) /. ((b - a) ^ n))))))))
  (h7 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Icc a b))) → ((B (n, x)) = (∑ j ∈ Finset.Icc (0 : ℕ) n, (((Real.exp (k * (a + ((b - a) * (j /. n))))) * (Nat.choose n j)) * ((((x - a) ^ j) * ((b - x) ^ (n - j))) /. ((b - a) ^ n))))))))
  (h8 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Icc a b))) → ((B (n, x)) = (((Real.exp (k * a)) /. ((b - a) ^ n)) * (∑ j ∈ Finset.Icc (0 : ℕ) n, ((((Real.exp ((k * (b - a)) * (j /. n))) * (Nat.choose n j)) * ((x - a) ^ j)) * ((b - x) ^ (n - j)))))))))
  : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Icc a b))) → ((B (n, x)) = (((Real.exp (k * a)) /. ((b - a) ^ n)) * (((((Real.exp ((k * (b - a)) /. n)) * (x - a)) + b) - x) ^ n))))) := by
  sorry

theorem proof_gap_exercise_3131_5
  (f : (ℝ -> ℝ))
  (B : (ℕ × ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (k : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : k ∈ (Set.univ : Set ℝ))
  (h4 : a < b)
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ (x ≤ b)) → ((f x) = (Real.exp (k * x))))))
  (h6 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Icc a b))) → ((B (n, x)) = (∑ j ∈ Finset.Icc (0 : ℕ) n, (((f (a + ((b - a) * (j /. n)))) * (Nat.choose n j)) * ((((x - a) ^ j) * ((b - x) ^ (n - j))) /. ((b - a) ^ n))))))))
  (h7 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Icc a b))) → ((B (n, x)) = (∑ j ∈ Finset.Icc (0 : ℕ) n, (((Real.exp (k * (a + ((b - a) * (j /. n))))) * (Nat.choose n j)) * ((((x - a) ^ j) * ((b - x) ^ (n - j))) /. ((b - a) ^ n))))))))
  (h8 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Icc a b))) → ((B (n, x)) = (((Real.exp (k * a)) /. ((b - a) ^ n)) * (∑ j ∈ Finset.Icc (0 : ℕ) n, ((((Real.exp ((k * (b - a)) * (j /. n))) * (Nat.choose n j)) * ((x - a) ^ j)) * ((b - x) ^ (n - j)))))))))
  (h9 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Icc a b))) → ((B (n, x)) = (((Real.exp (k * a)) /. ((b - a) ^ n)) * (((((Real.exp ((k * (b - a)) /. n)) * (x - a)) + b) - x) ^ n))))))
  : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Icc a b))) → ((B (n, x)) = ((Real.exp (k * a)) * ((((((Real.exp ((k * (b - a)) /. n)) * (x - a)) + b) - x) /. (b - a)) ^ n))))) := by
  sorry

theorem proof_gap_exercise_3131_6
  (f : (ℝ -> ℝ))
  (B : (ℕ × ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (k : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : k ∈ (Set.univ : Set ℝ))
  (h4 : a < b)
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ (x ≤ b)) → ((f x) = (Real.exp (k * x))))))
  (h6 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Icc a b))) → ((B (n, x)) = (∑ j ∈ Finset.Icc (0 : ℕ) n, (((f (a + ((b - a) * (j /. n)))) * (Nat.choose n j)) * ((((x - a) ^ j) * ((b - x) ^ (n - j))) /. ((b - a) ^ n))))))))
  (h7 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Icc a b))) → ((B (n, x)) = (∑ j ∈ Finset.Icc (0 : ℕ) n, (((Real.exp (k * (a + ((b - a) * (j /. n))))) * (Nat.choose n j)) * ((((x - a) ^ j) * ((b - x) ^ (n - j))) /. ((b - a) ^ n))))))))
  (h8 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Icc a b))) → ((B (n, x)) = (((Real.exp (k * a)) /. ((b - a) ^ n)) * (∑ j ∈ Finset.Icc (0 : ℕ) n, ((((Real.exp ((k * (b - a)) * (j /. n))) * (Nat.choose n j)) * ((x - a) ^ j)) * ((b - x) ^ (n - j)))))))))
  (h9 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Icc a b))) → ((B (n, x)) = (((Real.exp (k * a)) /. ((b - a) ^ n)) * (((((Real.exp ((k * (b - a)) /. n)) * (x - a)) + b) - x) ^ n))))))
  (h10 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Icc a b))) → ((B (n, x)) = ((Real.exp (k * a)) * ((((((Real.exp ((k * (b - a)) /. n)) * (x - a)) + b) - x) /. (b - a)) ^ n))))))
  : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Icc a b))) → ((B (n, x)) = ((Real.exp (k * a)) * ((1 + (((Real.exp ((k * (b - a)) /. n)) - 1) * ((x - a) /. (b - a)))) ^ n))))) → (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Icc a b))) → ((B (n, x)) = ((Real.exp (k * a)) * ((1 + (((Real.exp ((k * (b - a)) /. n)) - 1) * ((x - a) /. (b - a)))) ^ n))))) := by
  sorry

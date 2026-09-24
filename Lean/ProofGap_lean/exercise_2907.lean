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

-- exercise: exercise_2907

theorem proof_gap_exercise_2907_1
  (F : (ℝ -> ℝ))
  (h1 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| ≤ 1)) → ((F x) = (∑' n_1, if (0 : ℕ) ≤ n_1 then (((-(1 : ℤ)) ^ n_1) * ((x ^ ((2 * n_1) + 1)) /. ((2 * n_1) + 1))) else 0)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → (((iteratedDeriv 1 (fun t => F t) x) = (∑' n, if (0 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) * (x ^ (2 * n))) else 0)) ∧ ((∑' n, if (0 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) * (x ^ (2 * n))) else 0) = (1 /. (1 + (x ^ (2 : ℕ)))))))) := by
  sorry

theorem proof_gap_exercise_2907_2
  (F : (ℝ -> ℝ))
  (h1 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| ≤ 1)) → ((F x) = (∑' n_1, if (0 : ℕ) ≤ n_1 then (((-(1 : ℤ)) ^ n_1) * ((x ^ ((2 * n_1) + 1)) /. ((2 * n_1) + 1))) else 0)))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → (((iteratedDeriv 1 (fun t => F t) x) = (∑' n, if (0 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) * (x ^ (2 * n))) else 0)) ∧ ((∑' n, if (0 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) * (x ^ (2 * n))) else 0) = (1 /. (1 + (x ^ (2 : ℕ)))))))))
  : (F (0 : ℝ)) = 0 := by
  sorry

theorem proof_gap_exercise_2907_3
  (F : (ℝ -> ℝ))
  (h1 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| ≤ 1)) → ((F x) = (∑' n_1, if (0 : ℕ) ≤ n_1 then (((-(1 : ℤ)) ^ n_1) * ((x ^ ((2 * n_1) + 1)) /. ((2 * n_1) + 1))) else 0)))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → (((iteratedDeriv 1 (fun t_1 => F t_1) x) = (∑' n, if (0 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) * (x ^ (2 * n))) else 0)) ∧ ((∑' n, if (0 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) * (x ^ (2 * n))) else 0) = (1 /. (1 + (x ^ (2 : ℕ)))))))))
  (h3 : (F (0 : ℝ)) = 0)
  : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((F x) = (∫ t_1 in (0 : ℝ)..x, (((1 : ℝ) /. ((1 : ℝ) + (t_1 ^ (2 : ℕ)))) * (1 : ℝ)))))))) := by
  sorry

theorem proof_gap_exercise_2907_4
  (F : (ℝ -> ℝ))
  (h1 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| ≤ 1)) → ((F x) = (∑' n_1, if (0 : ℕ) ≤ n_1 then (((-(1 : ℤ)) ^ n_1) * ((x ^ ((2 * n_1) + 1)) /. ((2 * n_1) + 1))) else 0)))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → (((iteratedDeriv 1 (fun t_1 => F t_1) x) = (∑' n, if (0 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) * (x ^ (2 * n))) else 0)) ∧ ((∑' n, if (0 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) * (x ^ (2 * n))) else 0) = (1 /. (1 + (x ^ (2 : ℕ)))))))))
  (h3 : (F (0 : ℝ)) = 0)
  (h4 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((F x) = (∫ t_1 in (0 : ℝ)..x, (((1 : ℝ) /. ((1 : ℝ) + (t_1 ^ (2 : ℕ)))) * (1 : ℝ)))))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((F x) = (Real.arctan x)))) := by
  sorry

theorem proof_gap_exercise_2907_5
  (F : (ℝ -> ℝ))
  (h1 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| ≤ 1)) → ((F x) = (∑' n_1, if (0 : ℕ) ≤ n_1 then (((-(1 : ℤ)) ^ n_1) * ((x ^ ((2 * n_1) + 1)) /. ((2 * n_1) + 1))) else 0)))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → (((iteratedDeriv 1 (fun t_1 => F t_1) x) = (∑' n, if (0 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) * (x ^ (2 * n))) else 0)) ∧ ((∑' n, if (0 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) * (x ^ (2 * n))) else 0) = (1 /. (1 + (x ^ (2 : ℕ)))))))))
  (h3 : (F (0 : ℝ)) = 0)
  (h4 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((F x) = (∫ t_1 in (0 : ℝ)..x, (((1 : ℝ) /. ((1 : ℝ) + (t_1 ^ (2 : ℕ)))) * (1 : ℝ)))))))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((F x) = (Real.arctan x)))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| ≤ 1)) → ((∑' n, if (0 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) * ((x ^ ((2 * n) + 1)) /. ((2 * n) + 1))) else 0) = (Real.arctan x)))) := by
  sorry

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

-- exercise: exercise_3356

theorem proof_gap_exercise_3356_1
  (z : (ℝ × ℝ -> ℝ))
  (v_uCF_u86 : (ℤ × ℝ -> ℝ))
  (n : ℕ)
  (h1 : (n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1})))
  (h2 : ContDiffOn ℝ (n : ℕ∞) z ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv (n - 1) (fun t => z (x, t)) y) = (v_uCF_u86 ((n - 1), x))))) := by
  sorry

theorem proof_gap_exercise_3356_2
  (z : (ℝ × ℝ -> ℝ))
  (v_uCF_u86 : (ℤ × ℝ -> ℝ))
  (n : ℕ)
  (h1 : (n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1})))
  (h2 : ContDiffOn ℝ (n : ℕ∞) z ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h3 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv (n - 1) (fun t => z (x, t)) y) = (v_uCF_u86 ((n - 1), x))))))
  : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv (n - 2) (fun t => z (x, t)) y) = ((y * (v_uCF_u86 ((n - 1), x))) + (v_uCF_u86 ((n - 2), x)))))) := by
  sorry

theorem proof_gap_exercise_3356_3
  (z : (ℝ × ℝ -> ℝ))
  (v_uCF_u86 : (ℤ × ℝ -> ℝ))
  (n : ℕ)
  (h1 : (n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1})))
  (h2 : ContDiffOn ℝ (n : ℕ∞) z ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h3 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv (n - 1) (fun t => z (x, t)) y) = (v_uCF_u86 ((n - 1), x))))))
  (h4 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv (n - 2) (fun t => z (x, t)) y) = ((y * (v_uCF_u86 ((n - 1), x))) + (v_uCF_u86 ((n - 2), x)))))))
  : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((z (x, y)) = (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), ((y ^ i) * (v_uCF_u86 ((i : ℤ), x))))))) := by
  sorry

theorem proof_gap_exercise_3356_4
  (z : (ℝ × ℝ -> ℝ))
  (v_uCF_u86 : (ℤ × ℝ -> ℝ))
  (n : ℕ)
  (h1 : (n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1})))
  (h2 : ContDiffOn ℝ (n : ℕ∞) z ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h3 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv (n - 1) (fun t => z (x, t)) y) = (v_uCF_u86 ((n - 1), x))))))
  (h4 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv (n - 2) (fun t => z (x, t)) y) = ((y * (v_uCF_u86 ((n - 1), x))) + (v_uCF_u86 ((n - 2), x)))))))
  (h5 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((z (x, y)) = (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), ((y ^ i) * (v_uCF_u86 ((i : ℤ), x))))))))
  : (z = (fun (p : ℝ × ℝ) => (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), ((p.2 ^ i) * (v_uCF_u86 ((i : ℤ), p.1)))))) → (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv n (fun t => z (x, t)) y) = 0))) := by
  sorry

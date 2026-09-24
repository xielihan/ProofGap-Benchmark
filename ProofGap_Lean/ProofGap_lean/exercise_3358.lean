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

-- exercise: exercise_3358

theorem proof_gap_exercise_3358_1
  (z : (ℝ × ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => z (x, t)) y) = ((x ^ (2 : ℕ)) + (2 * y))))) := by
  sorry

theorem proof_gap_exercise_3358_2
  (z : (ℝ × ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => z (x, t)) y) = ((x ^ (2 : ℕ)) + (2 * y))))))
  : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((z (x, y)) = ((((x ^ (2 : ℕ)) * y) + (y ^ (2 : ℕ))) + (v_uCF_u86 x))))) := by
  sorry

theorem proof_gap_exercise_3358_3
  (z : (ℝ × ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => z (x, t)) y) = ((x ^ (2 : ℕ)) + (2 * y))))))
  (h2 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((z (x, y)) = ((((x ^ (2 : ℕ)) * y) + (y ^ (2 : ℕ))) + (v_uCF_u86 x))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((z (x, (x ^ (2 : ℕ)))) = (((x ^ (4 : ℕ)) + (x ^ (4 : ℕ))) + (v_uCF_u86 x))))) := by
  sorry

theorem proof_gap_exercise_3358_4
  (z : (ℝ × ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => z (x, t)) y) = ((x ^ (2 : ℕ)) + (2 * y))))))
  (h2 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((z (x, y)) = ((((x ^ (2 : ℕ)) * y) + (y ^ (2 : ℕ))) + (v_uCF_u86 x))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((z (x, (x ^ (2 : ℕ)))) = (((x ^ (4 : ℕ)) + (x ^ (4 : ℕ))) + (v_uCF_u86 x))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (1 = ((2 * (x ^ (4 : ℕ))) + (v_uCF_u86 x))))) := by
  sorry

theorem proof_gap_exercise_3358_5
  (z : (ℝ × ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => z (x, t)) y) = ((x ^ (2 : ℕ)) + (2 * y))))))
  (h2 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((z (x, y)) = ((((x ^ (2 : ℕ)) * y) + (y ^ (2 : ℕ))) + (v_uCF_u86 x))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((z (x, (x ^ (2 : ℕ)))) = (((x ^ (4 : ℕ)) + (x ^ (4 : ℕ))) + (v_uCF_u86 x))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (1 = ((2 * (x ^ (4 : ℕ))) + (v_uCF_u86 x))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 x) = (1 - (2 * (x ^ (4 : ℕ))))))) := by
  sorry

theorem proof_gap_exercise_3358_6
  (z : (ℝ × ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => z (x, t)) y) = ((x ^ (2 : ℕ)) + (2 * y))))))
  (h2 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((z (x, y)) = ((((x ^ (2 : ℕ)) * y) + (y ^ (2 : ℕ))) + (v_uCF_u86 x))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((z (x, (x ^ (2 : ℕ)))) = (((x ^ (4 : ℕ)) + (x ^ (4 : ℕ))) + (v_uCF_u86 x))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (1 = ((2 * (x ^ (4 : ℕ))) + (v_uCF_u86 x))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 x) = (1 - (2 * (x ^ (4 : ℕ))))))))
  : (z = (fun (p : ℝ × ℝ) => (((1 + ((p.1 ^ (2 : ℕ)) * p.2)) + (p.2 ^ (2 : ℕ))) - (2 * (p.1 ^ (4 : ℕ)))))) → ((forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => z (x, t)) y) = ((x ^ (2 : ℕ)) + (2 * y))))) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((z (x, (x ^ (2 : ℕ)))) = 1)))) := by
  sorry

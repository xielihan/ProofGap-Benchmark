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

-- exercise: exercise_3359

theorem proof_gap_exercise_3359_1
  (z : (ℝ × ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (v_uCF_u86__1 : (ℝ -> ℝ))
  : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 2 (fun t => z (x, t)) y) = 2))) := by
  sorry

theorem proof_gap_exercise_3359_2
  (z : (ℝ × ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (v_uCF_u86__1 : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 2 (fun t => z (x, t)) y) = 2))))
  : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => z (x, t)) y) = ((2 * y) + (v_uCF_u86 x))))) := by
  sorry

theorem proof_gap_exercise_3359_3
  (z : (ℝ × ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (v_uCF_u86__1 : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 2 (fun t => z (x, t)) y) = 2))))
  (h2 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => z (x, t)) y) = ((2 * y) + (v_uCF_u86 x))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (x = ((2 * 0) + (v_uCF_u86 x))))) := by
  sorry

theorem proof_gap_exercise_3359_4
  (z : (ℝ × ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (v_uCF_u86__1 : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 2 (fun t => z (x, t)) y) = 2))))
  (h2 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => z (x, t)) y) = ((2 * y) + (v_uCF_u86 x))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (x = ((2 * 0) + (v_uCF_u86 x))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 x) = x))) := by
  sorry

theorem proof_gap_exercise_3359_5
  (z : (ℝ × ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (v_uCF_u86__1 : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 2 (fun t => z (x, t)) y) = 2))))
  (h2 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => z (x, t)) y) = ((2 * y) + (v_uCF_u86 x))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (x = ((2 * 0) + (v_uCF_u86 x))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 x) = x))))
  : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => z (x, t)) y) = ((2 * y) + x)))) := by
  sorry

theorem proof_gap_exercise_3359_6
  (z : (ℝ × ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (v_uCF_u86__1 : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 2 (fun t => z (x, t)) y) = 2))))
  (h2 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => z (x, t)) y) = ((2 * y) + (v_uCF_u86 x))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (x = ((2 * 0) + (v_uCF_u86 x))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 x) = x))))
  (h5 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => z (x, t)) y) = ((2 * y) + x)))))
  : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((z (x, y)) = (((y ^ (2 : ℕ)) + (x * y)) + (v_uCF_u86__1 x))))) := by
  sorry

theorem proof_gap_exercise_3359_7
  (z : (ℝ × ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (v_uCF_u86__1 : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 2 (fun t => z (x, t)) y) = 2))))
  (h2 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => z (x, t)) y) = ((2 * y) + (v_uCF_u86 x))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (x = ((2 * 0) + (v_uCF_u86 x))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 x) = x))))
  (h5 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => z (x, t)) y) = ((2 * y) + x)))))
  (h6 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((z (x, y)) = (((y ^ (2 : ℕ)) + (x * y)) + (v_uCF_u86__1 x))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (1 = ((((0 : ℕ) ^ (2 : ℕ)) + (x * 0)) + (v_uCF_u86__1 x))))) := by
  sorry

theorem proof_gap_exercise_3359_8
  (z : (ℝ × ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (v_uCF_u86__1 : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 2 (fun t => z (x, t)) y) = 2))))
  (h2 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => z (x, t)) y) = ((2 * y) + (v_uCF_u86 x))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (x = ((2 * 0) + (v_uCF_u86 x))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 x) = x))))
  (h5 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => z (x, t)) y) = ((2 * y) + x)))))
  (h6 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((z (x, y)) = (((y ^ (2 : ℕ)) + (x * y)) + (v_uCF_u86__1 x))))))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (1 = ((((0 : ℕ) ^ (2 : ℕ)) + (x * 0)) + (v_uCF_u86__1 x))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86__1 x) = 1))) := by
  sorry

theorem proof_gap_exercise_3359_9
  (z : (ℝ × ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (v_uCF_u86__1 : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 2 (fun t => z (x, t)) y) = 2))))
  (h2 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => z (x, t)) y) = ((2 * y) + (v_uCF_u86 x))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (x = ((2 * 0) + (v_uCF_u86 x))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 x) = x))))
  (h5 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => z (x, t)) y) = ((2 * y) + x)))))
  (h6 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((z (x, y)) = (((y ^ (2 : ℕ)) + (x * y)) + (v_uCF_u86__1 x))))))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (1 = ((((0 : ℕ) ^ (2 : ℕ)) + (x * 0)) + (v_uCF_u86__1 x))))))
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86__1 x) = 1))))
  : (z = (fun (p : ℝ × ℝ) => ((1 + (p.1 * p.2)) + (p.2 ^ (2 : ℕ))))) → (((forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 2 (fun t => z (x, t)) y) = 2))) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((z (x, (0 : ℝ))) = 1)))) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => z (x, t)) 0) = x)))) := by
  sorry

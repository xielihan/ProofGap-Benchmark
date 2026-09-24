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

-- exercise: exercise_3338

theorem proof_gap_exercise_3338_1
  (z : (ℝ × ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (v_uCF_u88 : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((z (x, y)) = ((v_uCF_u86 (x + y)) + (v_uCF_u88 (x - y)))))))
  (h2 : ContDiff ℝ (2 : ℕ∞) (fun (x : ℝ) => (v_uCF_u86 x)))
  (h3 : ContDiff ℝ (2 : ℕ∞) (fun (x : ℝ) => (v_uCF_u88 x)))
  : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => (z (t, y))) x) = ((iteratedDeriv 1 (fun t => (v_uCF_u86 t)) (x + y)) + (iteratedDeriv 1 (fun t => (v_uCF_u88 t)) (x - y)))))) := by
  sorry

theorem proof_gap_exercise_3338_2
  (z : (ℝ × ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (v_uCF_u88 : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((z (x, y)) = ((v_uCF_u86 (x + y)) + (v_uCF_u88 (x - y)))))))
  (h2 : ContDiff ℝ (2 : ℕ∞) (fun (x : ℝ) => (v_uCF_u86 x)))
  (h3 : ContDiff ℝ (2 : ℕ∞) (fun (x : ℝ) => (v_uCF_u88 x)))
  (h4 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => (z (t, y))) x) = ((iteratedDeriv 1 (fun t => (v_uCF_u86 t)) (x + y)) + (iteratedDeriv 1 (fun t => (v_uCF_u88 t)) (x - y)))))))
  : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => (z (x, t))) y) = ((iteratedDeriv 1 (fun t => (v_uCF_u86 t)) (x + y)) - (iteratedDeriv 1 (fun t => (v_uCF_u88 t)) (x - y)))))) := by
  sorry

theorem proof_gap_exercise_3338_3
  (z : (ℝ × ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (v_uCF_u88 : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((z (x, y)) = ((v_uCF_u86 (x + y)) + (v_uCF_u88 (x - y)))))))
  (h2 : ContDiff ℝ (2 : ℕ∞) (fun (x : ℝ) => (v_uCF_u86 x)))
  (h3 : ContDiff ℝ (2 : ℕ∞) (fun (x : ℝ) => (v_uCF_u88 x)))
  (h4 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => (z (t, y))) x) = ((iteratedDeriv 1 (fun t => (v_uCF_u86 t)) (x + y)) + (iteratedDeriv 1 (fun t => (v_uCF_u88 t)) (x - y)))))))
  (h5 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => (z (x, t))) y) = ((iteratedDeriv 1 (fun t => (v_uCF_u86 t)) (x + y)) - (iteratedDeriv 1 (fun t => (v_uCF_u88 t)) (x - y)))))))
  : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 2 (fun t => (z (t, y))) x) = ((iteratedDeriv 2 (fun t => (v_uCF_u86 t)) (x + y)) + (iteratedDeriv 2 (fun t => (v_uCF_u88 t)) (x - y)))))) := by
  sorry

theorem proof_gap_exercise_3338_4
  (z : (ℝ × ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (v_uCF_u88 : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((z (x, y)) = ((v_uCF_u86 (x + y)) + (v_uCF_u88 (x - y)))))))
  (h2 : ContDiff ℝ (2 : ℕ∞) (fun (x : ℝ) => (v_uCF_u86 x)))
  (h3 : ContDiff ℝ (2 : ℕ∞) (fun (x : ℝ) => (v_uCF_u88 x)))
  (h4 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => (z (t, y))) x) = ((iteratedDeriv 1 (fun t => (v_uCF_u86 t)) (x + y)) + (iteratedDeriv 1 (fun t => (v_uCF_u88 t)) (x - y)))))))
  (h5 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => (z (x, t))) y) = ((iteratedDeriv 1 (fun t => (v_uCF_u86 t)) (x + y)) - (iteratedDeriv 1 (fun t => (v_uCF_u88 t)) (x - y)))))))
  (h6 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 2 (fun t => (z (t, y))) x) = ((iteratedDeriv 2 (fun t => (v_uCF_u86 t)) (x + y)) + (iteratedDeriv 2 (fun t => (v_uCF_u88 t)) (x - y)))))))
  : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 2 (fun t => (z (x, t))) y) = ((iteratedDeriv 2 (fun t => (v_uCF_u86 t)) (x + y)) + (iteratedDeriv 2 (fun t => (v_uCF_u88 t)) (x - y)))))) := by
  sorry

theorem proof_gap_exercise_3338_5
  (z : (ℝ × ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (v_uCF_u88 : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((z (x, y)) = ((v_uCF_u86 (x + y)) + (v_uCF_u88 (x - y)))))))
  (h2 : ContDiff ℝ (2 : ℕ∞) (fun (x : ℝ) => (v_uCF_u86 x)))
  (h3 : ContDiff ℝ (2 : ℕ∞) (fun (x : ℝ) => (v_uCF_u88 x)))
  (h4 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => (z (t, y))) x) = ((iteratedDeriv 1 (fun t => (v_uCF_u86 t)) (x + y)) + (iteratedDeriv 1 (fun t => (v_uCF_u88 t)) (x - y)))))))
  (h5 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => (z (x, t))) y) = ((iteratedDeriv 1 (fun t => (v_uCF_u86 t)) (x + y)) - (iteratedDeriv 1 (fun t => (v_uCF_u88 t)) (x - y)))))))
  (h6 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 2 (fun t => (z (t, y))) x) = ((iteratedDeriv 2 (fun t => (v_uCF_u86 t)) (x + y)) + (iteratedDeriv 2 (fun t => (v_uCF_u88 t)) (x - y)))))))
  (h7 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 2 (fun t => (z (x, t))) y) = ((iteratedDeriv 2 (fun t => (v_uCF_u86 t)) (x + y)) + (iteratedDeriv 2 (fun t => (v_uCF_u88 t)) (x - y)))))))
  : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 2 (fun t => (z (t, y))) x) = (iteratedDeriv 2 (fun t => (z (x, t))) y)))) := by
  sorry

theorem proof_gap_exercise_3338_6
  (z : (ℝ × ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (v_uCF_u88 : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((z (x, y)) = ((v_uCF_u86 (x + y)) + (v_uCF_u88 (x - y)))))))
  (h2 : ContDiff ℝ (2 : ℕ∞) (fun (x : ℝ) => (v_uCF_u86 x)))
  (h3 : ContDiff ℝ (2 : ℕ∞) (fun (x : ℝ) => (v_uCF_u88 x)))
  (h4 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => (z (t, y))) x) = ((iteratedDeriv 1 (fun t => (v_uCF_u86 t)) (x + y)) + (iteratedDeriv 1 (fun t => (v_uCF_u88 t)) (x - y)))))))
  (h5 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => (z (x, t))) y) = ((iteratedDeriv 1 (fun t => (v_uCF_u86 t)) (x + y)) - (iteratedDeriv 1 (fun t => (v_uCF_u88 t)) (x - y)))))))
  (h6 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 2 (fun t => (z (t, y))) x) = ((iteratedDeriv 2 (fun t => (v_uCF_u86 t)) (x + y)) + (iteratedDeriv 2 (fun t => (v_uCF_u88 t)) (x - y)))))))
  (h7 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 2 (fun t => (z (x, t))) y) = ((iteratedDeriv 2 (fun t => (v_uCF_u86 t)) (x + y)) + (iteratedDeriv 2 (fun t => (v_uCF_u88 t)) (x - y)))))))
  (h8 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 2 (fun t => (z (t, y))) x) = (iteratedDeriv 2 (fun t => (z (x, t))) y)))))
  : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 2 (fun t => (z (t, y))) x) = (iteratedDeriv 2 (fun t => (z (x, t))) y)))) := by
  sorry

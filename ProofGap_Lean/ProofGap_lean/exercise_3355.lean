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

-- exercise: exercise_3355

theorem proof_gap_exercise_3355_1
  (z : (ℝ × ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (v_uCF_u88 : (ℝ -> ℝ))
  : (exists (v_uCF_u88__1 : (ℝ -> ℝ)), (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => z (t, y)) x) = (v_uCF_u88__1 x))))) := by
  sorry

theorem proof_gap_exercise_3355_2
  (z : (ℝ × ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (v_uCF_u88 : (ℝ -> ℝ))
  (h1 : (exists (v_uCF_u88__1 : (ℝ -> ℝ)), (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t_1 => z (t_1, y)) x) = (v_uCF_u88__1 x))))))
  : (exists (v_uCF_u86__1 : (ℝ -> ℝ)), (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((z (x, y)) = ((∫ t in (0 : ℝ)..x, ((v_uCF_u86__1 t) * (1 : ℝ))) + (v_uCF_u88 y)))))) := by
  sorry

theorem proof_gap_exercise_3355_3
  (z : (ℝ × ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (v_uCF_u88 : (ℝ -> ℝ))
  (h1 : (exists (v_uCF_u88__1 : (ℝ -> ℝ)), (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t_1 => z (t_1, y)) x) = (v_uCF_u88__1 x))))))
  (h2 : (exists (v_uCF_u86__1 : (ℝ -> ℝ)), (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((z (x, y)) = ((∫ t in (0 : ℝ)..x, ((v_uCF_u86__1 t) * (1 : ℝ))) + (v_uCF_u88 y)))))))
  : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((z (x, y)) = ((v_uCF_u86 x) + (v_uCF_u88 y))))) := by
  sorry

theorem proof_gap_exercise_3355_4
  (z : (ℝ × ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (v_uCF_u88 : (ℝ -> ℝ))
  (h1 : (exists (v_uCF_u88__1 : (ℝ -> ℝ)), (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t_1 => z (t_1, y)) x) = (v_uCF_u88__1 x))))))
  (h2 : (exists (v_uCF_u86__1 : (ℝ -> ℝ)), (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((z (x, y)) = ((∫ t in (0 : ℝ)..x, ((v_uCF_u86__1 t) * (1 : ℝ))) + (v_uCF_u88 y)))))))
  (h3 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((z (x, y)) = ((v_uCF_u86 x) + (v_uCF_u88 y))))))
  : (z = (fun (p : ℝ × ℝ) => ((v_uCF_u86 p.1) + (v_uCF_u88 p.2)))) → (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t_1 => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t_1 => z (t_1, p.2)) p.1)) (x, t_1)) y) = 0))) := by
  sorry

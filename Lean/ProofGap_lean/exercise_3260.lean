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

-- exercise: exercise_3260

theorem proof_gap_exercise_3260_1
  (u : (ℝ × (ℝ × ℝ) -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((u (x, (y, z))) = (Real.exp ((x * y) * z))))))
  : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => u (t, (y, z))) x) = ((y * z) * (Real.exp ((x * y) * z)))))) := by
  sorry

theorem proof_gap_exercise_3260_2
  (u : (ℝ × (ℝ × ℝ) -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((u (x, (y, z))) = (Real.exp ((x * y) * z))))))
  (h2 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => u (t, (y, z))) x) = ((y * z) * (Real.exp ((x * y) * z)))))))
  : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => (fun (p : ℝ × (ℝ × ℝ)) => (iteratedDeriv 1 (fun t => u (t, (p.2.1, p.2.2))) p.1)) (x, (t, z))) y) = ((z * (Real.exp ((x * y) * z))) + (((x * y) * (z ^ (2 : ℕ))) * (Real.exp ((x * y) * z))))))) := by
  sorry

theorem proof_gap_exercise_3260_3
  (u : (ℝ × (ℝ × ℝ) -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((u (x, (y, z))) = (Real.exp ((x * y) * z))))))
  (h2 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => u (t, (y, z))) x) = ((y * z) * (Real.exp ((x * y) * z)))))))
  (h3 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => (fun (p : ℝ × (ℝ × ℝ)) => (iteratedDeriv 1 (fun t => u (t, (p.2.1, p.2.2))) p.1)) (x, (t, z))) y) = ((z * (Real.exp ((x * y) * z))) + (((x * y) * (z ^ (2 : ℕ))) * (Real.exp ((x * y) * z))))))))
  : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => (fun (p : ℝ × (ℝ × ℝ)) => (iteratedDeriv 1 (fun t => (fun (p : ℝ × (ℝ × ℝ)) => (iteratedDeriv 1 (fun t => u (t, (p.2.1, p.2.2))) p.1)) (p.1, (t, p.2.2))) p.2.1)) (x, (y, t))) z) = ((((Real.exp ((x * y) * z)) + (((x * y) * z) * (Real.exp ((x * y) * z)))) + ((((2 * x) * y) * z) * (Real.exp ((x * y) * z)))) + ((((x ^ (2 : ℕ)) * (y ^ (2 : ℕ))) * (z ^ (2 : ℕ))) * (Real.exp ((x * y) * z))))))) := by
  sorry

theorem proof_gap_exercise_3260_4
  (u : (ℝ × (ℝ × ℝ) -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((u (x, (y, z))) = (Real.exp ((x * y) * z))))))
  (h2 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => u (t, (y, z))) x) = ((y * z) * (Real.exp ((x * y) * z)))))))
  (h3 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => (fun (p : ℝ × (ℝ × ℝ)) => (iteratedDeriv 1 (fun t => u (t, (p.2.1, p.2.2))) p.1)) (x, (t, z))) y) = ((z * (Real.exp ((x * y) * z))) + (((x * y) * (z ^ (2 : ℕ))) * (Real.exp ((x * y) * z))))))))
  (h4 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => (fun (p : ℝ × (ℝ × ℝ)) => (iteratedDeriv 1 (fun t => (fun (p : ℝ × (ℝ × ℝ)) => (iteratedDeriv 1 (fun t => u (t, (p.2.1, p.2.2))) p.1)) (p.1, (t, p.2.2))) p.2.1)) (x, (y, t))) z) = ((((Real.exp ((x * y) * z)) + (((x * y) * z) * (Real.exp ((x * y) * z)))) + ((((2 * x) * y) * z) * (Real.exp ((x * y) * z)))) + ((((x ^ (2 : ℕ)) * (y ^ (2 : ℕ))) * (z ^ (2 : ℕ))) * (Real.exp ((x * y) * z))))))))
  : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → (((((Real.exp ((x * y) * z)) + (((x * y) * z) * (Real.exp ((x * y) * z)))) + ((((2 * x) * y) * z) * (Real.exp ((x * y) * z)))) + ((((x ^ (2 : ℕ)) * (y ^ (2 : ℕ))) * (z ^ (2 : ℕ))) * (Real.exp ((x * y) * z)))) = ((Real.exp ((x * y) * z)) * ((1 + (((3 * x) * y) * z)) + (((x ^ (2 : ℕ)) * (y ^ (2 : ℕ))) * (z ^ (2 : ℕ)))))))) := by
  sorry

theorem proof_gap_exercise_3260_5
  (u : (ℝ × (ℝ × ℝ) -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((u (x, (y, z))) = (Real.exp ((x * y) * z))))))
  (h2 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => u (t, (y, z))) x) = ((y * z) * (Real.exp ((x * y) * z)))))))
  (h3 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => (fun (p : ℝ × (ℝ × ℝ)) => (iteratedDeriv 1 (fun t => u (t, (p.2.1, p.2.2))) p.1)) (x, (t, z))) y) = ((z * (Real.exp ((x * y) * z))) + (((x * y) * (z ^ (2 : ℕ))) * (Real.exp ((x * y) * z))))))))
  (h4 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => (fun (p : ℝ × (ℝ × ℝ)) => (iteratedDeriv 1 (fun t => (fun (p : ℝ × (ℝ × ℝ)) => (iteratedDeriv 1 (fun t => u (t, (p.2.1, p.2.2))) p.1)) (p.1, (t, p.2.2))) p.2.1)) (x, (y, t))) z) = ((((Real.exp ((x * y) * z)) + (((x * y) * z) * (Real.exp ((x * y) * z)))) + ((((2 * x) * y) * z) * (Real.exp ((x * y) * z)))) + ((((x ^ (2 : ℕ)) * (y ^ (2 : ℕ))) * (z ^ (2 : ℕ))) * (Real.exp ((x * y) * z))))))))
  (h5 : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → (((((Real.exp ((x * y) * z)) + (((x * y) * z) * (Real.exp ((x * y) * z)))) + ((((2 * x) * y) * z) * (Real.exp ((x * y) * z)))) + ((((x ^ (2 : ℕ)) * (y ^ (2 : ℕ))) * (z ^ (2 : ℕ))) * (Real.exp ((x * y) * z)))) = ((Real.exp ((x * y) * z)) * ((1 + (((3 * x) * y) * z)) + (((x ^ (2 : ℕ)) * (y ^ (2 : ℕ))) * (z ^ (2 : ℕ)))))))))
  : (forall (x : ℝ) (y : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => (fun (p : ℝ × (ℝ × ℝ)) => (iteratedDeriv 1 (fun t => (fun (p : ℝ × (ℝ × ℝ)) => (iteratedDeriv 1 (fun t => u (t, (p.2.1, p.2.2))) p.1)) (p.1, (t, p.2.2))) p.2.1)) (x, (y, t))) z) = ((Real.exp ((x * y) * z)) * ((1 + (((3 * x) * y) * z)) + (((x ^ (2 : ℕ)) * (y ^ (2 : ℕ))) * (z ^ (2 : ℕ)))))))) := by
  sorry

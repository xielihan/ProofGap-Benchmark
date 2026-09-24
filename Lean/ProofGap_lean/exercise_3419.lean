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

-- exercise: exercise_3419

theorem proof_gap_exercise_3419_1
  (z : (ℝ × ℝ -> ℝ))
  (f : (ℝ × (ℝ × (ℝ × ℝ)) -> ℝ))
  (g : (ℝ × (ℝ × (ℝ × ℝ)) -> ℝ))
  (t : ℝ)
  (I_1 : ℝ)
  (I_2 : ℝ)
  (I_3 : ℝ)
  (h1 : t ∈ (Set.univ : Set ℝ))
  (h2 : I_1 ∈ (Set.univ : Set ℝ))
  (h3 : I_2 ∈ (Set.univ : Set ℝ))
  (h4 : I_3 ∈ (Set.univ : Set ℝ))
  (h5 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((f (x, (y, ((z (x, y)), t)))) = 0))))
  (h6 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((g (x, (y, ((z (x, y)), t)))) = 0))))
  (h7 : Differentiable ℝ f)
  (h8 : Differentiable ℝ g)
  (h9 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (I_1 = (((iteratedDeriv 1 (fun t_1 => f (t_1, (y, ((z (x, y)), t)))) x) * (iteratedDeriv 1 (fun t_1 => g (x, (y, ((z (x, y)), t_1)))) t)) - ((iteratedDeriv 1 (fun t_1 => f (x, (y, ((z (x, y)), t_1)))) t) * (iteratedDeriv 1 (fun t_1 => g (t_1, (y, ((z (x, y)), t)))) x)))))))
  (h10 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (I_2 = (((iteratedDeriv 1 (fun t_1 => f (x, (t_1, ((z (x, y)), t)))) y) * (iteratedDeriv 1 (fun t_1 => g (x, (y, ((z (x, y)), t_1)))) t)) - ((iteratedDeriv 1 (fun t_1 => f (x, (y, ((z (x, y)), t_1)))) t) * (iteratedDeriv 1 (fun t_1 => g (x, (t_1, ((z (x, y)), t)))) y)))))))
  (h11 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (I_3 = (((iteratedDeriv 1 (fun t_1 => f (x, (y, (t_1, t)))) (z (x, y))) * (iteratedDeriv 1 (fun t_1 => g (x, (y, ((z (x, y)), t_1)))) t)) - ((iteratedDeriv 1 (fun t_1 => f (x, (y, ((z (x, y)), t_1)))) t) * (iteratedDeriv 1 (fun t_1 => g (x, (y, (t_1, t)))) (z (x, y)))))))))
  (h12 : I_3 ≠ 0)
  : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (((fun p : (ℝ × ℝ) => ((((iteratedDeriv 1 (fun t_1 => f (t_1, (y, ((z (x, y)), t)))) x) • (fderiv ℝ (fun q : (ℝ × ℝ) => q.1) p)) + ((iteratedDeriv 1 (fun t_1 => f (x, (t_1, ((z (x, y)), t)))) y) • (fderiv ℝ (fun q : (ℝ × ℝ) => q.2) p))) + ((iteratedDeriv 1 (fun t_1 => f (x, (y, (t_1, t)))) (z (x, y))) • (fderiv ℝ (fun q : (ℝ × ℝ) => (z (q.1, q.2))) p)))) + ((iteratedDeriv 1 (fun t_1 => f (x, (y, ((z (x, y)), t_1)))) t) • (fderiv ℝ (fun (t_1 : ℝ) => t_1)))) = 0))) := by
  sorry

theorem proof_gap_exercise_3419_2
  (z : (ℝ × ℝ -> ℝ))
  (f : (ℝ × (ℝ × (ℝ × ℝ)) -> ℝ))
  (g : (ℝ × (ℝ × (ℝ × ℝ)) -> ℝ))
  (t : ℝ)
  (I_1 : ℝ)
  (I_2 : ℝ)
  (I_3 : ℝ)
  (h1 : t ∈ (Set.univ : Set ℝ))
  (h2 : I_1 ∈ (Set.univ : Set ℝ))
  (h3 : I_2 ∈ (Set.univ : Set ℝ))
  (h4 : I_3 ∈ (Set.univ : Set ℝ))
  (h5 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((f (x, (y, ((z (x, y)), t)))) = 0))))
  (h6 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((g (x, (y, ((z (x, y)), t)))) = 0))))
  (h7 : Differentiable ℝ f)
  (h8 : Differentiable ℝ g)
  (h9 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (I_1 = (((iteratedDeriv 1 (fun t_1 => f (t_1, (y, ((z (x, y)), t)))) x) * (iteratedDeriv 1 (fun t_1 => g (x, (y, ((z (x, y)), t_1)))) t)) - ((iteratedDeriv 1 (fun t_1 => f (x, (y, ((z (x, y)), t_1)))) t) * (iteratedDeriv 1 (fun t_1 => g (t_1, (y, ((z (x, y)), t)))) x)))))))
  (h10 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (I_2 = (((iteratedDeriv 1 (fun t_1 => f (x, (t_1, ((z (x, y)), t)))) y) * (iteratedDeriv 1 (fun t_1 => g (x, (y, ((z (x, y)), t_1)))) t)) - ((iteratedDeriv 1 (fun t_1 => f (x, (y, ((z (x, y)), t_1)))) t) * (iteratedDeriv 1 (fun t_1 => g (x, (t_1, ((z (x, y)), t)))) y)))))))
  (h11 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (I_3 = (((iteratedDeriv 1 (fun t_1 => f (x, (y, (t_1, t)))) (z (x, y))) * (iteratedDeriv 1 (fun t_1 => g (x, (y, ((z (x, y)), t_1)))) t)) - ((iteratedDeriv 1 (fun t_1 => f (x, (y, ((z (x, y)), t_1)))) t) * (iteratedDeriv 1 (fun t_1 => g (x, (y, (t_1, t)))) (z (x, y)))))))))
  (h12 : I_3 ≠ 0)
  (h13 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (((fun p : (ℝ × ℝ) => ((((iteratedDeriv 1 (fun t_1 => f (t_1, (y, ((z (x, y)), t)))) x) • (fderiv ℝ (fun q : (ℝ × ℝ) => q.1) p)) + ((iteratedDeriv 1 (fun t_1 => f (x, (t_1, ((z (x, y)), t)))) y) • (fderiv ℝ (fun q : (ℝ × ℝ) => q.2) p))) + ((iteratedDeriv 1 (fun t_1 => f (x, (y, (t_1, t)))) (z (x, y))) • (fderiv ℝ (fun q : (ℝ × ℝ) => (z (q.1, q.2))) p)))) + ((iteratedDeriv 1 (fun t_1 => f (x, (y, ((z (x, y)), t_1)))) t) • (fderiv ℝ (fun (t_1 : ℝ) => t_1)))) = 0))))
  : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (((fun p : (ℝ × ℝ) => ((((iteratedDeriv 1 (fun t_1 => g (t_1, (y, ((z (x, y)), t)))) x) • (fderiv ℝ (fun q : (ℝ × ℝ) => q.1) p)) + ((iteratedDeriv 1 (fun t_1 => g (x, (t_1, ((z (x, y)), t)))) y) • (fderiv ℝ (fun q : (ℝ × ℝ) => q.2) p))) + ((iteratedDeriv 1 (fun t_1 => g (x, (y, (t_1, t)))) (z (x, y))) • (fderiv ℝ (fun q : (ℝ × ℝ) => (z (q.1, q.2))) p)))) + ((iteratedDeriv 1 (fun t_1 => g (x, (y, ((z (x, y)), t_1)))) t) • (fderiv ℝ (fun (t_1 : ℝ) => t_1)))) = 0))) := by
  sorry

theorem proof_gap_exercise_3419_3
  (z : (ℝ × ℝ -> ℝ))
  (f : (ℝ × (ℝ × (ℝ × ℝ)) -> ℝ))
  (g : (ℝ × (ℝ × (ℝ × ℝ)) -> ℝ))
  (t : ℝ)
  (I_1 : ℝ)
  (I_2 : ℝ)
  (I_3 : ℝ)
  (h1 : t ∈ (Set.univ : Set ℝ))
  (h2 : I_1 ∈ (Set.univ : Set ℝ))
  (h3 : I_2 ∈ (Set.univ : Set ℝ))
  (h4 : I_3 ∈ (Set.univ : Set ℝ))
  (h5 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((f (x, (y, ((z (x, y)), t)))) = 0))))
  (h6 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((g (x, (y, ((z (x, y)), t)))) = 0))))
  (h7 : Differentiable ℝ f)
  (h8 : Differentiable ℝ g)
  (h9 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (I_1 = (((iteratedDeriv 1 (fun t_1 => f (t_1, (y, ((z (x, y)), t)))) x) * (iteratedDeriv 1 (fun t_1 => g (x, (y, ((z (x, y)), t_1)))) t)) - ((iteratedDeriv 1 (fun t_1 => f (x, (y, ((z (x, y)), t_1)))) t) * (iteratedDeriv 1 (fun t_1 => g (t_1, (y, ((z (x, y)), t)))) x)))))))
  (h10 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (I_2 = (((iteratedDeriv 1 (fun t_1 => f (x, (t_1, ((z (x, y)), t)))) y) * (iteratedDeriv 1 (fun t_1 => g (x, (y, ((z (x, y)), t_1)))) t)) - ((iteratedDeriv 1 (fun t_1 => f (x, (y, ((z (x, y)), t_1)))) t) * (iteratedDeriv 1 (fun t_1 => g (x, (t_1, ((z (x, y)), t)))) y)))))))
  (h11 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (I_3 = (((iteratedDeriv 1 (fun t_1 => f (x, (y, (t_1, t)))) (z (x, y))) * (iteratedDeriv 1 (fun t_1 => g (x, (y, ((z (x, y)), t_1)))) t)) - ((iteratedDeriv 1 (fun t_1 => f (x, (y, ((z (x, y)), t_1)))) t) * (iteratedDeriv 1 (fun t_1 => g (x, (y, (t_1, t)))) (z (x, y)))))))))
  (h12 : I_3 ≠ 0)
  (h13 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (((fun p : (ℝ × ℝ) => ((((iteratedDeriv 1 (fun t_1 => f (t_1, (y, ((z (x, y)), t)))) x) • (fderiv ℝ (fun q : (ℝ × ℝ) => q.1) p)) + ((iteratedDeriv 1 (fun t_1 => f (x, (t_1, ((z (x, y)), t)))) y) • (fderiv ℝ (fun q : (ℝ × ℝ) => q.2) p))) + ((iteratedDeriv 1 (fun t_1 => f (x, (y, (t_1, t)))) (z (x, y))) • (fderiv ℝ (fun q : (ℝ × ℝ) => (z (q.1, q.2))) p)))) + ((iteratedDeriv 1 (fun t_1 => f (x, (y, ((z (x, y)), t_1)))) t) • (fderiv ℝ (fun (t_1 : ℝ) => t_1)))) = 0))))
  (h14 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (((fun p : (ℝ × ℝ) => ((((iteratedDeriv 1 (fun t_1 => g (t_1, (y, ((z (x, y)), t)))) x) • (fderiv ℝ (fun q : (ℝ × ℝ) => q.1) p)) + ((iteratedDeriv 1 (fun t_1 => g (x, (t_1, ((z (x, y)), t)))) y) • (fderiv ℝ (fun q : (ℝ × ℝ) => q.2) p))) + ((iteratedDeriv 1 (fun t_1 => g (x, (y, (t_1, t)))) (z (x, y))) • (fderiv ℝ (fun q : (ℝ × ℝ) => (z (q.1, q.2))) p)))) + ((iteratedDeriv 1 (fun t_1 => g (x, (y, ((z (x, y)), t_1)))) t) • (fderiv ℝ (fun (t_1 : ℝ) => t_1)))) = 0))))
  : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((fun p : (ℝ × ℝ) => (fderiv ℝ (fun q : (ℝ × ℝ) => (z (q.1, q.2))) p)) = ((((iteratedDeriv 1 (fun t_1 => f (x, (y, ((z (x, y)), t_1)))) t) * (fun p : (ℝ × ℝ) => (((iteratedDeriv 1 (fun t_1 => g (t_1, (y, ((z (x, y)), t)))) x) • (fderiv ℝ (fun q : (ℝ × ℝ) => q.1) p)) + ((iteratedDeriv 1 (fun t_1 => g (x, (t_1, ((z (x, y)), t)))) y) • (fderiv ℝ (fun q : (ℝ × ℝ) => q.2) p))))) - ((iteratedDeriv 1 (fun t_1 => g (x, (y, ((z (x, y)), t_1)))) t) * (fun p : (ℝ × ℝ) => (((iteratedDeriv 1 (fun t_1 => f (t_1, (y, ((z (x, y)), t)))) x) • (fderiv ℝ (fun q : (ℝ × ℝ) => q.1) p)) + ((iteratedDeriv 1 (fun t_1 => f (x, (t_1, ((z (x, y)), t)))) y) • (fderiv ℝ (fun q : (ℝ × ℝ) => q.2) p)))))) /. I_3)))) := by
  sorry

theorem proof_gap_exercise_3419_4
  (z : (ℝ × ℝ -> ℝ))
  (f : (ℝ × (ℝ × (ℝ × ℝ)) -> ℝ))
  (g : (ℝ × (ℝ × (ℝ × ℝ)) -> ℝ))
  (t : ℝ)
  (I_1 : ℝ)
  (I_2 : ℝ)
  (I_3 : ℝ)
  (h1 : t ∈ (Set.univ : Set ℝ))
  (h2 : I_1 ∈ (Set.univ : Set ℝ))
  (h3 : I_2 ∈ (Set.univ : Set ℝ))
  (h4 : I_3 ∈ (Set.univ : Set ℝ))
  (h5 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((f (x, (y, ((z (x, y)), t)))) = 0))))
  (h6 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((g (x, (y, ((z (x, y)), t)))) = 0))))
  (h7 : Differentiable ℝ f)
  (h8 : Differentiable ℝ g)
  (h9 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (I_1 = (((iteratedDeriv 1 (fun t_1 => f (t_1, (y, ((z (x, y)), t)))) x) * (iteratedDeriv 1 (fun t_1 => g (x, (y, ((z (x, y)), t_1)))) t)) - ((iteratedDeriv 1 (fun t_1 => f (x, (y, ((z (x, y)), t_1)))) t) * (iteratedDeriv 1 (fun t_1 => g (t_1, (y, ((z (x, y)), t)))) x)))))))
  (h10 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (I_2 = (((iteratedDeriv 1 (fun t_1 => f (x, (t_1, ((z (x, y)), t)))) y) * (iteratedDeriv 1 (fun t_1 => g (x, (y, ((z (x, y)), t_1)))) t)) - ((iteratedDeriv 1 (fun t_1 => f (x, (y, ((z (x, y)), t_1)))) t) * (iteratedDeriv 1 (fun t_1 => g (x, (t_1, ((z (x, y)), t)))) y)))))))
  (h11 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (I_3 = (((iteratedDeriv 1 (fun t_1 => f (x, (y, (t_1, t)))) (z (x, y))) * (iteratedDeriv 1 (fun t_1 => g (x, (y, ((z (x, y)), t_1)))) t)) - ((iteratedDeriv 1 (fun t_1 => f (x, (y, ((z (x, y)), t_1)))) t) * (iteratedDeriv 1 (fun t_1 => g (x, (y, (t_1, t)))) (z (x, y)))))))))
  (h12 : I_3 ≠ 0)
  (h13 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (((fun p : (ℝ × ℝ) => ((((iteratedDeriv 1 (fun t_1 => f (t_1, (y, ((z (x, y)), t)))) x) • (fderiv ℝ (fun q : (ℝ × ℝ) => q.1) p)) + ((iteratedDeriv 1 (fun t_1 => f (x, (t_1, ((z (x, y)), t)))) y) • (fderiv ℝ (fun q : (ℝ × ℝ) => q.2) p))) + ((iteratedDeriv 1 (fun t_1 => f (x, (y, (t_1, t)))) (z (x, y))) • (fderiv ℝ (fun q : (ℝ × ℝ) => (z (q.1, q.2))) p)))) + ((iteratedDeriv 1 (fun t_1 => f (x, (y, ((z (x, y)), t_1)))) t) • (fderiv ℝ (fun (t_1 : ℝ) => t_1)))) = 0))))
  (h14 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → (((fun p : (ℝ × ℝ) => ((((iteratedDeriv 1 (fun t_1 => g (t_1, (y, ((z (x, y)), t)))) x) • (fderiv ℝ (fun q : (ℝ × ℝ) => q.1) p)) + ((iteratedDeriv 1 (fun t_1 => g (x, (t_1, ((z (x, y)), t)))) y) • (fderiv ℝ (fun q : (ℝ × ℝ) => q.2) p))) + ((iteratedDeriv 1 (fun t_1 => g (x, (y, (t_1, t)))) (z (x, y))) • (fderiv ℝ (fun q : (ℝ × ℝ) => (z (q.1, q.2))) p)))) + ((iteratedDeriv 1 (fun t_1 => g (x, (y, ((z (x, y)), t_1)))) t) • (fderiv ℝ (fun (t_1 : ℝ) => t_1)))) = 0))))
  (h15 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((fun p : (ℝ × ℝ) => (fderiv ℝ (fun q : (ℝ × ℝ) => (z (q.1, q.2))) p)) = ((((iteratedDeriv 1 (fun t_1 => f (x, (y, ((z (x, y)), t_1)))) t) * (fun p : (ℝ × ℝ) => (((iteratedDeriv 1 (fun t_1 => g (t_1, (y, ((z (x, y)), t)))) x) • (fderiv ℝ (fun q : (ℝ × ℝ) => q.1) p)) + ((iteratedDeriv 1 (fun t_1 => g (x, (t_1, ((z (x, y)), t)))) y) • (fderiv ℝ (fun q : (ℝ × ℝ) => q.2) p))))) - ((iteratedDeriv 1 (fun t_1 => g (x, (y, ((z (x, y)), t_1)))) t) * (fun p : (ℝ × ℝ) => (((iteratedDeriv 1 (fun t_1 => f (t_1, (y, ((z (x, y)), t)))) x) • (fderiv ℝ (fun q : (ℝ × ℝ) => q.1) p)) + ((iteratedDeriv 1 (fun t_1 => f (x, (t_1, ((z (x, y)), t)))) y) • (fderiv ℝ (fun q : (ℝ × ℝ) => q.2) p)))))) /. I_3)))))
  : (fun p : (ℝ × ℝ) => (fderiv ℝ (fun q : (ℝ × ℝ) => (z (q.1, q.2))) p)) = (-(fun p : (ℝ × ℝ) => ((I_3)⁻¹ • ((I_1 • (fderiv ℝ (fun q : (ℝ × ℝ) => q.1) p)) + (I_2 • (fderiv ℝ (fun q : (ℝ × ℝ) => q.2) p)))))) := by
  sorry

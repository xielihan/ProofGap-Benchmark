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

-- exercise: exercise_1255

theorem proof_gap_exercise_1255_1
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : a < b)
  (h4 : DifferentiableOn ℝ f (Set.Ioo a b))
  (h5 : Bornology.IsBounded ((fun (x1 : ℝ) => (iteratedDeriv 1 (fun t => f t) x1)) '' (Set.Ioo a b)))
  : (exists (M : ℝ), (((M ∈ (Set.univ : Set ℝ)) ∧ (M > 0)) ∧ (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo a b))) → (|((iteratedDeriv 1 (fun t => f t) x))| ≤ M))))) := by
  sorry

theorem proof_gap_exercise_1255_2
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : a < b)
  (h4 : DifferentiableOn ℝ f (Set.Ioo a b))
  (h5 : Bornology.IsBounded ((fun (x1 : ℝ) => (iteratedDeriv 1 (fun t => f t) x1)) '' (Set.Ioo a b)))
  (h6 : (exists (M : ℝ), (((M ∈ (Set.univ : Set ℝ)) ∧ (M > 0)) ∧ (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo a b))) → (|((iteratedDeriv 1 (fun t => f t) x))| ≤ M))))))
  : (forall (M : ℝ), (((M ∈ (Set.univ : Set ℝ)) ∧ (M > 0)) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 = (v_uCE_uB5 /. M))) ∧ (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioo a b))) ∧ (x_2 ∈ (Set.Ioo a b))) ∧ (|((x_1 - x_2))| < v_uCE_uB4)) → (exists (v_uCE_uBE : ℝ), (((v_uCE_uBE ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uBE ∈ (Set.Ioo a b))) ∧ (|(((f x_1) - (f x_2)))| = (|((x_1 - x_2))| * |((iteratedDeriv 1 (fun t => f t) v_uCE_uBE))|)))))))))))))) := by
  sorry

theorem proof_gap_exercise_1255_3
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : a < b)
  (h4 : DifferentiableOn ℝ f (Set.Ioo a b))
  (h5 : Bornology.IsBounded ((fun (x1 : ℝ) => (iteratedDeriv 1 (fun t => f t) x1)) '' (Set.Ioo a b)))
  (h6 : (exists (M : ℝ), (((M ∈ (Set.univ : Set ℝ)) ∧ (M > 0)) ∧ (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo a b))) → (|((iteratedDeriv 1 (fun t => f t) x))| ≤ M))))))
  (h7 : (forall (M : ℝ), (((M ∈ (Set.univ : Set ℝ)) ∧ (M > 0)) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 = (v_uCE_uB5 /. M))) ∧ (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioo a b))) ∧ (x_2 ∈ (Set.Ioo a b))) ∧ (|((x_1 - x_2))| < v_uCE_uB4)) → (exists (v_uCE_uBE : ℝ), (((v_uCE_uBE ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uBE ∈ (Set.Ioo a b))) ∧ (|(((f x_1) - (f x_2)))| = (|((x_1 - x_2))| * |((iteratedDeriv 1 (fun t => f t) v_uCE_uBE))|)))))))))))))))
  : (forall (M : ℝ), (((M ∈ (Set.univ : Set ℝ)) ∧ (M > 0)) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 = (v_uCE_uB5 /. M))) ∧ (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioo a b))) ∧ (x_2 ∈ (Set.Ioo a b))) ∧ (|((x_1 - x_2))| < v_uCE_uB4)) → (|(((f x_1) - (f x_2)))| ≤ (M * |((x_1 - x_2))|)))))))))))) := by
  sorry

theorem proof_gap_exercise_1255_4
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : a < b)
  (h4 : DifferentiableOn ℝ f (Set.Ioo a b))
  (h5 : Bornology.IsBounded ((fun (x1 : ℝ) => (iteratedDeriv 1 (fun t => f t) x1)) '' (Set.Ioo a b)))
  (h6 : (exists (M : ℝ), (((M ∈ (Set.univ : Set ℝ)) ∧ (M > 0)) ∧ (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo a b))) → (|((iteratedDeriv 1 (fun t => f t) x))| ≤ M))))))
  (h7 : (forall (M : ℝ), (((M ∈ (Set.univ : Set ℝ)) ∧ (M > 0)) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 = (v_uCE_uB5 /. M))) ∧ (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioo a b))) ∧ (x_2 ∈ (Set.Ioo a b))) ∧ (|((x_1 - x_2))| < v_uCE_uB4)) → (exists (v_uCE_uBE : ℝ), (((v_uCE_uBE ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uBE ∈ (Set.Ioo a b))) ∧ (|(((f x_1) - (f x_2)))| = (|((x_1 - x_2))| * |((iteratedDeriv 1 (fun t => f t) v_uCE_uBE))|)))))))))))))))
  : (forall (M : ℝ), (((M ∈ (Set.univ : Set ℝ)) ∧ (M > 0)) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 = (v_uCE_uB5 /. M))) ∧ (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioo a b))) ∧ (x_2 ∈ (Set.Ioo a b))) ∧ (|((x_1 - x_2))| < v_uCE_uB4)) → ((M * |((x_1 - x_2))|) < v_uCE_uB5))))))))))) := by
  sorry

theorem proof_gap_exercise_1255_5
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : a < b)
  (h4 : DifferentiableOn ℝ f (Set.Ioo a b))
  (h5 : Bornology.IsBounded ((fun (x1 : ℝ) => (iteratedDeriv 1 (fun t => f t) x1)) '' (Set.Ioo a b)))
  (h6 : (exists (M : ℝ), (((M ∈ (Set.univ : Set ℝ)) ∧ (M > 0)) ∧ (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo a b))) → (|((iteratedDeriv 1 (fun t => f t) x))| ≤ M))))))
  (h7 : (forall (M : ℝ), (((M ∈ (Set.univ : Set ℝ)) ∧ (M > 0)) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 = (v_uCE_uB5 /. M))) ∧ (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioo a b))) ∧ (x_2 ∈ (Set.Ioo a b))) ∧ (|((x_1 - x_2))| < v_uCE_uB4)) → (exists (v_uCE_uBE : ℝ), (((v_uCE_uBE ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uBE ∈ (Set.Ioo a b))) ∧ (|(((f x_1) - (f x_2)))| = (|((x_1 - x_2))| * |((iteratedDeriv 1 (fun t => f t) v_uCE_uBE))|)))))))))))))))
  (h8 : (forall (M : ℝ), (((M ∈ (Set.univ : Set ℝ)) ∧ (M > 0)) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 = (v_uCE_uB5 /. M))) ∧ (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioo a b))) ∧ (x_2 ∈ (Set.Ioo a b))) ∧ (|((x_1 - x_2))| < v_uCE_uB4)) → (|(((f x_1) - (f x_2)))| ≤ (M * |((x_1 - x_2))|)))))))))))))
  (h9 : (forall (M : ℝ), (((M ∈ (Set.univ : Set ℝ)) ∧ (M > 0)) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 = (v_uCE_uB5 /. M))) ∧ (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioo a b))) ∧ (x_2 ∈ (Set.Ioo a b))) ∧ (|((x_1 - x_2))| < v_uCE_uB4)) → ((M * |((x_1 - x_2))|) < v_uCE_uB5))))))))))))
  : (forall (M : ℝ), (((M ∈ (Set.univ : Set ℝ)) ∧ (M > 0)) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 = (v_uCE_uB5 /. M))) ∧ (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioo a b))) ∧ (x_2 ∈ (Set.Ioo a b))) ∧ (|((x_1 - x_2))| < v_uCE_uB4)) → (|(((f x_1) - (f x_2)))| < v_uCE_uB5))))))))))) := by
  sorry

theorem proof_gap_exercise_1255_6
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : a < b)
  (h4 : DifferentiableOn ℝ f (Set.Ioo a b))
  (h5 : Bornology.IsBounded ((fun (x1 : ℝ) => (iteratedDeriv 1 (fun t => f t) x1)) '' (Set.Ioo a b)))
  (h6 : (exists (M : ℝ), (((M ∈ (Set.univ : Set ℝ)) ∧ (M > 0)) ∧ (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo a b))) → (|((iteratedDeriv 1 (fun t => f t) x))| ≤ M))))))
  : UniformContinuousOn f (Set.Ioo a b) := by
  sorry

theorem proof_gap_exercise_1255_7
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : a < b)
  (h4 : DifferentiableOn ℝ f (Set.Ioo a b))
  (h5 : Bornology.IsBounded ((fun (x1 : ℝ) => (iteratedDeriv 1 (fun t => f t) x1)) '' (Set.Ioo a b)))
  (h6 : (exists (M : ℝ), (((M ∈ (Set.univ : Set ℝ)) ∧ (M > 0)) ∧ (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo a b))) → (|((iteratedDeriv 1 (fun t => f t) x))| ≤ M))))))
  (h7 : (forall (M : ℝ), (((M ∈ (Set.univ : Set ℝ)) ∧ (M > 0)) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 = (v_uCE_uB5 /. M))) ∧ (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioo a b))) ∧ (x_2 ∈ (Set.Ioo a b))) ∧ (|((x_1 - x_2))| < v_uCE_uB4)) → (exists (v_uCE_uBE : ℝ), (((v_uCE_uBE ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uBE ∈ (Set.Ioo a b))) ∧ (|(((f x_1) - (f x_2)))| = (|((x_1 - x_2))| * |((iteratedDeriv 1 (fun t => f t) v_uCE_uBE))|)))))))))))))))
  (h8 : (forall (M : ℝ), (((M ∈ (Set.univ : Set ℝ)) ∧ (M > 0)) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 = (v_uCE_uB5 /. M))) ∧ (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioo a b))) ∧ (x_2 ∈ (Set.Ioo a b))) ∧ (|((x_1 - x_2))| < v_uCE_uB4)) → (|(((f x_1) - (f x_2)))| ≤ (M * |((x_1 - x_2))|)))))))))))))
  (h9 : (forall (M : ℝ), (((M ∈ (Set.univ : Set ℝ)) ∧ (M > 0)) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 = (v_uCE_uB5 /. M))) ∧ (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioo a b))) ∧ (x_2 ∈ (Set.Ioo a b))) ∧ (|((x_1 - x_2))| < v_uCE_uB4)) → ((M * |((x_1 - x_2))|) < v_uCE_uB5))))))))))))
  (h10 : (forall (M : ℝ), (((M ∈ (Set.univ : Set ℝ)) ∧ (M > 0)) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 = (v_uCE_uB5 /. M))) ∧ (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioo a b))) ∧ (x_2 ∈ (Set.Ioo a b))) ∧ (|((x_1 - x_2))| < v_uCE_uB4)) → (|(((f x_1) - (f x_2)))| < v_uCE_uB5))))))))))))
  (h11 : UniformContinuousOn f (Set.Ioo a b))
  : UniformContinuousOn f (Set.Ioo a b) := by
  sorry

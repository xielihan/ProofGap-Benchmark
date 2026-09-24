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

-- exercise: exercise_799

theorem proof_gap_exercise_799_1
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ici 1))) → ((f x) = (Real.rpow x (((2 : ℝ))⁻¹))))))
  : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ici 1))) ∧ (x_2 ∈ (Set.Ici 1))) → (|(((Real.rpow x_1 (((2 : ℝ))⁻¹)) - (Real.rpow x_2 (((2 : ℝ))⁻¹))))| = |(((x_1 - x_2) /. ((Real.rpow x_1 (((2 : ℝ))⁻¹)) + (Real.rpow x_2 (((2 : ℝ))⁻¹)))))|))))) := by
  sorry

theorem proof_gap_exercise_799_2
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ici 1))) → ((f x) = (Real.rpow x (((2 : ℝ))⁻¹))))))
  (h2 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ici 1))) ∧ (x_2 ∈ (Set.Ici 1))) → (|(((Real.rpow x_1 (((2 : ℝ))⁻¹)) - (Real.rpow x_2 (((2 : ℝ))⁻¹))))| = |(((x_1 - x_2) /. ((Real.rpow x_1 (((2 : ℝ))⁻¹)) + (Real.rpow x_2 (((2 : ℝ))⁻¹)))))|))))))
  : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ici 1))) ∧ (x_2 ∈ (Set.Ici 1))) → (|(((x_1 - x_2) /. ((Real.rpow x_1 (((2 : ℝ))⁻¹)) + (Real.rpow x_2 (((2 : ℝ))⁻¹)))))| ≤ (|((x_1 - x_2))| /. 2)))))) := by
  sorry

theorem proof_gap_exercise_799_3
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ici 1))) → ((f x) = (Real.rpow x (((2 : ℝ))⁻¹))))))
  (h2 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ici 1))) ∧ (x_2 ∈ (Set.Ici 1))) → (|(((Real.rpow x_1 (((2 : ℝ))⁻¹)) - (Real.rpow x_2 (((2 : ℝ))⁻¹))))| = |(((x_1 - x_2) /. ((Real.rpow x_1 (((2 : ℝ))⁻¹)) + (Real.rpow x_2 (((2 : ℝ))⁻¹)))))|))))))
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ici 1))) ∧ (x_2 ∈ (Set.Ici 1))) → (|(((x_1 - x_2) /. ((Real.rpow x_1 (((2 : ℝ))⁻¹)) + (Real.rpow x_2 (((2 : ℝ))⁻¹)))))| ≤ (|((x_1 - x_2))| /. 2)))))))
  : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ici 1))) ∧ (x_2 ∈ (Set.Ici 1))) → (|(((Real.rpow x_1 (((2 : ℝ))⁻¹)) - (Real.rpow x_2 (((2 : ℝ))⁻¹))))| ≤ (|((x_1 - x_2))| /. 2)))))) := by
  sorry

theorem proof_gap_exercise_799_4
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ici 1))) → ((f x) = (Real.rpow x (((2 : ℝ))⁻¹))))))
  (h2 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ici 1))) ∧ (x_2 ∈ (Set.Ici 1))) → (|(((Real.rpow x_1 (((2 : ℝ))⁻¹)) - (Real.rpow x_2 (((2 : ℝ))⁻¹))))| = |(((x_1 - x_2) /. ((Real.rpow x_1 (((2 : ℝ))⁻¹)) + (Real.rpow x_2 (((2 : ℝ))⁻¹)))))|))))))
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ici 1))) ∧ (x_2 ∈ (Set.Ici 1))) → (|(((x_1 - x_2) /. ((Real.rpow x_1 (((2 : ℝ))⁻¹)) + (Real.rpow x_2 (((2 : ℝ))⁻¹)))))| ≤ (|((x_1 - x_2))| /. 2)))))))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ici 1))) ∧ (x_2 ∈ (Set.Ici 1))) → (|(((Real.rpow x_1 (((2 : ℝ))⁻¹)) - (Real.rpow x_2 (((2 : ℝ))⁻¹))))| ≤ (|((x_1 - x_2))| /. 2)))))))
  : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 = (2 * v_uCE_uB5))) ∧ (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (|((x_1 - x_2))| < v_uCE_uB4)) ∧ (x_1 ∈ (Set.Ici 1))) ∧ (x_2 ∈ (Set.Ici 1))) → (|(((Real.rpow x_1 (((2 : ℝ))⁻¹)) - (Real.rpow x_2 (((2 : ℝ))⁻¹))))| < (((1 /. 2) * 2) * v_uCE_uB5)))))))))) := by
  sorry

theorem proof_gap_exercise_799_5
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ici 1))) → ((f x) = (Real.rpow x (((2 : ℝ))⁻¹))))))
  (h2 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ici 1))) ∧ (x_2 ∈ (Set.Ici 1))) → (|(((Real.rpow x_1 (((2 : ℝ))⁻¹)) - (Real.rpow x_2 (((2 : ℝ))⁻¹))))| = |(((x_1 - x_2) /. ((Real.rpow x_1 (((2 : ℝ))⁻¹)) + (Real.rpow x_2 (((2 : ℝ))⁻¹)))))|))))))
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ici 1))) ∧ (x_2 ∈ (Set.Ici 1))) → (|(((x_1 - x_2) /. ((Real.rpow x_1 (((2 : ℝ))⁻¹)) + (Real.rpow x_2 (((2 : ℝ))⁻¹)))))| ≤ (|((x_1 - x_2))| /. 2)))))))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ici 1))) ∧ (x_2 ∈ (Set.Ici 1))) → (|(((Real.rpow x_1 (((2 : ℝ))⁻¹)) - (Real.rpow x_2 (((2 : ℝ))⁻¹))))| ≤ (|((x_1 - x_2))| /. 2)))))))
  (h5 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 = (2 * v_uCE_uB5))) ∧ (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (|((x_1 - x_2))| < v_uCE_uB4)) ∧ (x_1 ∈ (Set.Ici 1))) ∧ (x_2 ∈ (Set.Ici 1))) → (|(((Real.rpow x_1 (((2 : ℝ))⁻¹)) - (Real.rpow x_2 (((2 : ℝ))⁻¹))))| < (((1 /. 2) * 2) * v_uCE_uB5)))))))))))
  : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 = (2 * v_uCE_uB5))) ∧ (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (|((x_1 - x_2))| < v_uCE_uB4)) ∧ (x_1 ∈ (Set.Ici 1))) ∧ (x_2 ∈ (Set.Ici 1))) → (|(((f x_1) - (f x_2)))| < v_uCE_uB5))))))))) := by
  sorry

theorem proof_gap_exercise_799_6
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ici 1))) → ((f x) = (Real.rpow x (((2 : ℝ))⁻¹))))))
  (h2 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ici 1))) ∧ (x_2 ∈ (Set.Ici 1))) → (|(((Real.rpow x_1 (((2 : ℝ))⁻¹)) - (Real.rpow x_2 (((2 : ℝ))⁻¹))))| = |(((x_1 - x_2) /. ((Real.rpow x_1 (((2 : ℝ))⁻¹)) + (Real.rpow x_2 (((2 : ℝ))⁻¹)))))|))))))
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ici 1))) ∧ (x_2 ∈ (Set.Ici 1))) → (|(((x_1 - x_2) /. ((Real.rpow x_1 (((2 : ℝ))⁻¹)) + (Real.rpow x_2 (((2 : ℝ))⁻¹)))))| ≤ (|((x_1 - x_2))| /. 2)))))))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ici 1))) ∧ (x_2 ∈ (Set.Ici 1))) → (|(((Real.rpow x_1 (((2 : ℝ))⁻¹)) - (Real.rpow x_2 (((2 : ℝ))⁻¹))))| ≤ (|((x_1 - x_2))| /. 2)))))))
  (h5 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 = (2 * v_uCE_uB5))) ∧ (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (|((x_1 - x_2))| < v_uCE_uB4)) ∧ (x_1 ∈ (Set.Ici 1))) ∧ (x_2 ∈ (Set.Ici 1))) → (|(((Real.rpow x_1 (((2 : ℝ))⁻¹)) - (Real.rpow x_2 (((2 : ℝ))⁻¹))))| < (((1 /. 2) * 2) * v_uCE_uB5)))))))))))
  (h6 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 = (2 * v_uCE_uB5))) ∧ (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (|((x_1 - x_2))| < v_uCE_uB4)) ∧ (x_1 ∈ (Set.Ici 1))) ∧ (x_2 ∈ (Set.Ici 1))) → (|(((f x_1) - (f x_2)))| < v_uCE_uB5))))))))))
  : UniformContinuousOn f (Set.Ici 1) := by
  sorry

theorem proof_gap_exercise_799_7
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ici 1))) → ((f x) = (Real.rpow x (((2 : ℝ))⁻¹))))))
  (h2 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ici 1))) ∧ (x_2 ∈ (Set.Ici 1))) → (|(((Real.rpow x_1 (((2 : ℝ))⁻¹)) - (Real.rpow x_2 (((2 : ℝ))⁻¹))))| = |(((x_1 - x_2) /. ((Real.rpow x_1 (((2 : ℝ))⁻¹)) + (Real.rpow x_2 (((2 : ℝ))⁻¹)))))|))))))
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ici 1))) ∧ (x_2 ∈ (Set.Ici 1))) → (|(((x_1 - x_2) /. ((Real.rpow x_1 (((2 : ℝ))⁻¹)) + (Real.rpow x_2 (((2 : ℝ))⁻¹)))))| ≤ (|((x_1 - x_2))| /. 2)))))))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ici 1))) ∧ (x_2 ∈ (Set.Ici 1))) → (|(((Real.rpow x_1 (((2 : ℝ))⁻¹)) - (Real.rpow x_2 (((2 : ℝ))⁻¹))))| ≤ (|((x_1 - x_2))| /. 2)))))))
  (h5 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 = (2 * v_uCE_uB5))) ∧ (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (|((x_1 - x_2))| < v_uCE_uB4)) ∧ (x_1 ∈ (Set.Ici 1))) ∧ (x_2 ∈ (Set.Ici 1))) → (|(((Real.rpow x_1 (((2 : ℝ))⁻¹)) - (Real.rpow x_2 (((2 : ℝ))⁻¹))))| < (((1 /. 2) * 2) * v_uCE_uB5)))))))))))
  (h6 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 = (2 * v_uCE_uB5))) ∧ (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (|((x_1 - x_2))| < v_uCE_uB4)) ∧ (x_1 ∈ (Set.Ici 1))) ∧ (x_2 ∈ (Set.Ici 1))) → (|(((f x_1) - (f x_2)))| < v_uCE_uB5))))))))))
  (h7 : UniformContinuousOn f (Set.Ici 1))
  : UniformContinuousOn f (Set.Ici 1) := by
  sorry

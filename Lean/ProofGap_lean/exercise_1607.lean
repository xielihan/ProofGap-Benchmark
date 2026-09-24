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

-- exercise: exercise_1607

theorem proof_gap_exercise_1607_1
  (r : (ℝ -> ℝ))
  (R : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (forall (v_uCF_u86 : ℝ), ((v_uCF_u86 ∈ (Set.univ : Set ℝ)) → ((r v_uCF_u86) = (a * (1 + (Real.cos v_uCF_u86)))))))
  : (forall (v_uCF_u86 : ℝ), ((v_uCF_u86 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => r t) v_uCF_u86) = ((-a) * (Real.sin v_uCF_u86))))) := by
  sorry

theorem proof_gap_exercise_1607_2
  (r : (ℝ -> ℝ))
  (R : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (forall (v_uCF_u86 : ℝ), ((v_uCF_u86 ∈ (Set.univ : Set ℝ)) → ((r v_uCF_u86) = (a * (1 + (Real.cos v_uCF_u86)))))))
  (h3 : (forall (v_uCF_u86 : ℝ), ((v_uCF_u86 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => r t) v_uCF_u86) = ((-a) * (Real.sin v_uCF_u86))))))
  : (forall (v_uCF_u86 : ℝ), ((v_uCF_u86 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => r t) v_uCF_u86) = ((-a) * (Real.cos v_uCF_u86))))) := by
  sorry

theorem proof_gap_exercise_1607_3
  (r : (ℝ -> ℝ))
  (R : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (forall (v_uCF_u86 : ℝ), ((v_uCF_u86 ∈ (Set.univ : Set ℝ)) → ((r v_uCF_u86) = (a * (1 + (Real.cos v_uCF_u86)))))))
  (h3 : (forall (v_uCF_u86 : ℝ), ((v_uCF_u86 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => r t) v_uCF_u86) = ((-a) * (Real.sin v_uCF_u86))))))
  (h4 : (forall (v_uCF_u86 : ℝ), ((v_uCF_u86 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => r t) v_uCF_u86) = ((-a) * (Real.cos v_uCF_u86))))))
  : (forall (v_uCF_u86 : ℝ), (((v_uCF_u86 ∈ (Set.univ : Set ℝ)) ∧ ((1 + (Real.cos v_uCF_u86)) ≠ 0)) → ((R v_uCF_u86) = ((Real.rpow (((a ^ (2 : ℕ)) * ((1 + (Real.cos v_uCF_u86)) ^ (2 : ℕ))) + ((a ^ (2 : ℕ)) * ((Real.sin v_uCF_u86) ^ (2 : ℕ)))) (3 /. 2)) /. ((((a ^ (2 : ℕ)) * ((1 + (Real.cos v_uCF_u86)) ^ (2 : ℕ))) + ((2 * (a ^ (2 : ℕ))) * ((Real.sin v_uCF_u86) ^ (2 : ℕ)))) + (((a ^ (2 : ℕ)) * (Real.cos v_uCF_u86)) * (1 + (Real.cos v_uCF_u86)))))))) := by
  sorry

theorem proof_gap_exercise_1607_4
  (r : (ℝ -> ℝ))
  (R : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (forall (v_uCF_u86 : ℝ), ((v_uCF_u86 ∈ (Set.univ : Set ℝ)) → ((r v_uCF_u86) = (a * (1 + (Real.cos v_uCF_u86)))))))
  (h3 : (forall (v_uCF_u86 : ℝ), ((v_uCF_u86 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => r t) v_uCF_u86) = ((-a) * (Real.sin v_uCF_u86))))))
  (h4 : (forall (v_uCF_u86 : ℝ), ((v_uCF_u86 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => r t) v_uCF_u86) = ((-a) * (Real.cos v_uCF_u86))))))
  (h5 : (forall (v_uCF_u86 : ℝ), (((v_uCF_u86 ∈ (Set.univ : Set ℝ)) ∧ ((1 + (Real.cos v_uCF_u86)) ≠ 0)) → ((R v_uCF_u86) = ((Real.rpow (((a ^ (2 : ℕ)) * ((1 + (Real.cos v_uCF_u86)) ^ (2 : ℕ))) + ((a ^ (2 : ℕ)) * ((Real.sin v_uCF_u86) ^ (2 : ℕ)))) (3 /. 2)) /. ((((a ^ (2 : ℕ)) * ((1 + (Real.cos v_uCF_u86)) ^ (2 : ℕ))) + ((2 * (a ^ (2 : ℕ))) * ((Real.sin v_uCF_u86) ^ (2 : ℕ)))) + (((a ^ (2 : ℕ)) * (Real.cos v_uCF_u86)) * (1 + (Real.cos v_uCF_u86)))))))))
  : (forall (v_uCF_u86 : ℝ), (((v_uCF_u86 ∈ (Set.univ : Set ℝ)) ∧ ((1 + (Real.cos v_uCF_u86)) ≠ 0)) → ((R v_uCF_u86) = ((((2 * (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))) * (a ^ (3 : ℕ))) * (Real.rpow (1 + (Real.cos v_uCF_u86)) (3 /. 2))) /. ((3 * (a ^ (2 : ℕ))) * (1 + (Real.cos v_uCF_u86))))))) := by
  sorry

theorem proof_gap_exercise_1607_5
  (r : (ℝ -> ℝ))
  (R : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (forall (v_uCF_u86 : ℝ), ((v_uCF_u86 ∈ (Set.univ : Set ℝ)) → ((r v_uCF_u86) = (a * (1 + (Real.cos v_uCF_u86)))))))
  (h3 : (forall (v_uCF_u86 : ℝ), ((v_uCF_u86 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => r t) v_uCF_u86) = ((-a) * (Real.sin v_uCF_u86))))))
  (h4 : (forall (v_uCF_u86 : ℝ), ((v_uCF_u86 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => r t) v_uCF_u86) = ((-a) * (Real.cos v_uCF_u86))))))
  (h5 : (forall (v_uCF_u86 : ℝ), (((v_uCF_u86 ∈ (Set.univ : Set ℝ)) ∧ ((1 + (Real.cos v_uCF_u86)) ≠ 0)) → ((R v_uCF_u86) = ((Real.rpow (((a ^ (2 : ℕ)) * ((1 + (Real.cos v_uCF_u86)) ^ (2 : ℕ))) + ((a ^ (2 : ℕ)) * ((Real.sin v_uCF_u86) ^ (2 : ℕ)))) (3 /. 2)) /. ((((a ^ (2 : ℕ)) * ((1 + (Real.cos v_uCF_u86)) ^ (2 : ℕ))) + ((2 * (a ^ (2 : ℕ))) * ((Real.sin v_uCF_u86) ^ (2 : ℕ)))) + (((a ^ (2 : ℕ)) * (Real.cos v_uCF_u86)) * (1 + (Real.cos v_uCF_u86)))))))))
  (h6 : (forall (v_uCF_u86 : ℝ), (((v_uCF_u86 ∈ (Set.univ : Set ℝ)) ∧ ((1 + (Real.cos v_uCF_u86)) ≠ 0)) → ((R v_uCF_u86) = ((((2 * (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))) * (a ^ (3 : ℕ))) * (Real.rpow (1 + (Real.cos v_uCF_u86)) (3 /. 2))) /. ((3 * (a ^ (2 : ℕ))) * (1 + (Real.cos v_uCF_u86))))))))
  : (forall (v_uCF_u86 : ℝ), (((v_uCF_u86 ∈ (Set.univ : Set ℝ)) ∧ ((1 + (Real.cos v_uCF_u86)) ≠ 0)) → ((R v_uCF_u86) = ((2 /. 3) * (Real.rpow ((2 * a) * (r v_uCF_u86)) (((2 : ℝ))⁻¹)))))) := by
  sorry

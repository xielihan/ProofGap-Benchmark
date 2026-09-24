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

-- exercise: exercise_2447

theorem proof_gap_exercise_2447_1
  (r : (ℝ -> ℝ))
  (a : ℝ)
  (m : ℝ)
  (s : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (m ∈ (Set.univ : Set ℝ)) ∧ (m > 0))
  (h3 : s ∈ (Set.univ : Set ℝ))
  (h4 : (forall (v_uCF_u86 : ℝ), ((v_uCF_u86 ∈ (Set.univ : Set ℝ)) → ((r v_uCF_u86) = (a * (Real.exp (m * v_uCF_u86)))))))
  : (forall (v_uCF_u86 : ℝ), ((((v_uCF_u86 ∈ (Set.univ : Set ℝ)) ∧ (0 < (r v_uCF_u86))) ∧ ((r v_uCF_u86) < a)) → ((⊥ < (v_uCF_u86 : EReal)) ∧ (v_uCF_u86 < 0)))) := by
  sorry

theorem proof_gap_exercise_2447_2
  (r : (ℝ -> ℝ))
  (a : ℝ)
  (m : ℝ)
  (s : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (m ∈ (Set.univ : Set ℝ)) ∧ (m > 0))
  (h3 : s ∈ (Set.univ : Set ℝ))
  (h4 : (forall (v_uCF_u86 : ℝ), ((v_uCF_u86 ∈ (Set.univ : Set ℝ)) → ((r v_uCF_u86) = (a * (Real.exp (m * v_uCF_u86)))))))
  (h5 : (forall (v_uCF_u86 : ℝ), ((((v_uCF_u86 ∈ (Set.univ : Set ℝ)) ∧ (0 < (r v_uCF_u86))) ∧ ((r v_uCF_u86) < a)) → ((⊥ < (v_uCF_u86 : EReal)) ∧ (v_uCF_u86 < 0)))))
  (h6 : (forall (v_uCF_u86 : ℝ), (((v_uCF_u86 ∈ (Set.univ : Set ℝ)) ∧ (v_uCF_u86 < 0)) → (s = ((a * (Real.rpow ((m ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹))) * (∫ v_uCF_u86_1 in Set.Iio (0 : ℝ), ((Real.exp (m * v_uCF_u86_1)) * (1 : ℝ))))))))
  : (forall (v_uCF_u86 : ℝ), (((v_uCF_u86 ∈ (Set.univ : Set ℝ)) ∧ (v_uCF_u86 < 0)) → (s = (∫ v_uCF_u86_1 in Set.Iio (0 : ℝ), ((Real.rpow (((a ^ (2 : ℕ)) * (Real.exp ((2 * m) * v_uCF_u86_1))) + (((a ^ (2 : ℕ)) * (m ^ (2 : ℕ))) * (Real.exp ((2 * m) * v_uCF_u86_1)))) (((2 : ℝ))⁻¹)) * (1 : ℝ)))))) := by
  sorry

theorem proof_gap_exercise_2447_3
  (r : (ℝ -> ℝ))
  (a : ℝ)
  (m : ℝ)
  (s : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (m ∈ (Set.univ : Set ℝ)) ∧ (m > 0))
  (h3 : s ∈ (Set.univ : Set ℝ))
  (h4 : (forall (v_uCF_u86 : ℝ), ((v_uCF_u86 ∈ (Set.univ : Set ℝ)) → ((r v_uCF_u86) = (a * (Real.exp (m * v_uCF_u86)))))))
  (h5 : (forall (v_uCF_u86 : ℝ), ((((v_uCF_u86 ∈ (Set.univ : Set ℝ)) ∧ (0 < (r v_uCF_u86))) ∧ ((r v_uCF_u86) < a)) → ((⊥ < (v_uCF_u86 : EReal)) ∧ (v_uCF_u86 < 0)))))
  (h6 : (forall (v_uCF_u86 : ℝ), (((v_uCF_u86 ∈ (Set.univ : Set ℝ)) ∧ (v_uCF_u86 < 0)) → (s = (∫ v_uCF_u86_1 in Set.Iio (0 : ℝ), ((Real.rpow (((a ^ (2 : ℕ)) * (Real.exp ((2 * m) * v_uCF_u86_1))) + (((a ^ (2 : ℕ)) * (m ^ (2 : ℕ))) * (Real.exp ((2 * m) * v_uCF_u86_1)))) (((2 : ℝ))⁻¹)) * (1 : ℝ)))))))
  : (forall (v_uCF_u86 : ℝ), (((v_uCF_u86 ∈ (Set.univ : Set ℝ)) ∧ (v_uCF_u86 < 0)) → (s = ((a * (Real.rpow ((m ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹))) * (∫ v_uCF_u86_1 in Set.Iio (0 : ℝ), ((Real.exp (m * v_uCF_u86_1)) * (1 : ℝ))))))) := by
  sorry

theorem proof_gap_exercise_2447_4
  (r : (ℝ -> ℝ))
  (a : ℝ)
  (m : ℝ)
  (s : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (m ∈ (Set.univ : Set ℝ)) ∧ (m > 0))
  (h3 : s ∈ (Set.univ : Set ℝ))
  (h4 : (forall (v_uCF_u86 : ℝ), ((v_uCF_u86 ∈ (Set.univ : Set ℝ)) → ((r v_uCF_u86) = (a * (Real.exp (m * v_uCF_u86)))))))
  (h5 : (forall (v_uCF_u86 : ℝ), ((((v_uCF_u86 ∈ (Set.univ : Set ℝ)) ∧ (0 < (r v_uCF_u86))) ∧ ((r v_uCF_u86) < a)) → ((⊥ < (v_uCF_u86 : EReal)) ∧ (v_uCF_u86 < 0)))))
  (h6 : (forall (v_uCF_u86 : ℝ), (((v_uCF_u86 ∈ (Set.univ : Set ℝ)) ∧ (v_uCF_u86 < 0)) → (s = (∫ v_uCF_u86_1 in Set.Iio (0 : ℝ), ((Real.rpow (((a ^ (2 : ℕ)) * (Real.exp ((2 * m) * v_uCF_u86_1))) + (((a ^ (2 : ℕ)) * (m ^ (2 : ℕ))) * (Real.exp ((2 * m) * v_uCF_u86_1)))) (((2 : ℝ))⁻¹)) * (1 : ℝ)))))))
  (h7 : (forall (v_uCF_u86 : ℝ), (((v_uCF_u86 ∈ (Set.univ : Set ℝ)) ∧ (v_uCF_u86 < 0)) → (s = ((a * (Real.rpow ((m ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹))) * (∫ v_uCF_u86_1 in Set.Iio (0 : ℝ), ((Real.exp (m * v_uCF_u86_1)) * (1 : ℝ))))))))
  : s = ((a * (Real.rpow (1 + (m ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. m) := by
  sorry

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

-- exercise: exercise_2421

theorem proof_gap_exercise_2421_1
  (r : (ℝ -> ℝ))
  (p : ℝ)
  (S : ℝ)
  (h1 : (p ∈ (Set.univ : Set ℝ)) ∧ (p > 0))
  (h2 : S ∈ (Set.univ : Set ℝ))
  (h3 : (forall (v_uCF_u86 : ℝ), ((((v_uCF_u86 ∈ (Set.univ : Set ℝ)) ∧ ((Real.pi /. 4) ≤ v_uCF_u86)) ∧ (v_uCF_u86 ≤ (Real.pi /. 2))) → ((r v_uCF_u86) = (p /. (1 - (Real.cos v_uCF_u86)))))))
  : S = ((1 /. 2) * (∫ v_uCF_u86 in (Real.pi /. 4)..(Real.pi /. 2), (((r v_uCF_u86) ^ (2 : ℕ)) * (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_2421_2
  (r : (ℝ -> ℝ))
  (p : ℝ)
  (S : ℝ)
  (h1 : (p ∈ (Set.univ : Set ℝ)) ∧ (p > 0))
  (h2 : S ∈ (Set.univ : Set ℝ))
  (h3 : (forall (v_uCF_u86 : ℝ), ((((v_uCF_u86 ∈ (Set.univ : Set ℝ)) ∧ ((Real.pi /. 4) ≤ v_uCF_u86)) ∧ (v_uCF_u86 ≤ (Real.pi /. 2))) → ((r v_uCF_u86) = (p /. (1 - (Real.cos v_uCF_u86)))))))
  (h4 : S = ((1 /. 2) * (∫ v_uCF_u86 in (Real.pi /. 4)..(Real.pi /. 2), (((r v_uCF_u86) ^ (2 : ℕ)) * (1 : ℝ)))))
  : S = ((1 /. 2) * (∫ v_uCF_u86 in (Real.pi /. 4)..(Real.pi /. 2), (((p ^ (2 : ℕ)) /. ((1 - (Real.cos v_uCF_u86)) ^ (2 : ℕ))) * (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_2421_3
  (r : (ℝ -> ℝ))
  (p : ℝ)
  (S : ℝ)
  (h1 : (p ∈ (Set.univ : Set ℝ)) ∧ (p > 0))
  (h2 : S ∈ (Set.univ : Set ℝ))
  (h3 : (forall (v_uCF_u86 : ℝ), ((((v_uCF_u86 ∈ (Set.univ : Set ℝ)) ∧ ((Real.pi /. 4) ≤ v_uCF_u86)) ∧ (v_uCF_u86 ≤ (Real.pi /. 2))) → ((r v_uCF_u86) = (p /. (1 - (Real.cos v_uCF_u86)))))))
  (h4 : S = ((1 /. 2) * (∫ v_uCF_u86 in (Real.pi /. 4)..(Real.pi /. 2), (((r v_uCF_u86) ^ (2 : ℕ)) * (1 : ℝ)))))
  (h5 : S = ((1 /. 2) * (∫ v_uCF_u86 in (Real.pi /. 4)..(Real.pi /. 2), (((p ^ (2 : ℕ)) /. ((1 - (Real.cos v_uCF_u86)) ^ (2 : ℕ))) * (1 : ℝ)))))
  : S = (((p ^ (2 : ℕ)) /. 4) * (∫ v_uCF_u86 in (Real.pi /. 4)..(Real.pi /. 2), ((((1 : ℝ) /. (Real.sin (v_uCF_u86 /. 2))) ^ (4 : ℕ)) * (deriv (fun (v_uCF_u86 : ℝ) => (v_uCF_u86 /. 2)) v_uCF_u86)))) := by
  sorry

theorem proof_gap_exercise_2421_4
  (r : (ℝ -> ℝ))
  (p : ℝ)
  (S : ℝ)
  (h1 : (p ∈ (Set.univ : Set ℝ)) ∧ (p > 0))
  (h2 : S ∈ (Set.univ : Set ℝ))
  (h3 : (forall (v_uCF_u86 : ℝ), ((((v_uCF_u86 ∈ (Set.univ : Set ℝ)) ∧ ((Real.pi /. 4) ≤ v_uCF_u86)) ∧ (v_uCF_u86 ≤ (Real.pi /. 2))) → ((r v_uCF_u86) = (p /. (1 - (Real.cos v_uCF_u86)))))))
  (h4 : S = ((1 /. 2) * (∫ v_uCF_u86 in (Real.pi /. 4)..(Real.pi /. 2), (((r v_uCF_u86) ^ (2 : ℕ)) * (1 : ℝ)))))
  (h5 : S = ((1 /. 2) * (∫ v_uCF_u86 in (Real.pi /. 4)..(Real.pi /. 2), (((p ^ (2 : ℕ)) /. ((1 - (Real.cos v_uCF_u86)) ^ (2 : ℕ))) * (1 : ℝ)))))
  (h6 : S = (((p ^ (2 : ℕ)) /. 4) * (∫ v_uCF_u86 in (Real.pi /. 4)..(Real.pi /. 2), ((((1 : ℝ) /. (Real.sin (v_uCF_u86 /. 2))) ^ (4 : ℕ)) * (deriv (fun (v_uCF_u86 : ℝ) => (v_uCF_u86 /. 2)) v_uCF_u86)))))
  : S = (((-((p ^ (2 : ℕ)) /. 4)) * (((1 : ℝ) /. (Real.tan ((Real.pi /. 2) /. 2))) + ((1 /. 3) * (((1 : ℝ) /. (Real.tan ((Real.pi /. 2) /. 2))) ^ (3 : ℕ))))) - ((-((p ^ (2 : ℕ)) /. 4)) * (((1 : ℝ) /. (Real.tan ((Real.pi /. 4) /. 2))) + ((1 /. 3) * (((1 : ℝ) /. (Real.tan ((Real.pi /. 4) /. 2))) ^ (3 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_2421_5
  (r : (ℝ -> ℝ))
  (p : ℝ)
  (S : ℝ)
  (h1 : (p ∈ (Set.univ : Set ℝ)) ∧ (p > 0))
  (h2 : S ∈ (Set.univ : Set ℝ))
  (h3 : (forall (v_uCF_u86 : ℝ), ((((v_uCF_u86 ∈ (Set.univ : Set ℝ)) ∧ ((Real.pi /. 4) ≤ v_uCF_u86)) ∧ (v_uCF_u86 ≤ (Real.pi /. 2))) → ((r v_uCF_u86) = (p /. (1 - (Real.cos v_uCF_u86)))))))
  (h4 : S = ((1 /. 2) * (∫ v_uCF_u86 in (Real.pi /. 4)..(Real.pi /. 2), (((r v_uCF_u86) ^ (2 : ℕ)) * (1 : ℝ)))))
  (h5 : S = ((1 /. 2) * (∫ v_uCF_u86 in (Real.pi /. 4)..(Real.pi /. 2), (((p ^ (2 : ℕ)) /. ((1 - (Real.cos v_uCF_u86)) ^ (2 : ℕ))) * (1 : ℝ)))))
  (h6 : S = (((p ^ (2 : ℕ)) /. 4) * (∫ v_uCF_u86 in (Real.pi /. 4)..(Real.pi /. 2), ((((1 : ℝ) /. (Real.sin (v_uCF_u86 /. 2))) ^ (4 : ℕ)) * (deriv (fun (v_uCF_u86 : ℝ) => (v_uCF_u86 /. 2)) v_uCF_u86)))))
  (h7 : S = (((-((p ^ (2 : ℕ)) /. 4)) * (((1 : ℝ) /. (Real.tan ((Real.pi /. 2) /. 2))) + ((1 /. 3) * (((1 : ℝ) /. (Real.tan ((Real.pi /. 2) /. 2))) ^ (3 : ℕ))))) - ((-((p ^ (2 : ℕ)) /. 4)) * (((1 : ℝ) /. (Real.tan ((Real.pi /. 4) /. 2))) + ((1 /. 3) * (((1 : ℝ) /. (Real.tan ((Real.pi /. 4) /. 2))) ^ (3 : ℕ)))))))
  : ((1 : ℝ) /. (Real.tan (Real.pi /. 8))) = (1 + (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))) := by
  sorry

theorem proof_gap_exercise_2421_6
  (r : (ℝ -> ℝ))
  (p : ℝ)
  (S : ℝ)
  (h1 : (p ∈ (Set.univ : Set ℝ)) ∧ (p > 0))
  (h2 : S ∈ (Set.univ : Set ℝ))
  (h3 : (forall (v_uCF_u86 : ℝ), ((((v_uCF_u86 ∈ (Set.univ : Set ℝ)) ∧ ((Real.pi /. 4) ≤ v_uCF_u86)) ∧ (v_uCF_u86 ≤ (Real.pi /. 2))) → ((r v_uCF_u86) = (p /. (1 - (Real.cos v_uCF_u86)))))))
  (h4 : S = ((1 /. 2) * (∫ v_uCF_u86 in (Real.pi /. 4)..(Real.pi /. 2), (((r v_uCF_u86) ^ (2 : ℕ)) * (1 : ℝ)))))
  (h5 : S = ((1 /. 2) * (∫ v_uCF_u86 in (Real.pi /. 4)..(Real.pi /. 2), (((p ^ (2 : ℕ)) /. ((1 - (Real.cos v_uCF_u86)) ^ (2 : ℕ))) * (1 : ℝ)))))
  (h6 : S = (((p ^ (2 : ℕ)) /. 4) * (∫ v_uCF_u86 in (Real.pi /. 4)..(Real.pi /. 2), ((((1 : ℝ) /. (Real.sin (v_uCF_u86 /. 2))) ^ (4 : ℕ)) * (deriv (fun (v_uCF_u86 : ℝ) => (v_uCF_u86 /. 2)) v_uCF_u86)))))
  (h7 : S = (((-((p ^ (2 : ℕ)) /. 4)) * (((1 : ℝ) /. (Real.tan ((Real.pi /. 2) /. 2))) + ((1 /. 3) * (((1 : ℝ) /. (Real.tan ((Real.pi /. 2) /. 2))) ^ (3 : ℕ))))) - ((-((p ^ (2 : ℕ)) /. 4)) * (((1 : ℝ) /. (Real.tan ((Real.pi /. 4) /. 2))) + ((1 /. 3) * (((1 : ℝ) /. (Real.tan ((Real.pi /. 4) /. 2))) ^ (3 : ℕ)))))))
  (h8 : ((1 : ℝ) /. (Real.tan (Real.pi /. 8))) = (1 + (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))))
  : S = (((p ^ (2 : ℕ)) /. 6) * ((4 * (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))) + 3)) := by
  sorry

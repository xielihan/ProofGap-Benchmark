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

-- exercise: exercise_4157

theorem proof_gap_exercise_4157_1
  (u : (ℝ × (ℝ × ℝ) -> ℝ))
  (F : (ℝ -> ℝ))
  (a : ℝ)
  (h : ℝ)
  (v_uCF_u81__0 : ℝ)
  (z : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (h ∈ (Set.univ : Set ℝ)) ∧ (h > 0))
  (h3 : (v_uCF_u81__0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCF_u81__0 > 0))
  (h4 : z ∈ (Set.univ : Set ℝ))
  : (forall (z_1 : ℝ) (r : ℝ) (v_uCE_uB6 : ℝ), ((((((((z_1 ∈ (Set.univ : Set ℝ)) ∧ (r ∈ (Set.univ : Set ℝ))) ∧ (0 ≤ r)) ∧ (r ≤ a)) ∧ (v_uCE_uB6 ∈ (Set.univ : Set ℝ))) ∧ (0 ≤ v_uCE_uB6)) ∧ (v_uCE_uB6 ≤ h)) → ((u ((0 : ℝ), ((0 : ℝ), z_1))) = (((v_uCF_u81__0 * (∫ v_uCF_u86 in (0 : ℝ)..(2 * Real.pi), (1 : ℝ))) * (∫ v_uCE_uB6_1 in (0 : ℝ)..h, (1 : ℝ))) * (∫ r_1 in (0 : ℝ)..a, ((r_1 /. (Real.rpow ((r_1 ^ (2 : ℕ)) + ((v_uCE_uB6 - z_1) ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))))))) := by
  sorry

theorem proof_gap_exercise_4157_2
  (u : (ℝ × (ℝ × ℝ) -> ℝ))
  (F : (ℝ -> ℝ))
  (a : ℝ)
  (h : ℝ)
  (v_uCF_u81__0 : ℝ)
  (z : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (h ∈ (Set.univ : Set ℝ)) ∧ (h > 0))
  (h3 : (v_uCF_u81__0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCF_u81__0 > 0))
  (h4 : z ∈ (Set.univ : Set ℝ))
  (h5 : (forall (z_1 : ℝ) (r : ℝ) (v_uCE_uB6 : ℝ), ((((((((z_1 ∈ (Set.univ : Set ℝ)) ∧ (r ∈ (Set.univ : Set ℝ))) ∧ (0 ≤ r)) ∧ (r ≤ a)) ∧ (v_uCE_uB6 ∈ (Set.univ : Set ℝ))) ∧ (0 ≤ v_uCE_uB6)) ∧ (v_uCE_uB6 ≤ h)) → ((u ((0 : ℝ), ((0 : ℝ), z_1))) = (((v_uCF_u81__0 * (∫ v_uCF_u86 in (0 : ℝ)..(2 * Real.pi), (1 : ℝ))) * (∫ v_uCE_uB6_1 in (0 : ℝ)..h, (1 : ℝ))) * (∫ r_1 in (0 : ℝ)..a, ((r_1 /. (Real.rpow ((r_1 ^ (2 : ℕ)) + ((v_uCE_uB6 - z_1) ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))))))))
  : (forall (z_1 : ℝ) (v_uCE_uB6 : ℝ), (((((z_1 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB6 ∈ (Set.univ : Set ℝ))) ∧ (0 ≤ v_uCE_uB6)) ∧ (v_uCE_uB6 ≤ h)) → ((u ((0 : ℝ), ((0 : ℝ), z_1))) = (((2 * Real.pi) * v_uCF_u81__0) * (∫ v_uCE_uB6_1 in (0 : ℝ)..h, (((Real.rpow ((a ^ (2 : ℕ)) + ((v_uCE_uB6_1 - z_1) ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) - (Real.rpow (((0 : ℕ) ^ (2 : ℕ)) + ((v_uCE_uB6_1 - z_1) ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))))))) := by
  sorry

theorem proof_gap_exercise_4157_3
  (u : (ℝ × (ℝ × ℝ) -> ℝ))
  (F : (ℝ -> ℝ))
  (a : ℝ)
  (h : ℝ)
  (v_uCF_u81__0 : ℝ)
  (z : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (h ∈ (Set.univ : Set ℝ)) ∧ (h > 0))
  (h3 : (v_uCF_u81__0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCF_u81__0 > 0))
  (h4 : z ∈ (Set.univ : Set ℝ))
  (h5 : (forall (z_1 : ℝ) (r : ℝ) (v_uCE_uB6 : ℝ), ((((((((z_1 ∈ (Set.univ : Set ℝ)) ∧ (r ∈ (Set.univ : Set ℝ))) ∧ (0 ≤ r)) ∧ (r ≤ a)) ∧ (v_uCE_uB6 ∈ (Set.univ : Set ℝ))) ∧ (0 ≤ v_uCE_uB6)) ∧ (v_uCE_uB6 ≤ h)) → ((u ((0 : ℝ), ((0 : ℝ), z_1))) = (((v_uCF_u81__0 * (∫ v_uCF_u86 in (0 : ℝ)..(2 * Real.pi), (1 : ℝ))) * (∫ v_uCE_uB6_1 in (0 : ℝ)..h, (1 : ℝ))) * (∫ r_1 in (0 : ℝ)..a, ((r_1 /. (Real.rpow ((r_1 ^ (2 : ℕ)) + ((v_uCE_uB6 - z_1) ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))))))))
  (h6 : (forall (z_1 : ℝ) (v_uCE_uB6 : ℝ), (((((z_1 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB6 ∈ (Set.univ : Set ℝ))) ∧ (0 ≤ v_uCE_uB6)) ∧ (v_uCE_uB6 ≤ h)) → ((u ((0 : ℝ), ((0 : ℝ), z_1))) = (((2 * Real.pi) * v_uCF_u81__0) * (∫ v_uCE_uB6_1 in (0 : ℝ)..h, (((Real.rpow ((a ^ (2 : ℕ)) + ((v_uCE_uB6_1 - z_1) ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) - (Real.rpow (((0 : ℕ) ^ (2 : ℕ)) + ((v_uCE_uB6_1 - z_1) ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))))))))
  : (forall (z_1 : ℝ) (v_uCE_uB6 : ℝ), (((((z_1 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB6 ∈ (Set.univ : Set ℝ))) ∧ (0 ≤ v_uCE_uB6)) ∧ (v_uCE_uB6 ≤ h)) → ((u ((0 : ℝ), ((0 : ℝ), z_1))) = (((2 * Real.pi) * v_uCF_u81__0) * (∫ v_uCE_uB6_1 in (0 : ℝ)..h, (((Real.rpow ((a ^ (2 : ℕ)) + ((v_uCE_uB6_1 - z_1) ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) - |((v_uCE_uB6_1 - z_1))|) * (1 : ℝ))))))) := by
  sorry

theorem proof_gap_exercise_4157_4
  (u : (ℝ × (ℝ × ℝ) -> ℝ))
  (F : (ℝ -> ℝ))
  (a : ℝ)
  (h : ℝ)
  (v_uCF_u81__0 : ℝ)
  (z : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (h ∈ (Set.univ : Set ℝ)) ∧ (h > 0))
  (h3 : (v_uCF_u81__0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCF_u81__0 > 0))
  (h4 : z ∈ (Set.univ : Set ℝ))
  (h5 : (forall (z_1 : ℝ) (r : ℝ) (v_uCE_uB6 : ℝ), ((((((((z_1 ∈ (Set.univ : Set ℝ)) ∧ (r ∈ (Set.univ : Set ℝ))) ∧ (0 ≤ r)) ∧ (r ≤ a)) ∧ (v_uCE_uB6 ∈ (Set.univ : Set ℝ))) ∧ (0 ≤ v_uCE_uB6)) ∧ (v_uCE_uB6 ≤ h)) → ((u ((0 : ℝ), ((0 : ℝ), z_1))) = (((v_uCF_u81__0 * (∫ v_uCF_u86 in (0 : ℝ)..(2 * Real.pi), (1 : ℝ))) * (∫ v_uCE_uB6_1 in (0 : ℝ)..h, (1 : ℝ))) * (∫ r_1 in (0 : ℝ)..a, ((r_1 /. (Real.rpow ((r_1 ^ (2 : ℕ)) + ((v_uCE_uB6 - z_1) ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))))))))
  (h6 : (forall (z_1 : ℝ) (v_uCE_uB6 : ℝ), (((((z_1 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB6 ∈ (Set.univ : Set ℝ))) ∧ (0 ≤ v_uCE_uB6)) ∧ (v_uCE_uB6 ≤ h)) → ((u ((0 : ℝ), ((0 : ℝ), z_1))) = (((2 * Real.pi) * v_uCF_u81__0) * (∫ v_uCE_uB6_1 in (0 : ℝ)..h, (((Real.rpow ((a ^ (2 : ℕ)) + ((v_uCE_uB6_1 - z_1) ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) - (Real.rpow (((0 : ℕ) ^ (2 : ℕ)) + ((v_uCE_uB6_1 - z_1) ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))))))))
  (h7 : (forall (z_1 : ℝ) (v_uCE_uB6 : ℝ), (((((z_1 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB6 ∈ (Set.univ : Set ℝ))) ∧ (0 ≤ v_uCE_uB6)) ∧ (v_uCE_uB6 ≤ h)) → ((u ((0 : ℝ), ((0 : ℝ), z_1))) = (((2 * Real.pi) * v_uCF_u81__0) * (∫ v_uCE_uB6_1 in (0 : ℝ)..h, (((Real.rpow ((a ^ (2 : ℕ)) + ((v_uCE_uB6_1 - z_1) ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) - |((v_uCE_uB6_1 - z_1))|) * (1 : ℝ))))))))
  (h8 : F = (fun (t : ℝ) => (((((t - z) /. 2) * (Real.rpow ((a ^ (2 : ℕ)) + ((t - z) ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) + (((a ^ (2 : ℕ)) /. 2) * (Real.log ((t - z) + (Real.rpow ((a ^ (2 : ℕ)) + ((t - z) ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))))) - (((t - z) * |((t - z))|) /. 2))))
  : (forall (v_uCE_uB6 : ℝ), ((((v_uCE_uB6 ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ v_uCE_uB6)) ∧ (v_uCE_uB6 ≤ h)) → ((∫ v_uCE_uB6_1 in (0 : ℝ)..h, (((Real.rpow ((a ^ (2 : ℕ)) + ((v_uCE_uB6_1 - z) ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) - |((v_uCE_uB6_1 - z))|) * (1 : ℝ))) = ((F h) - (F (0 : ℝ)))))) := by
  sorry

theorem proof_gap_exercise_4157_5
  (u : (ℝ × (ℝ × ℝ) -> ℝ))
  (F : (ℝ -> ℝ))
  (a : ℝ)
  (h : ℝ)
  (v_uCF_u81__0 : ℝ)
  (z : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (h ∈ (Set.univ : Set ℝ)) ∧ (h > 0))
  (h3 : (v_uCF_u81__0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCF_u81__0 > 0))
  (h4 : z ∈ (Set.univ : Set ℝ))
  (h5 : (forall (z_1 : ℝ) (r : ℝ) (v_uCE_uB6 : ℝ), ((((((((z_1 ∈ (Set.univ : Set ℝ)) ∧ (r ∈ (Set.univ : Set ℝ))) ∧ (0 ≤ r)) ∧ (r ≤ a)) ∧ (v_uCE_uB6 ∈ (Set.univ : Set ℝ))) ∧ (0 ≤ v_uCE_uB6)) ∧ (v_uCE_uB6 ≤ h)) → ((u ((0 : ℝ), ((0 : ℝ), z_1))) = (((v_uCF_u81__0 * (∫ v_uCF_u86 in (0 : ℝ)..(2 * Real.pi), (1 : ℝ))) * (∫ v_uCE_uB6_1 in (0 : ℝ)..h, (1 : ℝ))) * (∫ r_1 in (0 : ℝ)..a, ((r_1 /. (Real.rpow ((r_1 ^ (2 : ℕ)) + ((v_uCE_uB6 - z_1) ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))))))))
  (h6 : (forall (z_1 : ℝ) (v_uCE_uB6 : ℝ), (((((z_1 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB6 ∈ (Set.univ : Set ℝ))) ∧ (0 ≤ v_uCE_uB6)) ∧ (v_uCE_uB6 ≤ h)) → ((u ((0 : ℝ), ((0 : ℝ), z_1))) = (((2 * Real.pi) * v_uCF_u81__0) * (∫ v_uCE_uB6_1 in (0 : ℝ)..h, (((Real.rpow ((a ^ (2 : ℕ)) + ((v_uCE_uB6_1 - z_1) ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) - (Real.rpow (((0 : ℕ) ^ (2 : ℕ)) + ((v_uCE_uB6_1 - z_1) ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))))))))
  (h7 : (forall (z_1 : ℝ) (v_uCE_uB6 : ℝ), (((((z_1 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB6 ∈ (Set.univ : Set ℝ))) ∧ (0 ≤ v_uCE_uB6)) ∧ (v_uCE_uB6 ≤ h)) → ((u ((0 : ℝ), ((0 : ℝ), z_1))) = (((2 * Real.pi) * v_uCF_u81__0) * (∫ v_uCE_uB6_1 in (0 : ℝ)..h, (((Real.rpow ((a ^ (2 : ℕ)) + ((v_uCE_uB6_1 - z_1) ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) - |((v_uCE_uB6_1 - z_1))|) * (1 : ℝ))))))))
  (h8 : F = (fun (t : ℝ) => (((((t - z) /. 2) * (Real.rpow ((a ^ (2 : ℕ)) + ((t - z) ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) + (((a ^ (2 : ℕ)) /. 2) * (Real.log ((t - z) + (Real.rpow ((a ^ (2 : ℕ)) + ((t - z) ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))))) - (((t - z) * |((t - z))|) /. 2))))
  (h9 : (forall (v_uCE_uB6 : ℝ), ((((v_uCE_uB6 ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ v_uCE_uB6)) ∧ (v_uCE_uB6 ≤ h)) → ((∫ v_uCE_uB6_1 in (0 : ℝ)..h, (((Real.rpow ((a ^ (2 : ℕ)) + ((v_uCE_uB6_1 - z) ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) - |((v_uCE_uB6_1 - z))|) * (1 : ℝ))) = ((F h) - (F (0 : ℝ)))))))
  : (u ((0 : ℝ), ((0 : ℝ), z))) = ((Real.pi * v_uCF_u81__0) * (((((h - z) * (Real.rpow ((a ^ (2 : ℕ)) + ((h - z) ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) + (z * (Real.rpow ((a ^ (2 : ℕ)) + (z ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) - (((h - z) * |((h - z))|) + (z * |(z)|))) + ((a ^ (2 : ℕ)) * (Real.log (((h - z) + (Real.rpow ((a ^ (2 : ℕ)) + ((h - z) ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) /. ((-z) + (Real.rpow ((a ^ (2 : ℕ)) + (z ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))))))) := by
  sorry

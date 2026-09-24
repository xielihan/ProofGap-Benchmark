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

-- exercise: exercise_3844

theorem proof_gap_exercise_3844_1
  (B : (ℝ × ℝ -> ℝ))
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ a)) → (((a ^ (2 : ℕ)) - (x ^ (2 : ℕ))) ≥ 0))) := by
  sorry

theorem proof_gap_exercise_3844_2
  (B : (ℝ × ℝ -> ℝ))
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ a)) → (((a ^ (2 : ℕ)) - (x ^ (2 : ℕ))) ≥ 0))))
  : (∫ x in (0 : ℝ)..a, (((x ^ (2 : ℕ)) * (Real.rpow ((a ^ (2 : ℕ)) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = ((a ^ (4 : ℕ)) * (∫ x in (0 : ℝ)..a, ((((x /. a) ^ (2 : ℕ)) * (Real.rpow (1 - ((x /. a) ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (deriv (fun (x : ℝ) => (x /. a)) x)))) := by
  sorry

theorem proof_gap_exercise_3844_3
  (B : (ℝ × ℝ -> ℝ))
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ a)) → (((a ^ (2 : ℕ)) - (x ^ (2 : ℕ))) ≥ 0))))
  (h3 : (∫ x in (0 : ℝ)..a, (((x ^ (2 : ℕ)) * (Real.rpow ((a ^ (2 : ℕ)) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = ((a ^ (4 : ℕ)) * (∫ x in (0 : ℝ)..a, ((((x /. a) ^ (2 : ℕ)) * (Real.rpow (1 - ((x /. a) ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (deriv (fun (x : ℝ) => (x /. a)) x)))))
  : (forall (u : ℝ) (x : ℝ), ((((((u ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (u = (x /. a))) ∧ (0 ≤ u)) ∧ (u ≤ 1)) → ((∫ x_1 in (0 : ℝ)..a, (((x_1 ^ (2 : ℕ)) * (Real.rpow ((a ^ (2 : ℕ)) - (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = ((a ^ (4 : ℕ)) * (∫ u_1 in (0 : ℝ)..(1 : ℝ), (((u_1 ^ (2 : ℕ)) * (Real.rpow (1 - (u_1 ^ (2 : ℕ))) (1 /. 2))) * (1 : ℝ))))))) := by
  sorry

theorem proof_gap_exercise_3844_4
  (B : (ℝ × ℝ -> ℝ))
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ a)) → (((a ^ (2 : ℕ)) - (x ^ (2 : ℕ))) ≥ 0))))
  (h3 : (∫ x in (0 : ℝ)..a, (((x ^ (2 : ℕ)) * (Real.rpow ((a ^ (2 : ℕ)) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = ((a ^ (4 : ℕ)) * (∫ x in (0 : ℝ)..a, ((((x /. a) ^ (2 : ℕ)) * (Real.rpow (1 - ((x /. a) ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (deriv (fun (x : ℝ) => (x /. a)) x)))))
  (h4 : (forall (u : ℝ) (x : ℝ), ((((((u ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (u = (x /. a))) ∧ (0 ≤ u)) ∧ (u ≤ 1)) → ((∫ x_1 in (0 : ℝ)..a, (((x_1 ^ (2 : ℕ)) * (Real.rpow ((a ^ (2 : ℕ)) - (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = ((a ^ (4 : ℕ)) * (∫ u_1 in (0 : ℝ)..(1 : ℝ), (((u_1 ^ (2 : ℕ)) * (Real.rpow (1 - (u_1 ^ (2 : ℕ))) (1 /. 2))) * (1 : ℝ))))))))
  : (∫ u in (0 : ℝ)..(1 : ℝ), (((u ^ (2 : ℕ)) * (Real.rpow (1 - (u ^ (2 : ℕ))) (1 /. 2))) * (1 : ℝ))) = ((1 /. 2) * (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t (1 /. 2)) * (Real.rpow (1 - t) (1 /. 2))) * (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_3844_5
  (B : (ℝ × ℝ -> ℝ))
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ a)) → (((a ^ (2 : ℕ)) - (x ^ (2 : ℕ))) ≥ 0))))
  (h3 : (∫ x in (0 : ℝ)..a, (((x ^ (2 : ℕ)) * (Real.rpow ((a ^ (2 : ℕ)) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = ((a ^ (4 : ℕ)) * (∫ x in (0 : ℝ)..a, ((((x /. a) ^ (2 : ℕ)) * (Real.rpow (1 - ((x /. a) ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (deriv (fun (x : ℝ) => (x /. a)) x)))))
  (h4 : (forall (u : ℝ) (x : ℝ), ((((((u ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (u = (x /. a))) ∧ (0 ≤ u)) ∧ (u ≤ 1)) → ((∫ x_1 in (0 : ℝ)..a, (((x_1 ^ (2 : ℕ)) * (Real.rpow ((a ^ (2 : ℕ)) - (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = ((a ^ (4 : ℕ)) * (∫ u_1 in (0 : ℝ)..(1 : ℝ), (((u_1 ^ (2 : ℕ)) * (Real.rpow (1 - (u_1 ^ (2 : ℕ))) (1 /. 2))) * (1 : ℝ))))))))
  (h5 : (∫ u in (0 : ℝ)..(1 : ℝ), (((u ^ (2 : ℕ)) * (Real.rpow (1 - (u ^ (2 : ℕ))) (1 /. 2))) * (1 : ℝ))) = ((1 /. 2) * (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t (1 /. 2)) * (Real.rpow (1 - t) (1 /. 2))) * (1 : ℝ)))))
  : (((a ^ (4 : ℕ)) /. 2) * (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t (1 /. 2)) * (Real.rpow (1 - t) (1 /. 2))) * (1 : ℝ)))) = (((a ^ (4 : ℕ)) /. 2) * (B ((3 /. 2), (3 /. 2)))) := by
  sorry

theorem proof_gap_exercise_3844_6
  (B : (ℝ × ℝ -> ℝ))
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ a)) → (((a ^ (2 : ℕ)) - (x ^ (2 : ℕ))) ≥ 0))))
  (h3 : (∫ x in (0 : ℝ)..a, (((x ^ (2 : ℕ)) * (Real.rpow ((a ^ (2 : ℕ)) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = ((a ^ (4 : ℕ)) * (∫ x in (0 : ℝ)..a, ((((x /. a) ^ (2 : ℕ)) * (Real.rpow (1 - ((x /. a) ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (deriv (fun (x : ℝ) => (x /. a)) x)))))
  (h4 : (forall (u : ℝ) (x : ℝ), ((((((u ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (u = (x /. a))) ∧ (0 ≤ u)) ∧ (u ≤ 1)) → ((∫ x_1 in (0 : ℝ)..a, (((x_1 ^ (2 : ℕ)) * (Real.rpow ((a ^ (2 : ℕ)) - (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = ((a ^ (4 : ℕ)) * (∫ u_1 in (0 : ℝ)..(1 : ℝ), (((u_1 ^ (2 : ℕ)) * (Real.rpow (1 - (u_1 ^ (2 : ℕ))) (1 /. 2))) * (1 : ℝ))))))))
  (h5 : (∫ u in (0 : ℝ)..(1 : ℝ), (((u ^ (2 : ℕ)) * (Real.rpow (1 - (u ^ (2 : ℕ))) (1 /. 2))) * (1 : ℝ))) = ((1 /. 2) * (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t (1 /. 2)) * (Real.rpow (1 - t) (1 /. 2))) * (1 : ℝ)))))
  (h6 : (((a ^ (4 : ℕ)) /. 2) * (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t (1 /. 2)) * (Real.rpow (1 - t) (1 /. 2))) * (1 : ℝ)))) = (((a ^ (4 : ℕ)) /. 2) * (B ((3 /. 2), (3 /. 2)))))
  : (((a ^ (4 : ℕ)) /. 2) * (B ((3 /. 2), (3 /. 2)))) = ((Real.pi * (a ^ (4 : ℕ))) /. 16) := by
  sorry

theorem proof_gap_exercise_3844_7
  (B : (ℝ × ℝ -> ℝ))
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ a)) → (((a ^ (2 : ℕ)) - (x ^ (2 : ℕ))) ≥ 0))))
  (h3 : (∫ x in (0 : ℝ)..a, (((x ^ (2 : ℕ)) * (Real.rpow ((a ^ (2 : ℕ)) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = ((a ^ (4 : ℕ)) * (∫ x in (0 : ℝ)..a, ((((x /. a) ^ (2 : ℕ)) * (Real.rpow (1 - ((x /. a) ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (deriv (fun (x : ℝ) => (x /. a)) x)))))
  (h4 : (forall (u : ℝ) (x : ℝ), ((((((u ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (u = (x /. a))) ∧ (0 ≤ u)) ∧ (u ≤ 1)) → ((∫ x_1 in (0 : ℝ)..a, (((x_1 ^ (2 : ℕ)) * (Real.rpow ((a ^ (2 : ℕ)) - (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = ((a ^ (4 : ℕ)) * (∫ u_1 in (0 : ℝ)..(1 : ℝ), (((u_1 ^ (2 : ℕ)) * (Real.rpow (1 - (u_1 ^ (2 : ℕ))) (1 /. 2))) * (1 : ℝ))))))))
  (h5 : (∫ u in (0 : ℝ)..(1 : ℝ), (((u ^ (2 : ℕ)) * (Real.rpow (1 - (u ^ (2 : ℕ))) (1 /. 2))) * (1 : ℝ))) = ((1 /. 2) * (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t (1 /. 2)) * (Real.rpow (1 - t) (1 /. 2))) * (1 : ℝ)))))
  (h6 : (((a ^ (4 : ℕ)) /. 2) * (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t (1 /. 2)) * (Real.rpow (1 - t) (1 /. 2))) * (1 : ℝ)))) = (((a ^ (4 : ℕ)) /. 2) * (B ((3 /. 2), (3 /. 2)))))
  (h7 : (((a ^ (4 : ℕ)) /. 2) * (B ((3 /. 2), (3 /. 2)))) = ((Real.pi * (a ^ (4 : ℕ))) /. 16))
  : (((a ^ (4 : ℕ)) /. 2) * (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t (1 /. 2)) * (Real.rpow (1 - t) (1 /. 2))) * (1 : ℝ)))) = ((Real.pi * (a ^ (4 : ℕ))) /. 16) := by
  sorry

theorem proof_gap_exercise_3844_8
  (B : (ℝ × ℝ -> ℝ))
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ a)) → (((a ^ (2 : ℕ)) - (x ^ (2 : ℕ))) ≥ 0))))
  (h3 : (∫ x in (0 : ℝ)..a, (((x ^ (2 : ℕ)) * (Real.rpow ((a ^ (2 : ℕ)) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = ((a ^ (4 : ℕ)) * (∫ x in (0 : ℝ)..a, ((((x /. a) ^ (2 : ℕ)) * (Real.rpow (1 - ((x /. a) ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (deriv (fun (x : ℝ) => (x /. a)) x)))))
  (h4 : (forall (u : ℝ) (x : ℝ), ((((((u ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (u = (x /. a))) ∧ (0 ≤ u)) ∧ (u ≤ 1)) → ((∫ x_1 in (0 : ℝ)..a, (((x_1 ^ (2 : ℕ)) * (Real.rpow ((a ^ (2 : ℕ)) - (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = ((a ^ (4 : ℕ)) * (∫ u_1 in (0 : ℝ)..(1 : ℝ), (((u_1 ^ (2 : ℕ)) * (Real.rpow (1 - (u_1 ^ (2 : ℕ))) (1 /. 2))) * (1 : ℝ))))))))
  (h5 : (∫ u in (0 : ℝ)..(1 : ℝ), (((u ^ (2 : ℕ)) * (Real.rpow (1 - (u ^ (2 : ℕ))) (1 /. 2))) * (1 : ℝ))) = ((1 /. 2) * (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t (1 /. 2)) * (Real.rpow (1 - t) (1 /. 2))) * (1 : ℝ)))))
  (h6 : (((a ^ (4 : ℕ)) /. 2) * (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t (1 /. 2)) * (Real.rpow (1 - t) (1 /. 2))) * (1 : ℝ)))) = (((a ^ (4 : ℕ)) /. 2) * (B ((3 /. 2), (3 /. 2)))))
  (h7 : (((a ^ (4 : ℕ)) /. 2) * (B ((3 /. 2), (3 /. 2)))) = ((Real.pi * (a ^ (4 : ℕ))) /. 16))
  (h8 : (((a ^ (4 : ℕ)) /. 2) * (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t (1 /. 2)) * (Real.rpow (1 - t) (1 /. 2))) * (1 : ℝ)))) = ((Real.pi * (a ^ (4 : ℕ))) /. 16))
  : (∫ x in (0 : ℝ)..a, (((x ^ (2 : ℕ)) * (Real.rpow ((a ^ (2 : ℕ)) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = ((Real.pi * (a ^ (4 : ℕ))) /. 16) := by
  sorry

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

-- exercise: exercise_4121

theorem proof_gap_exercise_4121_1
  (x : (ℝ × (ℝ × ℝ) -> ℝ))
  (y : (ℝ × (ℝ × ℝ) -> ℝ))
  (z : (ℝ × (ℝ × ℝ) -> ℝ))
  (a : ℝ)
  (Vol : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : S ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h3 : V ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h4 : Vol ∈ (Set.univ : Set ℝ))
  (h5 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (y_1 : ℝ), ((y_1 ∈ (Set.univ : Set ℝ)) → (forall (z_1 : ℝ), ((z_1 ∈ (Set.univ : Set ℝ)) → (S = ({p : ℝ × (ℝ × ℝ) | (((((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2.1 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ∈ (Set.univ : Set ℝ))) ∧ (((((p.1 ^ (2 : ℕ)) + (p.2.1 ^ (2 : ℕ))) + (p.2.2 ^ (2 : ℕ))) ^ (3 : ℕ)) = (((a ^ (6 : ℕ)) * (p.2.2 ^ (2 : ℕ))) /. ((p.1 ^ (2 : ℕ)) + (p.2.1 ^ (2 : ℕ)))))) ∧ (((p.1 ^ (2 : ℕ)) + (p.2.1 ^ (2 : ℕ))) ≠ 0))})))))))))
  (h6 : (forall (r : ℝ), ((r ∈ (Set.univ : Set ℝ)) → (forall (v_uCF_u86 : ℝ), ((v_uCF_u86 ∈ (Set.univ : Set ℝ)) → (forall (v_uCF_u88 : ℝ), ((v_uCF_u88 ∈ (Set.univ : Set ℝ)) → ((x (r, (v_uCF_u86, v_uCF_u88))) = ((r * (Real.cos v_uCF_u86)) * (Real.cos v_uCF_u88))))))))))
  (h7 : (forall (r : ℝ), ((r ∈ (Set.univ : Set ℝ)) → (forall (v_uCF_u86 : ℝ), ((v_uCF_u86 ∈ (Set.univ : Set ℝ)) → (forall (v_uCF_u88 : ℝ), ((v_uCF_u88 ∈ (Set.univ : Set ℝ)) → ((y (r, (v_uCF_u86, v_uCF_u88))) = ((r * (Real.sin v_uCF_u86)) * (Real.cos v_uCF_u88))))))))))
  (h8 : (forall (r : ℝ), ((r ∈ (Set.univ : Set ℝ)) → (forall (v_uCF_u86 : ℝ), ((v_uCF_u86 ∈ (Set.univ : Set ℝ)) → (forall (v_uCF_u88 : ℝ), ((v_uCF_u88 ∈ (Set.univ : Set ℝ)) → ((z (r, (v_uCF_u86, v_uCF_u88))) = (r * (Real.sin v_uCF_u88))))))))))
  : (forall (r : ℝ), ((r ∈ (Set.univ : Set ℝ)) → (r ≥ 0))) := by
  sorry

theorem proof_gap_exercise_4121_2
  (x : (ℝ × (ℝ × ℝ) -> ℝ))
  (y : (ℝ × (ℝ × ℝ) -> ℝ))
  (z : (ℝ × (ℝ × ℝ) -> ℝ))
  (a : ℝ)
  (Vol : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : S ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h3 : V ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h4 : Vol ∈ (Set.univ : Set ℝ))
  (h5 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (y_1 : ℝ), ((y_1 ∈ (Set.univ : Set ℝ)) → (forall (z_1 : ℝ), ((z_1 ∈ (Set.univ : Set ℝ)) → (S = ({p : ℝ × (ℝ × ℝ) | (((((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2.1 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ∈ (Set.univ : Set ℝ))) ∧ (((((p.1 ^ (2 : ℕ)) + (p.2.1 ^ (2 : ℕ))) + (p.2.2 ^ (2 : ℕ))) ^ (3 : ℕ)) = (((a ^ (6 : ℕ)) * (p.2.2 ^ (2 : ℕ))) /. ((p.1 ^ (2 : ℕ)) + (p.2.1 ^ (2 : ℕ)))))) ∧ (((p.1 ^ (2 : ℕ)) + (p.2.1 ^ (2 : ℕ))) ≠ 0))})))))))))
  (h6 : (forall (r : ℝ), ((r ∈ (Set.univ : Set ℝ)) → (forall (v_uCF_u86 : ℝ), ((v_uCF_u86 ∈ (Set.univ : Set ℝ)) → (forall (v_uCF_u88 : ℝ), ((v_uCF_u88 ∈ (Set.univ : Set ℝ)) → ((x (r, (v_uCF_u86, v_uCF_u88))) = ((r * (Real.cos v_uCF_u86)) * (Real.cos v_uCF_u88))))))))))
  (h7 : (forall (r : ℝ), ((r ∈ (Set.univ : Set ℝ)) → (forall (v_uCF_u86 : ℝ), ((v_uCF_u86 ∈ (Set.univ : Set ℝ)) → (forall (v_uCF_u88 : ℝ), ((v_uCF_u88 ∈ (Set.univ : Set ℝ)) → ((y (r, (v_uCF_u86, v_uCF_u88))) = ((r * (Real.sin v_uCF_u86)) * (Real.cos v_uCF_u88))))))))))
  (h8 : (forall (r : ℝ), ((r ∈ (Set.univ : Set ℝ)) → (forall (v_uCF_u86 : ℝ), ((v_uCF_u86 ∈ (Set.univ : Set ℝ)) → (forall (v_uCF_u88 : ℝ), ((v_uCF_u88 ∈ (Set.univ : Set ℝ)) → ((z (r, (v_uCF_u86, v_uCF_u88))) = (r * (Real.sin v_uCF_u88))))))))))
  (h9 : (forall (r : ℝ), ((r ∈ (Set.univ : Set ℝ)) → (r ≥ 0))))
  : V = ({p : ℝ × (ℝ × ℝ) | (((((((((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2.1 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ∈ (Set.univ : Set ℝ))) ∧ (0 ≤ p.2.1)) ∧ (p.2.1 ≤ (Real.pi /. 2))) ∧ (0 ≤ p.2.2)) ∧ (p.2.2 ≤ (Real.pi /. 2))) ∧ (0 ≤ p.1)) ∧ (p.1 ≤ (a * (Real.rpow (Real.tan p.2.2) (1 /. 3)))))}) := by
  sorry

theorem proof_gap_exercise_4121_3
  (x : (ℝ × (ℝ × ℝ) -> ℝ))
  (y : (ℝ × (ℝ × ℝ) -> ℝ))
  (z : (ℝ × (ℝ × ℝ) -> ℝ))
  (a : ℝ)
  (Vol : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : S ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h3 : V ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h4 : Vol ∈ (Set.univ : Set ℝ))
  (h5 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (y_1 : ℝ), ((y_1 ∈ (Set.univ : Set ℝ)) → (forall (z_1 : ℝ), ((z_1 ∈ (Set.univ : Set ℝ)) → (S = ({p : ℝ × (ℝ × ℝ) | (((((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2.1 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ∈ (Set.univ : Set ℝ))) ∧ (((((p.1 ^ (2 : ℕ)) + (p.2.1 ^ (2 : ℕ))) + (p.2.2 ^ (2 : ℕ))) ^ (3 : ℕ)) = (((a ^ (6 : ℕ)) * (p.2.2 ^ (2 : ℕ))) /. ((p.1 ^ (2 : ℕ)) + (p.2.1 ^ (2 : ℕ)))))) ∧ (((p.1 ^ (2 : ℕ)) + (p.2.1 ^ (2 : ℕ))) ≠ 0))})))))))))
  (h6 : (forall (r : ℝ), ((r ∈ (Set.univ : Set ℝ)) → (forall (v_uCF_u86 : ℝ), ((v_uCF_u86 ∈ (Set.univ : Set ℝ)) → (forall (v_uCF_u88 : ℝ), ((v_uCF_u88 ∈ (Set.univ : Set ℝ)) → ((x (r, (v_uCF_u86, v_uCF_u88))) = ((r * (Real.cos v_uCF_u86)) * (Real.cos v_uCF_u88))))))))))
  (h7 : (forall (r : ℝ), ((r ∈ (Set.univ : Set ℝ)) → (forall (v_uCF_u86 : ℝ), ((v_uCF_u86 ∈ (Set.univ : Set ℝ)) → (forall (v_uCF_u88 : ℝ), ((v_uCF_u88 ∈ (Set.univ : Set ℝ)) → ((y (r, (v_uCF_u86, v_uCF_u88))) = ((r * (Real.sin v_uCF_u86)) * (Real.cos v_uCF_u88))))))))))
  (h8 : (forall (r : ℝ), ((r ∈ (Set.univ : Set ℝ)) → (forall (v_uCF_u86 : ℝ), ((v_uCF_u86 ∈ (Set.univ : Set ℝ)) → (forall (v_uCF_u88 : ℝ), ((v_uCF_u88 ∈ (Set.univ : Set ℝ)) → ((z (r, (v_uCF_u86, v_uCF_u88))) = (r * (Real.sin v_uCF_u88))))))))))
  (h9 : (forall (r : ℝ), ((r ∈ (Set.univ : Set ℝ)) → (r ≥ 0))))
  (h10 : V = ({p : ℝ × (ℝ × ℝ) | (((((((((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2.1 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ∈ (Set.univ : Set ℝ))) ∧ (0 ≤ p.2.1)) ∧ (p.2.1 ≤ (Real.pi /. 2))) ∧ (0 ≤ p.2.2)) ∧ (p.2.2 ≤ (Real.pi /. 2))) ∧ (0 ≤ p.1)) ∧ (p.1 ≤ (a * (Real.rpow (Real.tan p.2.2) (1 /. 3)))))}))
  : Vol = (8 * (∫ v_uCF_u86 in (0 : ℝ)..(Real.pi /. 2), ((∫ v_uCF_u88 in (0 : ℝ)..(Real.pi /. 2), ((∫ r in (0 : ℝ)..(a * (Real.rpow (Real.tan v_uCF_u88) (1 /. 3))), (((r ^ (2 : ℕ)) * (Real.cos v_uCF_u88)) * (1 : ℝ))) * (1 : ℝ))) * (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_4121_4
  (x : (ℝ × (ℝ × ℝ) -> ℝ))
  (y : (ℝ × (ℝ × ℝ) -> ℝ))
  (z : (ℝ × (ℝ × ℝ) -> ℝ))
  (a : ℝ)
  (Vol : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : S ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h3 : V ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h4 : Vol ∈ (Set.univ : Set ℝ))
  (h5 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (y_1 : ℝ), ((y_1 ∈ (Set.univ : Set ℝ)) → (forall (z_1 : ℝ), ((z_1 ∈ (Set.univ : Set ℝ)) → (S = ({p : ℝ × (ℝ × ℝ) | (((((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2.1 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ∈ (Set.univ : Set ℝ))) ∧ (((((p.1 ^ (2 : ℕ)) + (p.2.1 ^ (2 : ℕ))) + (p.2.2 ^ (2 : ℕ))) ^ (3 : ℕ)) = (((a ^ (6 : ℕ)) * (p.2.2 ^ (2 : ℕ))) /. ((p.1 ^ (2 : ℕ)) + (p.2.1 ^ (2 : ℕ)))))) ∧ (((p.1 ^ (2 : ℕ)) + (p.2.1 ^ (2 : ℕ))) ≠ 0))})))))))))
  (h6 : (forall (r : ℝ), ((r ∈ (Set.univ : Set ℝ)) → (forall (v_uCF_u86 : ℝ), ((v_uCF_u86 ∈ (Set.univ : Set ℝ)) → (forall (v_uCF_u88 : ℝ), ((v_uCF_u88 ∈ (Set.univ : Set ℝ)) → ((x (r, (v_uCF_u86, v_uCF_u88))) = ((r * (Real.cos v_uCF_u86)) * (Real.cos v_uCF_u88))))))))))
  (h7 : (forall (r : ℝ), ((r ∈ (Set.univ : Set ℝ)) → (forall (v_uCF_u86 : ℝ), ((v_uCF_u86 ∈ (Set.univ : Set ℝ)) → (forall (v_uCF_u88 : ℝ), ((v_uCF_u88 ∈ (Set.univ : Set ℝ)) → ((y (r, (v_uCF_u86, v_uCF_u88))) = ((r * (Real.sin v_uCF_u86)) * (Real.cos v_uCF_u88))))))))))
  (h8 : (forall (r : ℝ), ((r ∈ (Set.univ : Set ℝ)) → (forall (v_uCF_u86 : ℝ), ((v_uCF_u86 ∈ (Set.univ : Set ℝ)) → (forall (v_uCF_u88 : ℝ), ((v_uCF_u88 ∈ (Set.univ : Set ℝ)) → ((z (r, (v_uCF_u86, v_uCF_u88))) = (r * (Real.sin v_uCF_u88))))))))))
  (h9 : (forall (r : ℝ), ((r ∈ (Set.univ : Set ℝ)) → (r ≥ 0))))
  (h10 : V = ({p : ℝ × (ℝ × ℝ) | (((((((((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2.1 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ∈ (Set.univ : Set ℝ))) ∧ (0 ≤ p.2.1)) ∧ (p.2.1 ≤ (Real.pi /. 2))) ∧ (0 ≤ p.2.2)) ∧ (p.2.2 ≤ (Real.pi /. 2))) ∧ (0 ≤ p.1)) ∧ (p.1 ≤ (a * (Real.rpow (Real.tan p.2.2) (1 /. 3)))))}))
  (h11 : Vol = (8 * (∫ v_uCF_u86 in (0 : ℝ)..(Real.pi /. 2), ((∫ v_uCF_u88 in (0 : ℝ)..(Real.pi /. 2), ((∫ r in (0 : ℝ)..(a * (Real.rpow (Real.tan v_uCF_u88) (1 /. 3))), (((r ^ (2 : ℕ)) * (Real.cos v_uCF_u88)) * (1 : ℝ))) * (1 : ℝ))) * (1 : ℝ)))))
  : Vol = ((((4 * Real.pi) * (a ^ (3 : ℕ))) /. 3) * (∫ v_uCF_u88 in (0 : ℝ)..(Real.pi /. 2), ((Real.sin v_uCF_u88) * (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_4121_5
  (x : (ℝ × (ℝ × ℝ) -> ℝ))
  (y : (ℝ × (ℝ × ℝ) -> ℝ))
  (z : (ℝ × (ℝ × ℝ) -> ℝ))
  (a : ℝ)
  (Vol : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : S ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h3 : V ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h4 : Vol ∈ (Set.univ : Set ℝ))
  (h5 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (y_1 : ℝ), ((y_1 ∈ (Set.univ : Set ℝ)) → (forall (z_1 : ℝ), ((z_1 ∈ (Set.univ : Set ℝ)) → (S = ({p : ℝ × (ℝ × ℝ) | (((((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2.1 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ∈ (Set.univ : Set ℝ))) ∧ (((((p.1 ^ (2 : ℕ)) + (p.2.1 ^ (2 : ℕ))) + (p.2.2 ^ (2 : ℕ))) ^ (3 : ℕ)) = (((a ^ (6 : ℕ)) * (p.2.2 ^ (2 : ℕ))) /. ((p.1 ^ (2 : ℕ)) + (p.2.1 ^ (2 : ℕ)))))) ∧ (((p.1 ^ (2 : ℕ)) + (p.2.1 ^ (2 : ℕ))) ≠ 0))})))))))))
  (h6 : (forall (r : ℝ), ((r ∈ (Set.univ : Set ℝ)) → (forall (v_uCF_u86 : ℝ), ((v_uCF_u86 ∈ (Set.univ : Set ℝ)) → (forall (v_uCF_u88 : ℝ), ((v_uCF_u88 ∈ (Set.univ : Set ℝ)) → ((x (r, (v_uCF_u86, v_uCF_u88))) = ((r * (Real.cos v_uCF_u86)) * (Real.cos v_uCF_u88))))))))))
  (h7 : (forall (r : ℝ), ((r ∈ (Set.univ : Set ℝ)) → (forall (v_uCF_u86 : ℝ), ((v_uCF_u86 ∈ (Set.univ : Set ℝ)) → (forall (v_uCF_u88 : ℝ), ((v_uCF_u88 ∈ (Set.univ : Set ℝ)) → ((y (r, (v_uCF_u86, v_uCF_u88))) = ((r * (Real.sin v_uCF_u86)) * (Real.cos v_uCF_u88))))))))))
  (h8 : (forall (r : ℝ), ((r ∈ (Set.univ : Set ℝ)) → (forall (v_uCF_u86 : ℝ), ((v_uCF_u86 ∈ (Set.univ : Set ℝ)) → (forall (v_uCF_u88 : ℝ), ((v_uCF_u88 ∈ (Set.univ : Set ℝ)) → ((z (r, (v_uCF_u86, v_uCF_u88))) = (r * (Real.sin v_uCF_u88))))))))))
  (h9 : (forall (r : ℝ), ((r ∈ (Set.univ : Set ℝ)) → (r ≥ 0))))
  (h10 : V = ({p : ℝ × (ℝ × ℝ) | (((((((((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2.1 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ∈ (Set.univ : Set ℝ))) ∧ (0 ≤ p.2.1)) ∧ (p.2.1 ≤ (Real.pi /. 2))) ∧ (0 ≤ p.2.2)) ∧ (p.2.2 ≤ (Real.pi /. 2))) ∧ (0 ≤ p.1)) ∧ (p.1 ≤ (a * (Real.rpow (Real.tan p.2.2) (1 /. 3)))))}))
  (h11 : Vol = (8 * (∫ v_uCF_u86 in (0 : ℝ)..(Real.pi /. 2), ((∫ v_uCF_u88 in (0 : ℝ)..(Real.pi /. 2), ((∫ r in (0 : ℝ)..(a * (Real.rpow (Real.tan v_uCF_u88) (1 /. 3))), (((r ^ (2 : ℕ)) * (Real.cos v_uCF_u88)) * (1 : ℝ))) * (1 : ℝ))) * (1 : ℝ)))))
  (h12 : Vol = ((((4 * Real.pi) * (a ^ (3 : ℕ))) /. 3) * (∫ v_uCF_u88 in (0 : ℝ)..(Real.pi /. 2), ((Real.sin v_uCF_u88) * (1 : ℝ)))))
  : Vol = (((4 * Real.pi) * (a ^ (3 : ℕ))) /. 3) := by
  sorry

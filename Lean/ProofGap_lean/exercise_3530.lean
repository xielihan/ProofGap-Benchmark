import Mathlib

attribute [local instance] Classical.propDecidable

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

-- exercise: exercise_3530

theorem proof_gap_exercise_3530_1
  (M : (ℝ × (ℝ × ℝ)))
  (h1 : C ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h2 : M ∈ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h3 : L ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h4 : P ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h5 : M = (1, 1, 1))
  (h6 : (forall (X : ℝ) (Y : ℝ) (Z : ℝ), ((((X ∈ (Set.univ : Set ℝ)) ∧ (Y ∈ (Set.univ : Set ℝ))) ∧ (Z ∈ (Set.univ : Set ℝ))) → (((X, Y, Z) ∈ C) ↔ ((Y = X) ∧ (Z = (X ^ (2 : ℕ))))))))
  (h7 : x = (fun (t : ℝ) => t))
  (h8 : y = (fun (t : ℝ) => t))
  (h9 : z = (fun (t : ℝ) => (t ^ (2 : ℕ))))
  : ((x 1), (y 1), (z 1)) = (1, 1, 1) := by
  sorry

theorem proof_gap_exercise_3530_2
  (M : (ℝ × (ℝ × ℝ)))
  (h1 : C ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h2 : M ∈ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h3 : L ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h4 : P ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h5 : M = (1, 1, 1))
  (h6 : (forall (X : ℝ) (Y : ℝ) (Z : ℝ), ((((X ∈ (Set.univ : Set ℝ)) ∧ (Y ∈ (Set.univ : Set ℝ))) ∧ (Z ∈ (Set.univ : Set ℝ))) → (((X, Y, Z) ∈ C) ↔ ((Y = X) ∧ (Z = (X ^ (2 : ℕ))))))))
  (h7 : x = (fun (t : ℝ) => t))
  (h8 : y = (fun (t : ℝ) => t))
  (h9 : z = (fun (t : ℝ) => (t ^ (2 : ℕ))))
  (h10 : ((x 1), (y 1), (z 1)) = (1, 1, 1))
  (h11 : v = ((iteratedDeriv 1 (fun t_1 => x t_1) 1), (iteratedDeriv 1 (fun t_1 => y t_1) 1), (iteratedDeriv 1 (fun t_1 => z t_1) 1)))
  : v = (1, 1, 2) := by
  sorry

theorem proof_gap_exercise_3530_3
  (M : (ℝ × (ℝ × ℝ)))
  (h1 : C ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h2 : M ∈ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h3 : L ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h4 : P ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h5 : M = (1, 1, 1))
  (h6 : (forall (X : ℝ) (Y : ℝ) (Z : ℝ), ((((X ∈ (Set.univ : Set ℝ)) ∧ (Y ∈ (Set.univ : Set ℝ))) ∧ (Z ∈ (Set.univ : Set ℝ))) → (((X, Y, Z) ∈ C) ↔ ((Y = X) ∧ (Z = (X ^ (2 : ℕ))))))))
  (h7 : x = (fun (t : ℝ) => t))
  (h8 : y = (fun (t : ℝ) => t))
  (h9 : z = (fun (t : ℝ) => (t ^ (2 : ℕ))))
  (h10 : ((x 1), (y 1), (z 1)) = (1, 1, 1))
  (h11 : v = ((iteratedDeriv 1 (fun t_1 => x t_1) 1), (iteratedDeriv 1 (fun t_1 => y t_1) 1), (iteratedDeriv 1 (fun t_1 => z t_1) 1)))
  (h12 : v = (1, 1, 2))
  : L = ({p : ℝ × (ℝ × ℝ) | (((((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2.1 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ∈ (Set.univ : Set ℝ))) ∧ (((p.1 - 1) /. 1) = ((p.2.1 - 1) /. 1))) ∧ (((p.2.1 - 1) /. 1) = ((p.2.2 - 1) /. 2)))}) := by
  sorry

theorem proof_gap_exercise_3530_4
  (M : (ℝ × (ℝ × ℝ)))
  (h1 : C ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h2 : M ∈ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h3 : L ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h4 : P ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h5 : M = (1, 1, 1))
  (h6 : (forall (X : ℝ) (Y : ℝ) (Z : ℝ), ((((X ∈ (Set.univ : Set ℝ)) ∧ (Y ∈ (Set.univ : Set ℝ))) ∧ (Z ∈ (Set.univ : Set ℝ))) → (((X, Y, Z) ∈ C) ↔ ((Y = X) ∧ (Z = (X ^ (2 : ℕ))))))))
  (h7 : x = (fun (t : ℝ) => t))
  (h8 : y = (fun (t : ℝ) => t))
  (h9 : z = (fun (t : ℝ) => (t ^ (2 : ℕ))))
  (h10 : ((x 1), (y 1), (z 1)) = (1, 1, 1))
  (h11 : v = ((iteratedDeriv 1 (fun t_1 => x t_1) 1), (iteratedDeriv 1 (fun t_1 => y t_1) 1), (iteratedDeriv 1 (fun t_1 => z t_1) 1)))
  (h12 : v = (1, 1, 2))
  (h13 : L = ({p : ℝ × (ℝ × ℝ) | (((((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2.1 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ∈ (Set.univ : Set ℝ))) ∧ (((p.1 - 1) /. 1) = ((p.2.1 - 1) /. 1))) ∧ (((p.2.1 - 1) /. 1) = ((p.2.2 - 1) /. 2)))}))
  : P = ({p : ℝ × (ℝ × ℝ) | ((((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2.1 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ∈ (Set.univ : Set ℝ))) ∧ (((((p.1 - 1) + p.2.1) - 1) + (2 * (p.2.2 - 1))) = 0))}) := by
  sorry

theorem proof_gap_exercise_3530_5
  (M : (ℝ × (ℝ × ℝ)))
  (h1 : C ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h2 : M ∈ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h3 : L ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h4 : P ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h5 : M = (1, 1, 1))
  (h6 : (forall (X : ℝ) (Y : ℝ) (Z : ℝ), ((((X ∈ (Set.univ : Set ℝ)) ∧ (Y ∈ (Set.univ : Set ℝ))) ∧ (Z ∈ (Set.univ : Set ℝ))) → (((X, Y, Z) ∈ C) ↔ ((Y = X) ∧ (Z = (X ^ (2 : ℕ))))))))
  (h7 : x = (fun (t : ℝ) => t))
  (h8 : y = (fun (t : ℝ) => t))
  (h9 : z = (fun (t : ℝ) => (t ^ (2 : ℕ))))
  (h10 : ((x 1), (y 1), (z 1)) = (1, 1, 1))
  (h11 : v = ((iteratedDeriv 1 (fun t_1 => x t_1) 1), (iteratedDeriv 1 (fun t_1 => y t_1) 1), (iteratedDeriv 1 (fun t_1 => z t_1) 1)))
  (h12 : v = (1, 1, 2))
  (h13 : L = ({p : ℝ × (ℝ × ℝ) | (((((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2.1 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ∈ (Set.univ : Set ℝ))) ∧ (((p.1 - 1) /. 1) = ((p.2.1 - 1) /. 1))) ∧ (((p.2.1 - 1) /. 1) = ((p.2.2 - 1) /. 2)))}))
  (h14 : P = ({p : ℝ × (ℝ × ℝ) | ((((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2.1 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ∈ (Set.univ : Set ℝ))) ∧ (((((p.1 - 1) + p.2.1) - 1) + (2 * (p.2.2 - 1))) = 0))}))
  : P = ({p : ℝ × (ℝ × ℝ) | ((((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2.1 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ∈ (Set.univ : Set ℝ))) ∧ (((p.1 + p.2.1) + (2 * p.2.2)) = 4))}) := by
  sorry

theorem proof_gap_exercise_3530_6
  (M : (ℝ × (ℝ × ℝ)))
  (h1 : C ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h2 : M ∈ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h3 : L ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h4 : P ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h5 : M = (1, 1, 1))
  (h6 : (forall (X : ℝ) (Y : ℝ) (Z : ℝ), ((((X ∈ (Set.univ : Set ℝ)) ∧ (Y ∈ (Set.univ : Set ℝ))) ∧ (Z ∈ (Set.univ : Set ℝ))) → (((X, Y, Z) ∈ C) ↔ ((Y = X) ∧ (Z = (X ^ (2 : ℕ))))))))
  (h7 : x = (fun (t : ℝ) => t))
  (h8 : y = (fun (t : ℝ) => t))
  (h9 : z = (fun (t : ℝ) => (t ^ (2 : ℕ))))
  (h10 : ((x 1), (y 1), (z 1)) = (1, 1, 1))
  (h11 : v = ((iteratedDeriv 1 (fun t_1 => x t_1) 1), (iteratedDeriv 1 (fun t_1 => y t_1) 1), (iteratedDeriv 1 (fun t_1 => z t_1) 1)))
  (h12 : v = (1, 1, 2))
  (h13 : L = ({p : ℝ × (ℝ × ℝ) | (((((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2.1 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ∈ (Set.univ : Set ℝ))) ∧ (((p.1 - 1) /. 1) = ((p.2.1 - 1) /. 1))) ∧ (((p.2.1 - 1) /. 1) = ((p.2.2 - 1) /. 2)))}))
  (h14 : P = ({p : ℝ × (ℝ × ℝ) | ((((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2.1 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ∈ (Set.univ : Set ℝ))) ∧ (((((p.1 - 1) + p.2.1) - 1) + (2 * (p.2.2 - 1))) = 0))}))
  (h15 : P = ({p : ℝ × (ℝ × ℝ) | ((((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2.1 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ∈ (Set.univ : Set ℝ))) ∧ (((p.1 + p.2.1) + (2 * p.2.2)) = 4))}))
  : ((L = ({p : ℝ × (ℝ × ℝ) | (((((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2.1 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ∈ (Set.univ : Set ℝ))) ∧ (((p.1 - 1) /. 1) = ((p.2.1 - 1) /. 1))) ∧ (((p.2.1 - 1) /. 1) = ((p.2.2 - 1) /. 2)))})) ∧ (P = ({p : ℝ × (ℝ × ℝ) | ((((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2.1 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ∈ (Set.univ : Set ℝ))) ∧ (((p.1 + p.2.1) + (2 * p.2.2)) = 4))}))) → ((M ∈ L) ∧ (M ∈ P)) := by
  sorry

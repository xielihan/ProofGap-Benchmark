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

-- exercise: exercise_1140

theorem proof_gap_exercise_1140_1
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (h1 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((x t) = ((2 * t) - (t ^ (2 : ℕ)))))))
  (h2 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((y t) = ((3 * t) - (t ^ (3 : ℕ)))))))
  : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((lpFunDeri y x) t) = ((iteratedDeriv 1 (fun t_1 => y t_1) t) /. (iteratedDeriv 1 (fun t_1 => x t_1) t))))) := by
  sorry

theorem proof_gap_exercise_1140_2
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (h1 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((x t) = ((2 * t) - (t ^ (2 : ℕ)))))))
  (h2 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((y t) = ((3 * t) - (t ^ (3 : ℕ)))))))
  (h3 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((lpFunDeri y x) t) = ((iteratedDeriv 1 (fun t_1 => y t_1) t) /. (iteratedDeriv 1 (fun t_1 => x t_1) t))))))
  : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((iteratedDeriv 1 (fun t_1 => y t_1) t) /. (iteratedDeriv 1 (fun t_1 => x t_1) t)) = ((3 - (3 * (t ^ (2 : ℕ)))) /. (2 - (2 * t)))))) := by
  sorry

theorem proof_gap_exercise_1140_3
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (h1 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((x t) = ((2 * t) - (t ^ (2 : ℕ)))))))
  (h2 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((y t) = ((3 * t) - (t ^ (3 : ℕ)))))))
  (h3 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((lpFunDeri y x) t) = ((iteratedDeriv 1 (fun t_1 => y t_1) t) /. (iteratedDeriv 1 (fun t_1 => x t_1) t))))))
  (h4 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((iteratedDeriv 1 (fun t_1 => y t_1) t) /. (iteratedDeriv 1 (fun t_1 => x t_1) t)) = ((3 - (3 * (t ^ (2 : ℕ)))) /. (2 - (2 * t)))))))
  : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((3 - (3 * (t ^ (2 : ℕ)))) /. (2 - (2 * t))) = ((3 /. 2) * (t + 1))))) := by
  sorry

theorem proof_gap_exercise_1140_4
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (h1 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((x t) = ((2 * t) - (t ^ (2 : ℕ)))))))
  (h2 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((y t) = ((3 * t) - (t ^ (3 : ℕ)))))))
  (h3 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((lpFunDeri y x) t) = ((iteratedDeriv 1 (fun t_1 => y t_1) t) /. (iteratedDeriv 1 (fun t_1 => x t_1) t))))))
  (h4 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((iteratedDeriv 1 (fun t_1 => y t_1) t) /. (iteratedDeriv 1 (fun t_1 => x t_1) t)) = ((3 - (3 * (t ^ (2 : ℕ)))) /. (2 - (2 * t)))))))
  (h5 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((3 - (3 * (t ^ (2 : ℕ)))) /. (2 - (2 * t))) = ((3 /. 2) * (t + 1))))))
  : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((lpFunDeri y x) t) = ((3 /. 2) * (t + 1))))) := by
  sorry

theorem proof_gap_exercise_1140_5
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (h1 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((x t) = ((2 * t) - (t ^ (2 : ℕ)))))))
  (h2 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((y t) = ((3 * t) - (t ^ (3 : ℕ)))))))
  (h3 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((lpFunDeri y x) t) = ((iteratedDeriv 1 (fun t_1 => y t_1) t) /. (iteratedDeriv 1 (fun t_1 => x t_1) t))))))
  (h4 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((iteratedDeriv 1 (fun t_1 => y t_1) t) /. (iteratedDeriv 1 (fun t_1 => x t_1) t)) = ((3 - (3 * (t ^ (2 : ℕ)))) /. (2 - (2 * t)))))))
  (h5 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((3 - (3 * (t ^ (2 : ℕ)))) /. (2 - (2 * t))) = ((3 /. 2) * (t + 1))))))
  (h6 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((lpFunDeri y x) t) = ((3 /. 2) * (t + 1))))))
  : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((lpFunDeri (lpFunDeri y x) x) t) = ((iteratedDeriv 1 (fun t_1 => (lpFunDeri y x) t_1) t) /. (iteratedDeriv 1 (fun t_1 => x t_1) t))))) := by
  sorry

theorem proof_gap_exercise_1140_6
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (h1 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((x t) = ((2 * t) - (t ^ (2 : ℕ)))))))
  (h2 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((y t) = ((3 * t) - (t ^ (3 : ℕ)))))))
  (h3 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((lpFunDeri y x) t) = ((iteratedDeriv 1 (fun t_1 => y t_1) t) /. (iteratedDeriv 1 (fun t_1 => x t_1) t))))))
  (h4 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((iteratedDeriv 1 (fun t_1 => y t_1) t) /. (iteratedDeriv 1 (fun t_1 => x t_1) t)) = ((3 - (3 * (t ^ (2 : ℕ)))) /. (2 - (2 * t)))))))
  (h5 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((3 - (3 * (t ^ (2 : ℕ)))) /. (2 - (2 * t))) = ((3 /. 2) * (t + 1))))))
  (h6 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((lpFunDeri y x) t) = ((3 /. 2) * (t + 1))))))
  (h7 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((lpFunDeri (lpFunDeri y x) x) t) = ((iteratedDeriv 1 (fun t_1 => (lpFunDeri y x) t_1) t) /. (iteratedDeriv 1 (fun t_1 => x t_1) t))))))
  : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((iteratedDeriv 1 (fun t_1 => (lpFunDeri y x) t_1) t) /. (iteratedDeriv 1 (fun t_1 => x t_1) t)) = ((3 /. 2) /. (2 - (2 * t)))))) := by
  sorry

theorem proof_gap_exercise_1140_7
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (h1 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((x t) = ((2 * t) - (t ^ (2 : ℕ)))))))
  (h2 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((y t) = ((3 * t) - (t ^ (3 : ℕ)))))))
  (h3 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((lpFunDeri y x) t) = ((iteratedDeriv 1 (fun t_1 => y t_1) t) /. (iteratedDeriv 1 (fun t_1 => x t_1) t))))))
  (h4 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((iteratedDeriv 1 (fun t_1 => y t_1) t) /. (iteratedDeriv 1 (fun t_1 => x t_1) t)) = ((3 - (3 * (t ^ (2 : ℕ)))) /. (2 - (2 * t)))))))
  (h5 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((3 - (3 * (t ^ (2 : ℕ)))) /. (2 - (2 * t))) = ((3 /. 2) * (t + 1))))))
  (h6 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((lpFunDeri y x) t) = ((3 /. 2) * (t + 1))))))
  (h7 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((lpFunDeri (lpFunDeri y x) x) t) = ((iteratedDeriv 1 (fun t_1 => (lpFunDeri y x) t_1) t) /. (iteratedDeriv 1 (fun t_1 => x t_1) t))))))
  (h8 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((iteratedDeriv 1 (fun t_1 => (lpFunDeri y x) t_1) t) /. (iteratedDeriv 1 (fun t_1 => x t_1) t)) = ((3 /. 2) /. (2 - (2 * t)))))))
  : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((3 /. 2) /. (2 - (2 * t))) = (3 /. (4 * (1 - t)))))) := by
  sorry

theorem proof_gap_exercise_1140_8
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (h1 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((x t) = ((2 * t) - (t ^ (2 : ℕ)))))))
  (h2 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((y t) = ((3 * t) - (t ^ (3 : ℕ)))))))
  (h3 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((lpFunDeri y x) t) = ((iteratedDeriv 1 (fun t_1 => y t_1) t) /. (iteratedDeriv 1 (fun t_1 => x t_1) t))))))
  (h4 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((iteratedDeriv 1 (fun t_1 => y t_1) t) /. (iteratedDeriv 1 (fun t_1 => x t_1) t)) = ((3 - (3 * (t ^ (2 : ℕ)))) /. (2 - (2 * t)))))))
  (h5 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((3 - (3 * (t ^ (2 : ℕ)))) /. (2 - (2 * t))) = ((3 /. 2) * (t + 1))))))
  (h6 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((lpFunDeri y x) t) = ((3 /. 2) * (t + 1))))))
  (h7 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((lpFunDeri (lpFunDeri y x) x) t) = ((iteratedDeriv 1 (fun t_1 => (lpFunDeri y x) t_1) t) /. (iteratedDeriv 1 (fun t_1 => x t_1) t))))))
  (h8 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((iteratedDeriv 1 (fun t_1 => (lpFunDeri y x) t_1) t) /. (iteratedDeriv 1 (fun t_1 => x t_1) t)) = ((3 /. 2) /. (2 - (2 * t)))))))
  (h9 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((3 /. 2) /. (2 - (2 * t))) = (3 /. (4 * (1 - t)))))))
  : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((lpFunDeri (lpFunDeri y x) x) t) = (3 /. (4 * (1 - t)))))) := by
  sorry

theorem proof_gap_exercise_1140_9
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (h1 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((x t) = ((2 * t) - (t ^ (2 : ℕ)))))))
  (h2 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((y t) = ((3 * t) - (t ^ (3 : ℕ)))))))
  (h3 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((lpFunDeri y x) t) = ((iteratedDeriv 1 (fun t_1 => y t_1) t) /. (iteratedDeriv 1 (fun t_1 => x t_1) t))))))
  (h4 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((iteratedDeriv 1 (fun t_1 => y t_1) t) /. (iteratedDeriv 1 (fun t_1 => x t_1) t)) = ((3 - (3 * (t ^ (2 : ℕ)))) /. (2 - (2 * t)))))))
  (h5 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((3 - (3 * (t ^ (2 : ℕ)))) /. (2 - (2 * t))) = ((3 /. 2) * (t + 1))))))
  (h6 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((lpFunDeri y x) t) = ((3 /. 2) * (t + 1))))))
  (h7 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((lpFunDeri (lpFunDeri y x) x) t) = ((iteratedDeriv 1 (fun t_1 => (lpFunDeri y x) t_1) t) /. (iteratedDeriv 1 (fun t_1 => x t_1) t))))))
  (h8 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((iteratedDeriv 1 (fun t_1 => (lpFunDeri y x) t_1) t) /. (iteratedDeriv 1 (fun t_1 => x t_1) t)) = ((3 /. 2) /. (2 - (2 * t)))))))
  (h9 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((3 /. 2) /. (2 - (2 * t))) = (3 /. (4 * (1 - t)))))))
  (h10 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((lpFunDeri (lpFunDeri y x) x) t) = (3 /. (4 * (1 - t)))))))
  : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((((lpFunDeri (lpFunDeri (lpFunDeri y x) x) x) t) = ((iteratedDeriv 1 (fun t_1 => (lpFunDeri (lpFunDeri y x) x) t_1) t) /. (iteratedDeriv 1 (fun t_1 => x t_1) t))) ∧ (((iteratedDeriv 1 (fun t_1 => (lpFunDeri (lpFunDeri y x) x) t_1) t) /. (iteratedDeriv 1 (fun t_1 => x t_1) t)) = ((3 /. (4 * ((1 - t) ^ (2 : ℕ)))) /. (2 - (2 * t))))) ∧ (((3 /. (4 * ((1 - t) ^ (2 : ℕ)))) /. (2 - (2 * t))) = (3 /. (8 * ((1 - t) ^ (3 : ℕ)))))))) := by
  sorry
